#!/usr/bin/env python3
"""Check frozen source integrity; optionally validate saved Lean axiom output.

This is a text/integrity check. Lean's kernel, invoked separately, checks proofs.
"""
from pathlib import Path
import argparse, collections, hashlib, json, re, sys

def fail(message):
    raise SystemExit('FAIL: '+message)

def lean_code(text):
    # Remove nested block comments, line comments and strings before token scan.
    out=[]; i=0; depth=0
    while i < len(text):
        if depth:
            if text.startswith('/-',i): depth+=1; i+=2
            elif text.startswith('-/',i): depth-=1; i+=2
            else: i+=1
        elif text.startswith('/-',i): depth=1; i+=2
        elif text.startswith('--',i):
            j=text.find('\n',i); i=len(text) if j<0 else j
        elif text[i]=='"':
            i+=1
            while i<len(text):
                if text[i]=='\\': i+=2
                elif text[i]=='"': i+=1; break
                else: i+=1
            out.append(' ')
        else: out.append(text[i]); i+=1
    return ''.join(out)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit-log',type=Path)
    args=parser.parse_args()
    root=Path(__file__).resolve().parents[1]
    manifest={}
    for line in (root/'REPRODUCIBLE_SOURCES_SHA256.txt').read_text(encoding='utf-8-sig').splitlines():
        m=re.fullmatch(r'([0-9a-f]{64})  (.+)',line)
        if not m: fail('malformed source-manifest entry')
        digest,rel=m.groups()
        if rel in manifest or Path(rel).is_absolute() or '..' in Path(rel).parts:
            fail('invalid/duplicate source path '+rel)
        manifest[rel]=digest
    if len(manifest)!=59: fail('expected 59 source/configuration entries')
    for rel,digest in manifest.items():
        path=root/rel
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest()!=digest:
            fail('source mismatch: '+rel)
    sources={str(p.relative_to(root)).replace('\\','/') for p in (root/'AffineQuadric').rglob('*.lean')}
    sources.add('AffineQuadric.lean')
    if sources!={r for r in manifest if r.endswith('.lean')} or len(sources)!=56:
        fail('Lean file set does not match the frozen 56-file set')
    banned=re.compile(r"(?<![\w'])\b(sorry|admit|sorryAx|native_decide|axiom|unsafe)\b(?![\w'])")
    for rel in sorted(sources):
        if banned.search(lean_code((root/rel).read_text(encoding='utf-8-sig'))):
            fail('prohibited source token in '+rel)
    if (root/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.24.0':
        fail('wrong Lean toolchain')
    packages=json.loads((root/'lake-manifest.json').read_text())['packages']
    mathlib=[p for p in packages if p['name']=='mathlib']
    if len(packages)!=9 or len(mathlib)!=1 or mathlib[0]['rev']!='f897ebcf72cd16f89ab4577d0c826cd14afaafc7':
        fail('wrong pinned package set')
    expected_lines=(root/'tools/expected-declarations.txt').read_text(encoding='utf-8-sig').splitlines()
    expected=[s.strip() for s in expected_lines if s.strip()]
    if len(expected)!=614 or len(set(expected))!=614: fail('expected inventory is not 614 distinct names')
    audit=(root/'AffineQuadric/Audit.lean').read_text(encoding='utf-8-sig')
    requested=re.findall(r'^#print axioms\s+(\S+)\s*$',audit,re.M)
    if collections.Counter(requested)!=collections.Counter(expected):
        fail('Audit.lean and independently accepted inventory differ')
    print('PASS: 59 frozen sources/configurations; 56 Lean files; 9 pinned packages; 614 audit names.')
    print('PASS: prohibited-token source scan. This is not a new Lean compilation.')
    if args.audit_log:
        text=args.audit_log.read_text(encoding='utf-8-sig')
        pattern=re.compile(r"'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",re.S)
        matches=list(pattern.finditer(text))
        if collections.Counter(m.group(1) for m in matches)!=collections.Counter(expected):
            fail('audit output does not cover exactly 614 accepted names once each')
        allowed={'propext','Classical.choice','Quot.sound'}
        for m in matches:
            axioms={a.strip() for a in (m.group(2) or '').split(',') if a.strip()}
            if not axioms<=allowed: fail('unexpected axiom in '+m.group(1))
        remaining=pattern.sub('',text)
        if remaining.strip(): fail('unrecognized audit output; inspect warnings or errors')
        print('PASS: saved audit output covers 614/614 names, only permitted axioms.')

if __name__=='__main__':
    main()
