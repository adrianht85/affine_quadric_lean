# Development method and limits

The development used an AI-assisted workflow. A local Codex executor edited Lean files, ran the pinned compiler and saved build and axiom-audit output. A separate conversational review compared selected statements, hypotheses, source hashes and logs with the manuscript, and directed bounded follow-up tasks. The author supervised objectives and accepted scope decisions. This process does not constitute independent human mathematical review.

Lean's kernel checks the delivered proof terms under their stated mathematical hypotheses. This does not by itself certify that every informal statement has been translated faithfully, prove inputs that remain hypotheses, or establish the paper's external geometric identifications. FORMALIZATION_SCOPE.md records those distinctions.

Preservation, name coverage and reproducibility were treated separately from mathematical progress. An earlier declaration scanner omitted three structure fields with Unicode numeric subscripts even though the theorems had already been audited. The inventory was corrected and checked against independent explicit names. The accepted inventory now has 614 names. Public packaging uses that fixed inventory rather than regenerating both expected and observed names with one parser.

The mathematical corpus is frozen. Software 0.1.0 and the companion preprint were published on 5 November 2026. Publication preparation concerned documentation, reproducibility and release metadata. Subsequent documentation corrections do not create a new software version. Analytic ODE regularity, ambient tensor reconstruction and other declared boundaries are not silently claimed as complete.
