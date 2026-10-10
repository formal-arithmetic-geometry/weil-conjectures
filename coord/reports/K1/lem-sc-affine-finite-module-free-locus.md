Files written:

- `dag/nodes/sec-picard-framework/lem-sc-affine-finite-module-free-locus.json`: item, statement, four proof steps, and split report.
- `dag/nodes/sec-picard-framework/lem-sc-noetherian-finite-module-finite-presentation.json`: Mathlib leaf; exact match `Module.finitePresentation_of_finite`.
- `dag/nodes/sec-picard-framework/lem-sc-finitely-presented-free-at-prime-principal.json`: unsplit Stacks statement; no exact Mathlib match.

Attachments: none.

WANTED: none.

The item was unsplit and has no exact sorry-free declaration in either source checkout. I searched the DAG and blueprint for the item, Tag 0GWM, finite presentation over Noetherian rings, and free-locus terminology. The pointwise 0GWM assertion was absent, so I created one statement-only node; the Noetherian finite-module assertion is a Mathlib leaf. The item keeps its original statement and adds the missing proof and dependencies. Small cases checked were $M=A^r$ (one principal open), $M=0$, and the non-free ideal $(x,y)$ over $k[x,y]$, where the hypothesis fails at $(x,y)$.

## Review by K1

I read the item source reference, Stacks Algebra Tag 0GWM, and the cited affine module-sheaf and spectrum statements. Step 1 uses the new Mathlib leaf, whose statement exactly supplies finite presentation from the Noetherian and finite hypotheses. Step 2 uses the new 0GWM node, whose statement exactly supplies an element outside each prime and a finite-free localization, together with the existing free-module definition. Step 3 uses the existing spectrum node: its statement explicitly says principal opens cover iff their elements generate the unit ideal and that Spec is quasi-compact. Step 4 uses the existing tilde-sections node, whose statement explicitly identifies sections on $D(f)$ with $M_f$, yielding the stated finite locally free sheaf. I verified all statement dependencies exist and are used, recorded all citations verbatim in `citations.json`, and checked the new node IDs are absent from the repository DAG. No source or hypothesis correction was needed.

What could not be finished: no Lean was written or compiled, as required for stage 1.
