1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-finite-flat-restriction-projective.json` — item, Mathlib leaf.

2. Attachments: none.

3. WANTED: none.

4. The item is not stated by a project declaration carrying the blueprint tag. I checked the source theorem `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pushforward` in `WeilConjectures/AlgebraicGeometry/Modules/FinitePushforward.lean`, lines 214–244. Its affine argument uses finite-presentation transitivity and flatness transitivity; the requested projectivity conclusion follows by the Mathlib theorem that finitely presented flat modules are projective. The existing node `lem-pc-finite-flat-affine-sections-projective` concerns sections of a finite locally free sheaf and is not a duplicate.

## Review by E1

I checked the item statement against the affine scalar-restriction argument in `FinitePushforward.lean`: A→B is finite and finitely presented, B is flat over A, and M is finitely presented and projective over B. The finite-presentation clause is exactly the composition supplied by `Module.FinitePresentation.of_finite_of_finitePresentation` and `Module.FinitePresentation.trans`. For the projectivity clause, `Module.Flat.of_projective` turns the given B-projectivity of M into B-flatness, `Module.Flat.trans` gives A-flatness using the A-flatness of B, and `Module.Flat.projective_of_finitePresentation` applies after the first clause.

I read the Mathlib declarations at `RingTheory/Finiteness/ModuleFinitePresentation.lean:80`, `RingTheory/Flat/Basic.lean:231`, `RingTheory/Flat/Stability.lean:62`, and `RingTheory/Flat/EquationalCriterion.lean:287`, and recorded searches run through `msearch.py`, including the unavailable LeanSearch calls. I checked small cases conceptually: A=B reduces to the ordinary fact that finitely presented projective modules are projective, and M=B reduces to finite flat finitely presented B being projective over A. No new node was created because every ingredient is a Mathlib declaration.

## Second reading by E1

- Item statement: checked against `FinitePushforward.lean`, theorem `isFiniteLocallyFree_pushforward`, lines 228–242; finite, finite-presentation, flatness, and projectivity hypotheses and conclusions agree.
- Finite-module notion: checked against `def-weil-finitely-generated-module`; the finite $A$-module phrase is explicitly cited.
- Finite-presentation transitivity: checked against `Module.FinitePresentation.of_finite_of_finitePresentation` and `.trans`; the source lines provide the first conclusion.
- Flatness transitivity: checked against `Module.Flat.of_projective` and `Module.Flat.trans`; these provide the flatness input for the second conclusion.
- Projectivity criterion: checked against `Module.Flat.projective_of_finitePresentation`; it gives projectivity from the preceding properties.
- New nodes: none; existing definitions and Mathlib declarations suffice, with no duplicate node created.
- Edge cases: $A=B$, $M=B$, the zero module, and a field base satisfy the implication.

Changes made: corrected `created.item` to the delivered item; added the missing finite-module dependency; corrected the source description so the `.trans` calls are identified as finite-presentation and flatness transitivity; recorded this audit.
