Files written:

- `dag/nodes/sec-picard-framework/lem-pc-finite-flat-pushforward-locally-free.json` — statement split into four proof steps.
- `dag/nodes/sec-picard-framework/lem-pc-finite-flat-affine-sections-projective.json` — statement-only algebraic helper, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-finite-flat-restriction-projective.json` — statement-only scalar-restriction helper, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-affine-sections-finite-locally-free-criterion.json` — attached sorry-free source declaration.
- `citations.json` — verbatim statement quotations for every proof citation.

Attachments:

- `AlgebraicGeometry.Scheme.Modules.finitePresentation_projective_sections` belongs to `lem-pc-finite-flat-affine-sections-projective`.
- `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_isAffineOpen` belongs to `lem-pc-affine-sections-finite-locally-free-criterion`.

WANTED:

- None.

What was wrong in the imported material:

- The item had an empty proof even though its source theorem gives the affine-open argument. The source declaration is not a closed attachment because the audit records a transitive dependency on `isQuasicoherent_higherDirectImage`.
- The split makes the scalar restriction step explicit; it is the content of the source lines using `Module.FinitePresentation.of_finite_of_finitePresentation` and `Module.Projective.trans`, rather than an unstated “finite over finite” inference.

What could not be finished:

- The scalar-restriction helper is intentionally statement-only for the next stage. It has no exact Mathlib declaration after LeanFinder, Loogle, grep, and unavailable LeanSearch checks.

## Review by M1

I read the source theorem and docstring in `WeilConjectures/AlgebraicGeometry/Modules/FinitePushforward.lean`, lines 208-242, and the two source declarations in `LocallyFreeAffine.lean`, lines 67-73 and 224-227. Step 1 uses the finite-morphism definition, which explicitly includes affineness, so affine inverse images are available. Step 2 uses the finite-locally-free definition's quasi-coherence clause and the existing affine pushforward statement; I checked that its hypotheses are an affine morphism and a quasi-coherent module, both supplied here. Step 3 uses the attached affine-sections declaration exactly for the $B$-module of sections, then the new scalar-restriction statement for the finite, finitely presented, flat ring map induced by $g$; the finite, flat, and locally finitely presented hypotheses are precisely the item's hypotheses on every affine open. Step 4 uses the attached affine criterion exactly, with Step 2 supplying quasi-coherence and Step 3 supplying finitely presented projective sections.

I opened every cited node and copied the quoted sentences into `citations.json`; each quote is a verbatim part of that node's statement. I searched the whole DAG and blueprint for duplicate affine-section, scalar-restriction, and affine-criterion statements before creating nodes. Mathlib searches were run for all three new nodes using LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was recorded as unavailable. Small cases checked were the identity morphism, a finite free algebra of rank one, the zero module/rank zero case, and a disconnected affine base with different finite ranks. The only correction made during review was to split the final affine criterion into its own attached helper instead of marking that non-elementary theorem as an elementary step.

## Second reading by M1

- Item statement: checked against `FinitePushforward.lean`, theorem `isFiniteLocallyFree_pushforward`, lines 214-244; hypotheses and conclusion agree.
- Step 1: checked against the finite morphism definition and affine preimage clause; the reduction is elementary.
- Step 2: checked against the affine pushforward quasi-coherence node; its affine and quasi-coherent hypotheses are supplied.
- Step 3: checked against the source's `finitePresentation_projective_sections`, `finite_app`, finite-presentation, and flatness facts; all cited statements now cover the ring-map hypotheses and projectivity-to-flatness conversion.
- Step 4: checked against `isFiniteLocallyFree_of_isAffineOpen`, lines 224-227; the criterion now correctly uses finitely presented flat sections.
- New node `lem-pc-finite-flat-affine-sections-projective`: checked against `finitePresentation_projective_sections`, lines 67-73; attached declaration and statement agree.
- New node `lem-pc-finite-flat-restriction-projective`: checked against the scalar-restriction argument in `FinitePushforward.lean`, lines 228-242; statement is smaller than the item and has all definition dependencies.
- New node `lem-pc-affine-sections-finite-locally-free-criterion`: checked against `isFiniteLocallyFree_of_isAffineOpen`, lines 224-227; statement corrected from projective sections to flat sections to match the declaration.
- Changed the affine criterion statement and Step 4 to match the source declaration, added missing scalar-ring definition dependencies and verbatim citations, and documented projective-implies-flat in Step 3.
