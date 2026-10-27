## What changed

Replaced the one `sorry` in
`AlgebraicGeometry.Etale.VectorTraceScalar.vectorTraceScalarDescent` with a complete combining
proof. The signature and all five conclusions are unchanged. The proof now derives the
projective decomposition square from its two columns using an additive functor's biproduct
comparison, and derives the trace square by cancelling the specified decompositions.
It then applies affine induction and the comparison on each framed open. The final global
step is proved: geometric trace invertibility identifies the source with a degree-zero object;
fullness of `DerivedCategory.singleFunctor`, compatibility of `etaleDegreeZeroHomEquiv_map`,
and joint faithfulness of inverse image along the Zariski cover detect equality of sheaf maps.
This does not use detection of arbitrary derived morphisms by open restrictions.

Added three strictly smaller scalar lemmas, each in its own module, with a complete proof in
words and a DAG node. `projective_components` concerns only the two projective columns;
`affine_of_projective` is the coordinate-tower implication assuming projective trace squares;
`frame_scalar_square` proves equality after one specified framed open, assuming affine squares.
The parent proves the biproduct, trace and global sheaf descent calculations itself.

Moved the eleven canonical helper definitions unchanged into `VectorTraceScalarData`, publicly
re-exported by the original module, so the three substeps do not import their parent. Bodies,
signatures and attributes are preserved; only docstring ownership identifiers change. Updated
the existing coefficient-data attachment and added the map-data node. No adopted source-library
file or target is edited. Change record:
`coord/changes/R1-vector-trace-scalar-data-relocation.md`.

The item compiled against the sandbox modules in 45.2 seconds. The data module and each new
lemma compiled individually within the 60-second limit. Final changed-file and direct-importer
checks are recorded below when complete.

## Proved and sorry left

This is a decomposition, not a sorry-free proof or a positive net hole reduction.
One old hole is closed syntactically:
`AlgebraicGeometry.Etale.VectorTraceScalar.vectorTraceScalarDescent`
(`lem-pur-vector-trace-scalar-descent`). Its module contains zero `sorry`.
Three holes are added, all public named theorems whose bodies are exactly `:= by sorry`:

- `AlgebraicGeometry.Etale.VectorTraceScalar.projective_components`, in
  `Sheaf.Paper.VectorTraceScalarProjectiveComponents`, node
  `lem-pur-vector-scalar-projective-components`.
- `AlgebraicGeometry.Etale.VectorTraceScalar.affine_of_projective`, in
  `Sheaf.Paper.VectorTraceScalarAffineInduction`, node
  `lem-pur-vector-scalar-affine-induction`.
- `AlgebraicGeometry.Etale.VectorTraceScalar.frame_scalar_square`, in
  `Sheaf.Paper.VectorTraceScalarFrameComparison`, node
  `lem-pur-vector-scalar-frame-comparison`.

The data module has zero holes. The private lemmas `splitting_square`, `trace_square`,
`derived_eq_of_cover`, `projective_splitting_square` and `projective_trace_square` are fully proved.
Net local hole change is +2; no claim of closing a target with only the permitted axioms is made.
No hole is left inside a definition or inside the main proof.

## No longer needed

No module is withdrawn or asserted globally unnecessary. The unit's projective-line, affine
composition and bundle-frame route is preserved. Lower geometric dependencies are assigned to
the appropriate new statements rather than imported solely to accompany the old parent `sorry`.
The eight old public imports move to the data module and remain transitively public.

Removed direct proof-only imports from the parent module:

- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`.
- `Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension`.
- `Sheaf.CategoryTheory.DerivedCategory.AdjunctionMateTranspose`.
- `Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints`.
- `Sheaf.AlgebraicGeometry.EtaleDirectImageScalarExchange`.
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`.
- `Sheaf.Paper.OpenScalarSiteCoherence`.
- `Sheaf.Paper.EtaleOpenScalarExchange`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`.
- `Sheaf.Paper.P1KummerDerivedScalar`.
- `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`.
- `Sheaf.AlgebraicGeometry.IsIsoIffOfJointlySurjectiveEtaleFamily`.
- `Mathlib.AlgebraicGeometry.Noetherian`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.

The old parent's proof dependencies concerning Kummer normalization, Tate pullback, proper/open
mate exchange, monoidal comparisons and affine induction now occur in the split nodes; they
remain needed there. `lem-pur-sheaf-hom-cover-gluing` is not used by the new parent proof:
joint faithfulness follows instead from the already proved sheaf cover reflection-of-isomorphisms
result and the general abelian-category implication. It is not withdrawn, since other users may
need it. The separate `DerivedTensorAdditiveConstraints` lemma is unnecessary for the parent's
biproduct calculation: additivity follows directly from the scalar adjunction. Its module is
not withdrawn. No top-level maintainer `tool_uses` approval is edited.

## Where the brief, the DAG or earlier work was wrong

The original statement was not disputed. Its proof plan is valid but several geometric
normalization/mate calculations are not one-line applications of the available declarations.
They are now explicit strict substeps rather than an unchanged parent `sorry`. The generic
categorical and sheaf-descent parts have real Lean proofs. The existing proved
`vectorBundleIntegration_concentration_and_isIso` supplies the invertible source identification,
so the original geometric concentration argument need not be reproduced here.

Searches found no Mathlib theorem for these normalized small-etale trace squares.
Mathlib's biproduct API does supply the shorter categorical calculation. The similarly named
`FiniteVectorIntegrationScalar` already uses the assigned theorem and would be circular;
restricted arithmetic/projective scalar lemmas do not have the arbitrary finite-ring and
Noetherian-base hypotheses needed here. Rank zero, zero rings/N=1, empty opens and empty bases
were checked in the mathematical statements: the traces reduce to the prescribed identity or
unique zero maps. No flatness of the coefficient map is introduced.

The live server queue classified this as a proof item, not a zero-hole repair. Its prior build
record referred to a missing buildtree source; the current item source is present and compiles.
The latest blueprint paragraph 2 and the unit route were read; no unit or chapter record changes.

A full reachable-DAG audit encountered a pre-existing cycle through `thm-sp-grothendieck`,
Cartan--Eilenberg truncation and edge-map nodes. Those records are untouched. A separate audit
of all 60 new dependency edges confirms that none introduces a cycle.

## New nodes

`lem-pur-vector-scalar-projective-components`: the two proper projective components, obtained
from normalized Tate pullback and Kummer compatibility by adjunction. It has no affine or bundle
claim. Its proof records the original scalar-descent Steps 1--3.

`lem-pur-vector-scalar-affine-induction`: the ordered affine trace implication from all projective
trace equations. Its proof records open counit compatibility, tensoring with ordered Tate inputs,
coordinate induction and refinement, corresponding to original Steps 5--8.

`lem-pur-vector-scalar-frame-comparison`: the local framed restriction equality assuming affine
squares. It records original Step 9 and Tate pullback normalization; it makes no global equality
detection assertion. The parent supplies that detection in proved Lean.

`def-pur-vector-trace-scalar-map-data`: records the seven unchanged canonical map constructions
`pullBase`, `projective`, `sum`, `affineCoefficient`, `affineTrace`, `affine`, `vector`, moved into
the public data module. The four unchanged coefficient constructions retain their existing node.
All new nodes include three kinds of Mathlib searches and the exact Lean declaration signatures.

Change record: `coord/changes/R1-vector-trace-scalar-data-relocation.md`.

## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 4 OK.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"Sheaf.Paper.VectorTraceScalarAffineInduction": "b0b355099f1bffd9c52ea12799b0d56eccdb0247", "Sheaf.Paper.VectorTraceScalarData": "077d4cae1382032d998817a2d2b762c82c15ad6d", "Sheaf.Paper.VectorTraceScalarDescent": "056d191f1b4a9748c9c12b57d2afcc6c081477ce", "Sheaf.Paper.VectorTraceScalarFrameComparison": "6d9edd05e6c04a2d8b82edf0bf4e091809ce989e", "Sheaf.Paper.VectorTraceScalarProjectiveComponents": "d8de4e37bfba81b1e952aae8f63eb6f44e3f8952"}, "results": {"Sheaf.Paper.FiniteCoefficientTensorFactorization": {"hash": "969c072b72584dec0f6ee14d6371220d4ff14171", "status": "OK"}, "Sheaf.Paper.FinitePurityCounitSystem": {"hash": "0b0bc7ef25aed819debf022434a329c99d0f7df4", "status": "OK"}, "Sheaf.Paper.FiniteScalarUnitNormalization": {"hash": "75a318c2a191e7e4c18da7746465d5e04dbcf051", "status": "OK"}, "Sheaf.Paper.P1CounitScalar": {"hash": "d2514dc6297139687fbd7f14760051b4c34f2802", "status": "OK"}}, "seconds": 511, "time": "2026-10-28T03:40:44+0800", "transitive": 0, "version": 1}
```

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
