## What changed

Replaced the hole in `WeilConjectures.normalizedDVRTower_effectivity` by a proof
combining finite comparison, all-pairs coherence and transport of the canonical
augmented reduction tower. Its signature and all three existing definitions are
unchanged. The identity and longer-transition cases are included. Elaborator instances are
explicitly named local instances; their registration is confined to each file.

The finite comparison now uses the adopted, proved generic theorem
`CochainComplex.IsNormalizedAdicTower.isIso_π_comp`, followed by a proved exact
faithful restriction argument. `NormalizedDVRRoosFiniteReduction` contains that
combination. `NormalizedDVRKFlatReductionModel` constructs the representative and
comparison isomorphisms from K-flat resolution and universal tensor counits, and
proves their unit and transition equations from the retained transition lemma.
The original module proves Roos projection identities, adjunction coherence and
product-triangle transport directly.

Also closed `integralReductionTowerMap_naturality` in the unclaimed
`Sheaf.Paper.IntegralReductionTower`: the pure-tensor formulas prove compatibility
for successors, and `NatTrans.ofOpSequence` gives all arrows. Every public
signature, definition and import in that module is unchanged. The change record is
`coord/changes/t6-integral-tower-naturality.md`. The explicitly named local elaboration
instances are recorded in `coord/changes/t6-normalized-dvr-local-instances.md`.
No source-library declaration was
removed, no existing definition was changed, and no other group's module was adapted.

## Proved and sorry left

Original item: one hole, `WeilConjectures.normalizedDVRTower_effectivity`; its proof
now has no `sorry`. The delivery adds two named holes, so this part is a
decomposition, not an axiom-free proof of DVR effectivity:

- `WeilConjectures.normalizedDVR_adic_cone_model`, node
  `lem-coef-normalized-dvr-adic-cone-model`: strict flat-term normalized adic model,
  compatible identifications at every positive level, bounded-free tensor/Roos
  comparison and equality of its actual augmented projection
  with the restricted adjoint comparison. Its conclusion does not assert that this
  projection is invertible; the existing generic adic theorem proves that step.
- `WeilConjectures.normalizedDVR_kflat_transition`, node
  `lem-coef-normalized-dvr-kflat-transition`: the universal K-flat comparisons carry
  the adjacent quotient map to the recorded pure-tensor chain transition. This is
  the finite-linear tensor/adjunction compatibility calculation, not effectivity.

The new named supporting theorems
`WeilConjectures.normalizedDVRRoos_finite_reduction` and
`WeilConjectures.normalizedDVR_kflat_reduction_model` have complete proofs from
these statements and the existing library. All private helpers are proved.
The existing dependency `WeilConjectures.integralReductionTowerMap_naturality`
is also closed, with no new hole for it. Packet accounting is two existing holes
closed and two holes added. Inherited holes in imported dependencies are unchanged.
There are no holes in definitions.

## No longer needed

The route does not need `lem-weil-pbc-sequential-tower-evaluation-full` or
`Sheaf.CategoryTheory.SequentialTowerEvaluationFull`: level isomorphisms and their
products suffice to transfer the actual Roos triangle. It does not need
`lem-weil-pbc-ringed-strict-tower-homotopy-limit` or the ringed strict-tower
homotopy-limit modules, including the independent-coefficient variant: the adopted
generic strict normalized adic cone theorem already proves the nilpotent-fibre
limit argument. These are route prunings, not claims that no other target uses them.

The following private imports were removed from the item module:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.CategoryTheory.SequentialTowerEvaluationFull`
- `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts`
- `Mathlib.Algebra.Homology.HomologicalComplexLimits`
- `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic`
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`
- `Mathlib.Algebra.Homology.DerivedCategory.Fractions`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Algebra.Homology.KFlat`
- `Mathlib.Algebra.Homology.BifunctorShift`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.DerivedCompleteOnSlices`
- `Sheaf.Paper.PbcRoosTriangle`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

The coefficient/DVR, K-flat, tensor, exact-product and derived-change-of-rings
mathematics among these remains in the strict cone-model dependency's stated
proof plan where needed. Removing their direct imports is not a claim that those
foundations are unnecessary. Derived-completeness-on-slices, a separate total
strict-tower derived-limit construction, and a derived evaluation fullness lift
are not used by this argument.

The old top-level `tool_uses` approvals on the item node were removed with the old
seven-step direct proof. These entries were the DVR lemma, constant completion
equivalence, derived homology long exact sequence, K-flat resolution, quasi-isomorphism
fractions, sequential evaluation fullness, Roos triangle, derived change of rings,
ringed strict-tower homotopy limit, and exact pro-etale countable products. The
foundational entries still used in the retained model argument are recorded as
that node's dependencies; no maintainer approval was added or reordered.

## Where the brief, the DAG or earlier work was wrong

The direct plan requested two stronger diagram constructions than necessary:
fullness of derived evaluation and exactness of a separately constructed total
strict-tower homotopy-limit functor. The supplied Roos triangle already lets us
work with products and compatible level maps. The adopted generic strict adic cone
theorem supplies the nilpotent-fibre calculation.

The old proof dependencies did not state the precise canonical unit/transition
comparison needed to connect the derived adjunction to the published chain-level
augmentation. This calculation is now explicit as the separate transition node.
The strict cone-model node isolates the remaining sheaf/Koszul construction and
requires identifications of every positive level, commuting with every successor;
it is a model of the entire given tower. The finite-linear lift calculation cannot
be obtained merely by cancelling the completed-coefficient tensor unit: that unit
need not be epic in the derived category. The ordinary integral tower API exports
completed-linear maps with pure-tensor formulas; its finite-linear sheaf-map
construction is private. The alternative published scalar-surjectivity interface
uses a coupled site/field universe and does not directly cover this statement's
independent universes. The retained transition lemma states the precise compatible
finite-linear tensor calculation, with its full proof in words.
All positive coefficient exponents are indexed by `n+1`; zero towers, the empty
scheme and the first coefficient level require no extra hypotheses. No disputed
statement or target signature change is proposed.

## New nodes

`lem-coef-normalized-dvr-adic-cone-model`: strict normalized adic model and
bounded-free cone computation, in `Sheaf.Paper.NormalizedDVRAdicConeModel`; one hole.

`lem-coef-strict-normalized-adic-cone-limit`: attaches the existing proved source
theorem `CochainComplex.IsNormalizedAdicTower.isIso_π_comp` in
`WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower`. No source file changes.

`lem-coef-normalized-dvr-roos-finite-reduction`: proves invertibility from the cone
model and the adopted source theorem, then reflects it through exact faithful
restriction, in `Sheaf.Paper.NormalizedDVRRoosFiniteReduction`; no hole.

`lem-coef-normalized-dvr-kflat-transition`: precise adjacent quotient compatibility
in `Sheaf.Paper.NormalizedDVRKFlatTransition`, together with the actual comparison
morphism definition; one hole.

`lem-coef-normalized-dvr-kflat-reduction-model`: K-flat representative and augmented
tower comparisons in `Sheaf.Paper.NormalizedDVRKFlatReductionModel`; no hole.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
