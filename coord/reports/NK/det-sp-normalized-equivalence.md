## Worker report

The module `Sheaf.Paper.SmoothPurityNormalizedEquivalence` states
`AlgebraicGeometry.ProEtale.sp_normalized_equivalence`. Its sole theorem proof is
`sorry`; the helper definitions have complete data. `SpNormalizedEquivalence`
bundles the ambient adjunction, the complete-object unit and normalized-tower
counit isomorphisms, and the constructible equivalence. No node statement,
dependency record, or dependency list is changed.

Source read: main-20261015,
`sec-smooth-purity/sk-lem-sp-tower/sk-lem-sp-tower-equivalence.md`, together with
the item's ten-step reviewed proof and its statement dependencies. The repair
note is resolved stage 1: its long-step defect was already addressed in the
current ten-step proof. No stage-2 repair remains in that note.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Prime ell | `(l : ℕ) [Fact l.Prime]` |
| Finite extension E/Q_ell, with its valuation ring | `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`; the recorded coefficient constructions use `Padic.coefficientExtensionIntegers l E` |
| Scheme T with ell invertible | `(T : Scheme.{u})` and `[∀ x : T, Invertible (l : T.residueField x)]` |
| Small pro-etale site and completed coefficient sheaf R_T | Existing `Scheme.ProEt.topology T` and `completedIntegralCommRingSheafUnrestricted l E T`, underlying `scalarReductionSource l E T`; `sp_completed_coefficient_limit` identifies this with the ell-power limit, respecting the quotient projections |
| Ordinary unbounded D(Mod(R_T)) | `DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T)` |
| Ordinary derived coefficient-tower category | `spDerivedCoefficientTowers l E T D`, with the recorded strict varying-coefficient category and localization from `D : SpCoefficientTowersAbelian l E T` |
| Reduction M to its derived ell-power reductions, with actual transitions | `spCompletedReduction l E T D R`, transporting `R.red` along its coefficient-ring isomorphism by exact restriction of scalars; `R : SpReductionTower l E T D` already specifies ordinary tensor generators, quotient transitions, the universal derived functor and K-flat computation |
| Forget finite scalars before total derived limit | `spCompletedStrictTower` is `Functor.ofOpSequence` of the existing completed evaluations and their actual transitions, flipped into a functor on towers; `spCompletedTotalLimit` applies its exact derived functor and then the existing `coefficientConstantTowerLimit` |
| Exact total-derived-limit functor | `limitShift`, `limit_triangulated`; the latter limit is already defined by the total right-derived inverse limit computed on simultaneous K-injectives |
| Roos-triangle meaning of Rlim | `products` and `roos`, using `IsDerivedLimitTriangle` for the existing `spDerivedCompletedTransition`; the first map is the product of `spCompletedTotalProjection`, obtained from the existing K-injective-normalized limit projections through canonical exact-functor localization comparisons |
| r_T left adjoint to L_T | `SpNormalizedEquivalence.adjunction : spCompletedReduction ... ⊣ spCompletedTotalLimit ...` |
| Unit isomorphism on derived-complete objects | `unit_isIso`, with the dependency's global `IntegralOnSlice.IsComplete l E T none M`; no boundedness, constructibility, Noetherianity or Tor bound is imposed here |
| Counit isomorphism on normalized towers | `counit_isIso`, assuming only `IsSpNormalizedTower l E T D C`, without constructibility, Tor bounds or boundedness |
| Additional Noetherian hypothesis only for restriction | `restriction : IsNoetherian T → ...`; Mathlib's `isNoetherian_iff_of_finite_affine_openCover` identifies this with the stated finite affine cover by Noetherian spectra |
| Derived-complete integral constructible category | The dependency's existing `WeilConjectures.sfIntegralConstructibleCategory l E T`: derived completeness, every uniformizer reduction bounded constructible, and one common cohomological interval |
| Normalized constructible towers with uniform cohomological and Tor bounds | The dependency's existing `spNormalizedConstructibleTorTowerCategory l E T D`; `spConstructibleTorTowers` retains both independent uniform intervals and `IsSpNormalizedTower` tests all m <= n |
| Mutually inverse equivalences given by reduction and total limit | `restriction` supplies `e : sfIntegralConstructibleCategory ... ≌ spNormalizedConstructibleTorTowerCategory ...`; both functors, composed with the full-subcategory inclusions, equal the ambient reduction and total-limit restrictions. Thus all ambient morphisms are retained. The ambient unit/counit remain natural and satisfy their triangle identities on these full subcategories |

The parameters D and R are the recorded coefficient and reduction constructions,
whose existence is already stated by `sp_coefficient_towers_abelian` and
`sp_reduction_tower_normalized`. They are not new hypotheses on T or on its
objects. Likewise forgetting exactness is an asserted part of the output
structure, not a theorem hypothesis. These helpers implement the very functors
named in this node; no independent mathematical notion or definition node is
introduced. The completed coefficient ring is transported along the existing
specified ring isomorphism, not replaced by an arbitrary coefficient map.

Dependency declarations read and used (the module imports each recorded
statement dependency and every already stated proof dependency):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the imported coefficient-extension
  valuation ring and finite quotient constructions.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`;
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `WeilConjectures.integralConstantToCompletionOfUniverses` and the imported
  `completedIntegralCommRingSheafUnrestricted`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `Functor.mapDerivedCategoryCompIso`.
- `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spCoefficientTowers`,
  `spCoefficientRings`, `sp_completed_coefficient_limit`.
- `Sheaf.Paper.SmoothPurityNormalizedTowers`: `spDerivedCoefficientTowers`,
  `spNormalizedConstructibleTorTowers`, `spNormalizedConstructibleTorTowerCategory`,
  `IsSpNormalizedTower`.
- `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructible`,
  whose Tor condition is retained in the recorded tower category.
- `Sheaf.Paper.SfIntegralConstructible`:
  `WeilConjectures.sfIntegralConstructible`, `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.DerivedCompleteOnSlices`:
  `WeilConjectures.IntegralOnSlice.IsComplete`; the global branch is the original
  augmented quotient-tower Roos condition, without a chosen completion map.
- `Sheaf.Paper.SmoothPurityReductionTowerNormalized`: `SpReductionTower`,
  `sp_reduction_tower_normalized`; the new reduction is its canonical transport.
- `Sheaf.Paper.SmoothPurityTowerReconstruction`: `spCompletedEvaluation`,
  `spCompletedTransition`, `spCompletedEllRestriction`,
  `spDerivedCompletedEvaluation`, `spDerivedCompletedTransition`,
  `spTower_reconstruction`.
- `Sheaf.Paper.CoefficientRingedSequenceSite`:
  `WeilConjectures.coefficientConstantTowerLimit`,
  `coefficientConstantTowerEvaluation`, `coefficientConstantTowerProjection`;
  these are existing total-derived constructions with K-injective normalization,
  not a new choice of a triangulated limit.
- `Sheaf.Paper.CompletedDerivedInverseLimit`: `Scheme.CompletedDerivedInverseLimit`
  supplies the recorded Roos-triangle interpretation. Its adic-datum tower
  presentation is not substituted for the item's strict ell-power tower; the
  common `IsDerivedLimitTriangle` is applied to the latter's actual evaluations.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`,
  fixing the exact total-derived-limit/Roos interpretation used here.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`;
  `Mathlib.AlgebraicGeometry.Noetherian`: `IsNoetherian` and its finite affine
  open-cover characterization.
- Proof-plan imports also retain the DVR, system-extension, uniformizer derived
  adjunction, initial-functor limit, K-flat change-of-rings, effectivity,
  triangle-isomorphism, intrinsic constructibility and residue-Tor declarations
  named in the node's ten proof steps. The theorem docstring records every step.

Edge cases checked against the signatures and definitions: positive level one is
index zero; equal-level normalization is included; ramified extensions are not
identified with the unramified case (ell-powers stay distinct from uniformizer
powers, related by cofinality in the proof); zero objects and the empty scheme
are allowed; no nonempty-site or nonzero-object hypothesis is added; the unit
and counit clauses allow unbounded objects; finite-level cohomological and Tor
intervals are uniform and need not coincide. No quasi-compactness or separatedness
hypothesis was added to the ambient theorem. The shared universe convention is
that of the recorded normalized-tower and integral categories; the pro-etale
site has object universe u+1 and morphism universe u, with module coefficients
in u+1. No equation of these site universes is imposed.

Searches for an existing declaration:

- `msearch.py ... leanfinder`, query "derived complete integral constructible
  complexes equivalent to normalized constructible coefficient towers": eight
  hits about constructible spectrum sets and scheme normalization, no match.
- `msearch.py ... leansearch`, query "derived reduction normalized towers derived
  complete equivalence": eight hits about ordinary adic completion and p-adic
  fields, no derived sheaf-tower equivalence.
- `msearch.py ... loogle`, query
  `CategoryTheory.Adjunction, CategoryTheory.Equivalence`: six hits, including
  `Equivalence.toAdjunction` and `Adjunction.toEquivalence`; these are general
  categorical constructions and do not state this coefficient-tower theorem.
- `msearch.py ... grep`, query
  `normalized.*[Ee]quivalence|[Ee]quivalence.*[Tt]ower|[Aa]dic.*[Aa]djunction`
  in `CategoryTheory`: twenty abstract monadic-adjunction hits, no match.
- `rg -n` for normalized equivalences, tower equivalences, the proposed name and
  the blueprint id in upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no match for this theorem. The integral-lisse
  equivalence is only a heart-level lisse statement and does not match it.
- `grep -rn "det-sp-normalized-equivalence"` in upstream `WeilConjectures`:
  no hits. Direct source searches found the reusable fixed-ring total limit and
  its canonical projections in `CoefficientRingedSequenceSite`; these are used.

Author re-reading with the node and final file open: each displayed category is
the recorded category, reduction uses the actual strict-tower construction,
scalar forgetting precedes the existing total derived limit, and both unbounded
isomorphism clauses are separated from the conditional Noetherian restriction.
The initial prototype omitted the explicit Roos presentation; the final file
adds canonical projections and `roos`, using the existing resolution-normalized
projections instead of selecting maps from triangles. No statement fault or
STATEMENT-DISPUTED flag remains.

Validation: file-only compilation through `scompile.py`, with automatic implicits
explicitly disabled, under the unchanged 60-second limit. No theorem was proved,
and no global build was run. Final preflight and delivery results are recorded
below after running the prescribed wrapper.

Final validation: `deliver2.py NK det-sp-normalized-equivalence --no-push`
printed `OK (dry run)`: the one-module packet passes server preflight and
file-only compilation. The final source has no extra warnings, no overlong Lean
lines, exactly one `sorry`, and its recorded signature matches the file verbatim.
The source node differs only in `lean`. Independent review is by the maintainer,
as prescribed by the dispatcher brief.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
