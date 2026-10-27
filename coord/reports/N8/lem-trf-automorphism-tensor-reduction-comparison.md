## Worker report

Item: lem-trf-automorphism-tensor-reduction-comparison. Module:
`Sheaf.TraceFormula.AutomorphismTensorReductionComparison`, main declaration
`WeilConjectures.automorphismTensorReductionComparison`.

The module states the comparison on **ordinary unbounded complexes of the existing
strict quotient-linear module systems**. All theorem proofs are `sorry`.
Definitions have actual data: site postcomposition, the existing canonical finite
coefficient maps assembled into a system map, continuous module pushforward,
the existing sheafified change-of-rings objects and maps, and their local generators.
No tensor, system category, coefficient ring, or derived category is redefined.

The sequence-site presentation is the existing `coefficientSequenceModules`:
sections at `(n,U)` are sections of the nth module and horizontal restrictions
are its actual quotient-linear transitions. Covers are vertical, so sheafification
on this site is componentwise sheafification. `trfAutomorphismTensorEvaluation`
explicitly identifies the tensor system's nth evaluation with the actual finite
sheafified tensor and fixes that identification on every local pure tensor.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Prime ell | `(l : ℕ) [Fact l.Prime]` in the module's explicit variable declaration. |
| Finite extension E/Q_ell | `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. |
| Valuation ring, chosen uniformizer, positive quotient levels | Existing `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, and `coefficientExtensionRing`; the inherited coefficient sheaves index exponent `n+1` by `n : ℕ`, including exponent one. |
| Scheme with ell invertible | `{S : Scheme.{t}}` and `_hS : ∀ x : S, IsUnit (l : S.presheaf.stalk x)`. |
| Automorphism g | `(g : S ⟶ S) [IsIso g]`. |
| Small pro-etale site | `S.ProEt`, `ProEt.topology S`, and the recorded `proEtaleIsoPostcompose g`; object universe `t+1`, Hom universe `t`. |
| B_n, rho_n, completed ring, pi_n | `integralCoefficientSheaf`, `integralCoefficientSheafTransition`, `completedIntegralCoefficientSheafUnrestricted`, and `limit.π (integralCoefficientSheafSystem ...) (op n)`. |
| Canonical F and c_n | `isoSectionwiseInverseImage`; `inverseImageFiniteCoefficientMap`; system components are exactly these maps, with commutativity retained. |
| Canonical completed comparison | Existing `inverseImageCompletedCoefficientMap`, whose actual projection square is in the main statement. |
| Transport action by c_n inverse | `trfAutomorphismSystemInverse` is continuous module pushforward with coefficient map the image of `inv (trfAutomorphismCoefficientMap ...)` under `sheafCompose`. |
| Strict systems with arbitrary quotient-linear transitions | Existing `coefficientSequenceModules l E S`, not a cartesian subcategory, not a derived diagram category. |
| Ordinary unbounded complexes | `CochainComplex (coefficientSequenceModules l E S) ℤ`; both functors are applied by `mapHomologicalComplex (.up ℤ)`. |
| T_n M_n = FM_n tensor over FB_n with B_n | `trfAutomorphismRawModules ⋙ trfAutomorphismTensorExtension`, using `changeOfRingsOfUniverses` and `changeOfRingsHomOfUniverses`; `trfAutomorphismTensorEvaluation` identifies the nth level with `trfAutomorphismFiniteTensor`. |
| j sends x to x tensor 1 | First equation in the existential natural isomorphism: `j.hom` equals `trfAutomorphismTensorSection ... x 1`. This section is `scalarExtensionRingIsoTmul`, the actual sheafification-unit generator. |
| j inverse sends x tensor a to c_n inverse(a) x | Second equation for `j.inv`, using `inv (inverseImageFiniteCoefficientMap ...)`. |
| tau sends x tensor a to F(v_n)(x) tensor rho_n(a) | Third equation, with the actual horizontal restriction of the tensor system on the left and the actual restriction of the original system at `gU` on the right. |
| tau j = j F(v_n) | Fourth equation for every section x. Both occurrences of tau and F(v_n) are actual sequence-site restrictions. |
| Comparisons commute with differentials | `j` is an isomorphism of functors into `CochainComplex`; each component and its inverse are bundled chain maps. |
| Naturality in all system chain maps | `j` is a `NatIso` on the entire ordinary complex category; no choice of system morphisms is restricted. The objectwise x tensor 1 formula also fixes naturality at each individual module level. |
| Actual rho_n c_(n+1) = c_n F(rho_n) square | Third main conjunct, written in Lean's left-to-right composition order `c_(n+1) ≫ rho_n = F.map rho_n ≫ c_n`. |
| Actual pi_n c_hat = c_n F(pi_n) square | Fourth main conjunct, written `c_hat ≫ pi_n = F.map pi_n ≫ c_n`. |
| Completed scalar linearity | Final main equation explicitly uses `c_n inverse(pi_n(b))` on the inverse-image source and `pi_n(b)` on the tensor target. The inverse is linear because it is a bundled module isomorphism; the two transitions are already bundled quotient-linear maps, and the recorded cone equation `pi_n = rho_n pi_(n+1)` makes them completed-linear too. The completed square identifies this with inverse image followed by transport along c_hat. |
| Exactness of G | `PreservesFiniteLimits (trfAutomorphismSystemInverse ...)` and `PreservesFiniteColimits ...`, together with its named additive instance. |
| No flatness, cartesianness, bounds or finite Tor amplitude | None occurs among the binders. M ranges over the entire ordinary complex category. |

The auxiliary continuity, naturality, invertibility, tensor functor laws,
additivity, and tensor-evaluation theorems are construction properties already
asserted by this same node. Their proofs are postponed as named theorems, listed
in `lean.declarations`, with source and complete natural-language proof docstrings.
They do not assume a map or a comparison as arbitrary input, and no definition
selects undetermined data from a mere existence assertion.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, publicly retaining the recorded
  coefficient ring, uniformizer, and quotient maps.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`,
  `ProEt.topology`. The scheme-morphism-properties node is explicitly a convention
  node with no independent declaration; automorphism is the usual `IsIso g`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and its publicly retained independent
  universe coefficient system, completion and projections.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`:
  `isoSectionwiseInverseImage`, `isoSectionwiseConstantMap`,
  `isoSectionwiseInverseImage_equivalence`, `isoSectionwiseModuleInverseImage_exact`.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived`, publicly retaining
  `AlgebraicGeometry.ProEtale.inverseImageFiniteCoefficientMap` and
  `inverseImageCompletedCoefficientMap` and their normalized constructions.
  Its integral derived comparison is not substituted for the finite comparison.
- `Sheaf.Paper.SemilinearDerivedSections`:
  `WeilConjectures.SemilinearSections.semilinearDerivedSections` and its actual
  ordinary system model with componentwise exactness. The specialized existing
  category and evaluations are `coefficientSequenceModules` and
  `coefficientSequenceEvaluation` in `Sheaf.Paper.CoefficientRingedSequenceSite`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory`; the present result takes place before localization,
  on the same ordinary cochain complexes used by that construction.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and its public
  dependencies: existing sheaf tensor and `changeOfRingsOfUniverses`,
  `changeOfRingsHomOfUniverses`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso`:
  `SheafOfModules.scalarExtensionRingIsoTmul` and
  `SheafOfModules.exists_scalarExtensionRingIso` (the latter is the proof input).
- The recorded proof inputs for general inverse image, module sheaves and scalar
  restriction are publicly available through these imports:
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
  `Sheaf.CategoryTheory.RingedSiteModules` (`ringedSiteModules`), and
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings` (`restrictScalars`).

Source checked: the current blueprint proof (2) says that automorphism pullback
is an exact monoidal equivalence fixing the constant coefficients and commuting
with reductions and transitions; proof (3) uses compatibility on the entire
reduction tower. The node supplies the seven-step elementary expansion at the
ordinary strict-system level. No unit or chapter statement is changed.

Edge cases checked before writing:

- `g = 𝟙 S`: site transport and coefficient maps are the canonical identity
  identifications, so the comparison is the ordinary tensor-unit map.
- Zero modules and zero transitions: both generator equations give zero;
  transitions are never inverted.
- Nonflat torsion modules and noncartesian systems: scalar extension is along
  c_n, a ring-sheaf isomorphism; rho_n is not required to be flat or invertible.
- Exponent one: `n=0` is exactly R/(varpi); no positive level is omitted.
- Arbitrary negative and positive cochain degrees: q ranges over all integers.
- Empty scheme: no nonemptiness or point hypothesis is added.
- Independent scheme/coefficient sizes: `t` and `u` remain independent, with
  coefficient/module universe `max u (t+1)` and the original small site's Hom
  universe t unchanged.

Existing-declaration searches (real msearch.py calls, logs in searches.jsonl):

- LeanFinder: “For an automorphism, tensor extension along constant coefficient
  isomorphisms is naturally isomorphic to inverse image on arbitrary strict
  quotient semilinear module systems, compatibly with completed scalar
  projections”. Eight hits on ordinary tensor quotient linear equivalences;
  none states the system, chain-map and completed-coefficient comparison.
- Loogle: `SheafOfModules.pullback, SheafOfModules.restrictScalars`. Zero hits.
- Mathlib grep under `Algebra/Category/ModuleCat`:
  `scalarExtension.*[Ii]so|tensor.*[Rr]eduction|[Ss]emilinear.*[Tt]ensor`.
  Zero hits.
- LeanSearch: “A scheme automorphism induces a natural tensor unit isomorphism
  on arbitrary strict quotient semilinear systems of module sheaves, compatible
  with completed coefficient projections”. Eight hits: scheme section-map
  invertibility, free pullback-unit invertibility, and restriction adjunction
  results. None gives the node's arbitrary-system comparison.
- `rg` in the live `lean/WeilConjectures` and `lean/Sheaf`, using the item id,
  automorphism/tensor and scalar-extension-isomorphism patterns. No item match.
  Reused the existing scalar-extension ring-isomorphism theorem; the nearby
  `IsomorphismReductionTower` requires K-flat flat-term source complexes and
  compares integral reduction towers, and `IsomorphismMultiplicationConeDescent`
  concerns good quotient presentations and Roos cones. Neither is this statement.

No new nodes, dependency-record repairs, or statement correction are needed.
The previous worker's stage-1 live-wins refusal does not apply: the current item
is already split and reviewed, but has no Lean record; this delivery changes only
its `lean` field and supplies its stage-2 module.

Validation: every delivered Lean file is checked through scompile.py against
the server's live published build; no local or global library build is used.

The final scompile.py pass is clean: sandbox check 17.8 seconds, library-module
check 17.9 seconds, no errors or warnings. Section evaluation uses the existing
`coefficientEvaluationSection` from `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`
so that the scalar-action transport is explicit without unfolding the coefficient
constructions. No time limit or heartbeat limit was raised.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
