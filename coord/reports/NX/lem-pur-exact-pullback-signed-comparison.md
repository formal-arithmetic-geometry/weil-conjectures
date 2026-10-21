## Worker report

The module `Sheaf.Algebra.Homology.ExactPullbackSignedComparison` states
`SheafOfModules.ExactPullbackSigned.exact_pullback_signed_comparison` with `sorry`.
The mathematical node statement and its dependency lists are unchanged. All helper
`exactDerivedFunctor` and `exactFactorization` explicitly type the existing Mathlib
constructions to avoid default-universe inference during elaboration. All helper
bodies are real constructions or predicates; the structure only packages the canonical
constraints already named in this node. No tensor, pullback, category, flatness notion
or K-flatness notion is redefined. Its abbreviations `tensor` and `tensorMap` evaluate
the existing bifunctor.

Hypotheses, one by one:

- Sites and the common universe: `C : Type uC`, `Category.{vC} C`,
  `EssentiallySmall.{r} C`, and independently `D : Type uD`, `Category.{vD} D`,
  `EssentiallySmall.{r} D`; topologies `J`, `K`, rings `R`, `S` in `CommRingCat.{r}`.
  No equality of site-object, site-Hom or coefficient universes is imposed.
- Ordinary module sheaves: the published `KFlatFixedTensor.Modules R`, which is the
  transparent `CategoryTheory.ringedSiteModules` specialization of `SheafOfModules`.
- Geometric inverse image and structural ring map: `f : CochainPullback.RingedPullback R S`
  contains `uInv`, `uPush`, their adjunction, finite-limit preservation, `RI`, the
  algebraic inverse-image presentation `I`, and `coefficient : RI ⟶ S`.
  Its `hobj` and `hmap` identify `f.L` with actual scalar extension after inverse image.
  Its module adjunction and additivity are supplied presentation data, whose existence
  the existing `ringedPullbackPresentation_exists` proves for every such morphism.
- Exactness is precisely `PreservesFiniteLimits f.L` and
  `PreservesFiniteColimits f.L`. In this abelian additive setting these encode exactness.
- Unbounded derived categories: `HasDerivedCategory.{wR} (Modules R)` and the
  independent `HasDerivedCategory.{wS} (Modules S)`.
- Canonical derived pullback: `L`, its natural counit `epsilon`, and `hL` asserting
  the universal left-derived-functor property. This is its equivalent complex-localization
  presentation, as in the shift-unit dependency; no arbitrary comparison map replaces it.
- The ordinary canonical comparison is `k : CochainPullback.Comparison f`, the existing
  structure with insertion of one, naturality and its generalized pure-tensor equation.

Conclusions, clause by clause:

- `U` is literally `f.L.mapDerivedCategory`; `kappa` is literally
  `f.L.mapDerivedCategoryFactors`, both from Mathlib. The integer shift comparison
  on `U` and its compatibility with `kappa` are the existing exact-functor instances.
  These are fixed constructions, not existential choices of an exact functor.
- The existential `eta : L ≅ U` satisfies `IsNormalizedIdentification f L epsilon eta`:
  for every flat-term K-flat `P`, `eta.hom.app (Q.obj P) ≫ kappa.hom.app P = epsilon.app P`.
  The following quantified implication is uniqueness among every natural isomorphism
  with that normalization. On resolving models, `epsilon.app P` is the node's `e_P`.
- The supplied `L.CommShift` satisfies `NatTrans.CommShift epsilon ℤ`; thus it is the
  resolution-normalized shift structure. `NatTrans.CommShift eta.hom ℤ` gives every
  integer shift square, including zero and addition through the `CommShift` structures.
- The separate equation at `(CochainComplex.singleFunctor (Modules R) 0).obj M`
  states the degree-zero comparison for every sheaf `M`, without a flatness hypothesis.
  Composition with the existing `mapDerivedCategorySingleFunctor 0` identifies this
  equation with the usual sheaf-to-degree-zero comparison.
- The flatness implication is the separate `∀ M` conjunct using `IsFlatOnSite`.
  The following `∀ P` conjunct preserves exactly K-flat complexes with flat terms,
  using `IsKFlatIndependentCoefficients` and `∀ n, IsFlatOnSite (P.X n)`.
- Preservation of direct sums is `∀ I : Type r, PreservesColimitsOfShape (Discrete I) f.L`.
  The next conjunct states preservation of every integral multiple of a morphism,
  including all differential, shift and interchange signs. Termwise pullback is the
  existing `f.L.mapHomologicalComplex (.up ℤ)`, whose shift comparison in each degree
  is the identity (`mapHomologicalComplex_commShiftIso_hom_app_f`).
- `mu : Phi U ≅ Psi U` is a natural isomorphism of the actual K-flat tensor bifunctors.
  `IsNormalized f k U kappa.hom mu.hom` is exactly the node's representative equation,
  in Lean composition order: `U(r) ≫ mu ≫ tensor(kappa_P,kappa_Q) =
  kappa_total ≫ Q(c) ≫ r'`. This also explicitly provides target resolving witnesses.
  The next conjunct is uniqueness among ALL natural transformations satisfying it.
- `c` in that equation is precisely `CochainPullback.comparison f k P Q`, the total
  of the existing canonical module comparison. Its `Comparison.pure` and insertion
  fields fix the local map `s tensor (x tensor y)` to
  `(s tensor x) tensor (1 tensor y)`, with scalar contraction as inverse, as in the
  cochain dependency. That dependency supplies its unsigned reassociation and signed
  interchange equations; this statement uses those exact maps.
- The existential `muL` has the existing shift-unit predicate `IsNormalized f k L epsilon`.
  The component equation for `mu` is the exact transport
  `eta_tensor.inv ≫ muL ≫ tensor(eta,eta)`. Its normalization uniquely identifies
  `muL` with the shift-unit comparison; no abstract tensor isomorphism is substituted.
- `HasCanonicalTensorShifts` over each ring fixes both derived shift comparisons by
  `representativeIso` and the signed cochain shifts. `tensorShift` composes the unsigned
  first-input extraction with the shifted second-input extraction, then combines
  `[b][a]` to `[a+b]`. On original first-factor degree `p` the coefficient is `(-1)^(bp)`.
  The `∀ a b A B` equation is the first displayed equation in the node, with precisely
  this order of extraction on both sides.
- `TensorConstraints.sigma` is natural in both arguments and its `sigma_model` equation
  identifies it with the actual `CochainComplex.Monoidal.braiding`, sign `(-1)^(pq)`.
  The `∀ A B` equation is exactly `U(sigma) ≫ mu = mu ≫ sigma'`.
- `TensorConstraints.alpha` is natural in all three arguments; `alpha_model` identifies
  it with `HomologicalComplex.associator`, using the two successive representative
  maps on each side. Witnesses explicitly assert the intermediate totals are resolving.
  The final `∀ A B N` equation is exactly the node's unsigned reassociation equation.
  These constraints are on the published tensor and fixed by these normalization
  equations, not another monoidal structure or arbitrary objectwise isomorphisms.

Dependency declarations used (module and names):

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` and its additive/colimit instances.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`, `Q`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `site_derived_tensor_descent_independentCoefficients`, `siteDerivedTensorIndependentCoefficients`.
- `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`: `Modules`, `derivedTensor`,
  `totalTensor`, `representativeIso` (the published tensor and its model comparison).
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `IsFlatOnSite`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`: `IsKFlatIndependentCoefficients`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `mapBifunctor` and both signed shift isomorphisms.
- `Sheaf.SecSmoothPurity.CochainTensorCoherenceData`: `RingedPullback`, `Comparison`,
  `pull`, `comparison`, `ringedPullbackPresentation_exists`. Its normalized ordinary
  comparison is the already published general-site interface of the canonical tensor
  comparison dependency; the ordinary insertion and generalized pure-section equations
  were read, including the current `RingedTopoiTensorComparisonData` declaration.
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`: `cochainPullbackTensorCoherence`.
- `Sheaf.Paper.PullbackTensorCanonicalShiftUnit`: `HasCanonicalTensorShifts`, `Phi`,
  `Psi`, `IsNormalized`, `pullback_tensor_canonical_shift_unit`.
- `Sheaf.Paper.RingedTopoiDerivedPullback`: `ringedTopoiDerivedPullback` (canonical
  homotopy-localization counit, used in the complex-localization presentation).
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `ringedTopoiCanonicalDerivedTensorPullback` (model-normalized tensor pullback).
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`: `mapDerivedCategory`,
  `mapDerivedCategoryFactors`, their `CommShift` instances and the degree-zero comparison.
- Proof imports: `KFlatTotalTensorModel.kFlat_total_tensor_model`,
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`,
  `SheafOfModules.isFlat_ringedToposPullback`, `SheafOfModules.isKFlat_ringedToposPullback`,
  `SheafOfModules.module_pullback_pushforward_adjunction`,
  `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`, and localization in
  `Mathlib.CategoryTheory.Localization.Predicate`. All use the recorded module paths.

Edge cases checked before drafting: the zero complex and zero sheaf; the zero ring;
empty direct sums; `a = 0`, `b = 0`, and negative shifts; both complexes unbounded;
a degree-zero nonflat sheaf; a structural ring map that is not flat while the specified
module pullback is exact; independent site-object, site-Hom and coefficient universes;
independently sized source and target derived Hom universes. No boundedness, nonzero
ring, coefficient characteristic or structural-ring flatness restriction was inserted.
For `a = b = 1`, extraction order matters: first extracting `a` gives sign `(-1)^p`,
whereas extracting `b` first would give `(-1)^(p-1)` before the mixed sign correction.
The definition uses the first order consistently with the node's `(-1)^(bp)`.

Searches made with the prescribed `msearch.py` wrapper (raw entries are in sandbox
`searches.jsonl`):

- LeanFinder: "Exact ringed topos pullback identifies derived pullback with termwise
  localization and canonical signed tensor comparison preserving shifts symmetry and
  associativity". Eight hits, ordinary `SheafOfModules.pullbackIso`, `pullbackComp`,
  free-module and conjugacy results; none is this statement.
- Loogle: `CategoryTheory.Functor.mapDerivedCategory`. Twelve hits, including its exact
  factorization, shifts and single-functor comparison. These are used, but do not state
  the normalized simultaneous tensor comparison.
- Mathlib grep: `mapDerivedCategoryFactors|CommShift₂Int` in `Algebra/Homology`.
  Eleven hits in `BifunctorShift` and `DerivedCategory/ExactFunctor`; the actual exact
  functor and shift APIs were read and reused.
- Project grep: the item ID and `exact.*pullback.*signed` in `lean/WeilConjectures`,
  `lean/Sheaf` and `dag/lean_names_upstream.json`: no matching statement.
- Project search of derived associativity/symmetry found
  `RingedDerivedClosedSymmetricMonoidal`, which uses a different closed-structure
  presentation with coefficient universe `max c v u`; it is not the fixed tensor
  `siteDerivedTensorIndependentCoefficients` of this node. No second monoidal tensor
  is introduced to use it. The helper constraints only package this node's prescribed
  maps on its existing tensor. The shift-unit node supplies separate-input squares,
  but does not supply this exact-functor identification or these three equations.

Source checked: Stacks `sites-cohomology.tex`, lemma-pullback-tensor-product (07A4),
whose proof explicitly uses flat-term K-flat totals and the ordinary tensor comparison;
`sites-modules.tex`, lemma-tensor-product-pullback (03EL); the node's ten-step proof;
and the current blueprint frame-independence proof under `sk-prop-an` (the unit's
pullback-compatible exterior products). No statement dispute or mathematical correction.

## Dependency modules

`lem-weil-pbc-pullback-tensor-canonical-shift-unit`: its live source timed out while
preparing the overlay dependency and again on current-server confirmation, before
compiling the consumer. The sandbox copy of its owning module retains every declaration,
every mathematical signature and its full proof docstring. It disables unused generated
`ActionUnits` structure auxiliaries, and marks `HasCanonicalTensorShifts` and
`IsNormalized` locally irreducible before elaborating the concluding theorem. It also enables the backward elaborator transparency options used in the monoidal
interfaces. No proof or mathematical definition is weakened or replaced. The copied node changes only `lean`,
with the diagnostic and the preserved interface in `lean.note`.

Profiling the timeout identified repeated generic multicospan `HasSheafCompose` searches.
Both files locally disable the overly general multicospan instance search, leaving
Mathlib `hasSheafComposeEssentiallySmallSite` to supply the same proposition by
small-site transport. No mathematical hypothesis changes. Temporary profiling options were removed.

The instance-search adjustment uses `attribute [-instance] ... in` on individual
declarations. Its scope ends at each declaration, preserving the
exported instance configuration. An earlier global-removal draft was replaced before
push. The first complete dry run passed preflight and both compiles; the final scoped
version is checked again before delivery.

Final per-file compilation of the scoped version passed without warnings: repaired
shift-unit dependency 22.8 seconds, consumer library module 41.2 seconds (its separate
sandbox invocation also passed in 51.1 seconds), each under the unchanged 60-second limit.
Both node copies change only `lean`; the item statement, proof and dependency lists
remain verbatim. Both theorem signatures in the records match the files exactly.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
