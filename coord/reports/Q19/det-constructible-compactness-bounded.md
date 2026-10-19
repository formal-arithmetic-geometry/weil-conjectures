## Worker report

The module Sheaf.Paper.ConstructibleCompactnessBounded states
`AlgebraicGeometry.ProEtale.constructible_compactness_bounded` for finite coefficient
subextensions and `constructible_compactness_bounded_padicAlgCl` for the condensed algebraic
closure. Both theorem proofs are `sorry`. Their docstrings give all seven induction steps
of the DAG proof. The helper `constructibleBoundedComparison` has real data: it is
`DirectSum.toAddMonoid` of postcomposition with the shifted coprojections.
No statement correction, dependency repair, or new DAG node is needed.

Hypothesis and clause correspondence, applying to both theorems:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- The geometric field is `(k : Type u) [Field k] (p : ℕ) [CharP k p]`, with
  `hp : 0 < p` and `hpl : p ≠ ℓ`. A field of positive characteristic automatically has
  prime characteristic; no perfection, algebraic closedness, or finite-field condition
  is added.
- The separated finite-type k-scheme is `(X : Scheme.{u}) [X.Over (Spec (.of k))]`,
  `[IsSeparated (X ↘ Spec (.of k))]`, `[LocallyOfFiniteType ...]`, and
  `[QuasiCompact ...]`. Locally finite type plus quasi-compact is finite type.
- The chosen algebraic closure is the upstream `PadicAlgCl ℓ`, its standard model for
  the fixed closure in this coefficient convention. The finite case has
  `(E : PadicAlgCl.FiniteIntermediateField ℓ)`, which is an intermediate field of
  `ℚ_[ℓ]` in that closure together with its finite-dimensionality. The closure case
  does not need to bind the unused finite subextension.
- For finite E, the coefficient is `Profinite.continuousMapRingObj E`, with E's induced
  normed-field topology. For the closure it is `Profinite.padicAlgClRingObj ℓ`, whose
  sections are the continuous functions valued in some finite subextension, as the
  DAG requires; this is not the sheaf of all continuous closure-valued functions.
- In both cases `condensedRingObj Λ X` is the pulled-back ring object Λ_X. The sheaf
  category is precisely `CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u+1})
  (condensedRingObj Λ X)`, the category of internal left module objects. All derived
  objects are in its ordinary `DerivedCategory`; there is no completeness condition.
- `C` is a sheaf in this internal-module category. Its assumption
  `hC : IsConstantModelConstructible Λ X C` uses exactly the recorded finite constant
  scalar-model constructibility, rather than upstream arbitrary local presentations.
  The helper places C in degree zero with `(DerivedCategory.singleFunctor A 0).obj C`.
- The bounds are arbitrary integers `(a b : ℤ)` with `hab : a ≤ b`.
- `(I : Type (u+1))` allows all small sets in the same fixed universe used by the
  pro-etale site and its abelian coefficient sheaves. No `Nonempty` instance is required.
- `K` is any I-indexed family in the ordinary ambient derived category.
- For every i and every integer n, `hK` says that the cohomology sheaf
  `(DerivedCategory.homologyFunctor _ n).obj (K i)` satisfies
  `ObjectProperty.ind.{u+1} (IsConstantModelConstructible Λ X)`. Mathlib's `ind`
  literally means the existence of a small filtered colimit presentation in the
  ambient module category with all terms constructible. It is closed under
  isomorphisms and expresses exactly the inline IndCons and hence Dic definitions.
- `hbound` says that this cohomology object is `IsZero` whenever `n < a ∨ b < n`.
  This is exactly vanishing off the closed interval [a,b], without any restriction
  on representatives or on their terms.
- The conclusion supplies `(c : Cofan K)` and `IsColimit c`. Thus c.pt is the ambient
  direct sum of the original unshifted K_i and c.inj i is its coprojection. This
  records the existence of the sum already implicit in the node; it does not assume
  extra coproduct data. A coproduct is specified by its universal property, not by
  choosing an arbitrary map or by asserting that two endpoints happen to be isomorphic.
  Every other chosen coproduct is uniquely isomorphic to this one compatibly with
  all injections, so the conclusion is independent of its choice.
- For every integer s, `Function.Bijective (constructibleBoundedComparison C K c s)`
  says precisely that the displayed additive comparison is an isomorphism of groups.
  Its source is `⨁ i, Hom(C[0], (K i)⟦s⟧)` and its target is
  `Hom(C[0], c.pt⟦s⟧)`. The map is already an additive homomorphism; bijectivity is
  equivalent to being an isomorphism, with no arbitrary isomorphism substituted.
- The summand map is `Preadditive.rightComp _ ((shiftFunctor _ s).map (c.inj i))`,
  namely f ↦ f ≫ iota_i[s]. `DirectSum.toAddMonoid` extends these maps by finite
  sums of the finitely supported input, exactly the node's alpha_s formula.
  The target is the shift of the unshifted ambient sum, so no comparison between
  differently chosen shifted coproducts is hidden in the statement. Mathlib's
  cochain shift has the node's convention `(K[s])^n = K^(n+s)`.

Dependency declarations read and used:

- sk-def-sfb-dc-setting: the recorded module
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
  is imported. Its `CondensedRing.compactificationOverField` and bounded-constructible
  constructions express the standing setting, here expanded as the geometric binders.
  The compactification choice does not occur in this comparison.
- sk-def-sfb-condensed-ring: the closed upstream audit gives
  WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap:
  `Profinite.continuousMapRingSheaf`, `continuousMapRingObj`, and
  `continuousMapRingSheafMap`; Condensed.EllAdic gives `padicIntCondensedRing`,
  `padicCondensedRing`, `padicSubfieldCondensedRing`, and `padicIntegersCondensedRing`.
  The finite-field coefficient spelling follows the published FiniteSubextension
  interface, where `continuousMapRingObj E` is explicitly the ring object E-bar.
- sk-def-sfb-qlbar-condensed: the same EllAdic module's
  `Profinite.padicAlgClCondensedRing` and `padicAlgClRingObj` use finite-subextension-valued
  sections. They are available through the public FiniteSubextension import.
- sk-def-sfb-pulled-back-coefficients: the recorded
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic declarations
  `coefficientRing`, `coefficientRing_X`, `condensedRingObj`, and its commutative-ring
  instance. The statement uses `condensedRingObj`, the recorded unbundled encoding.
- sk-def-sfb-module-objects: the closed Mathlib.CategoryTheory.Monoidal.Mod audit
  records `CategoryTheory.ModObj`, `Mod`, `Mod.forget`, and `Mod.regular`. The statement
  uses exactly `CategoryTheory.Mod` and its inherited action structure.
- sk-def-sfb-constructible: Sheaf.Paper.CondensedConstantConstructibility,
  `AlgebraicGeometry.ProEtale.IsConstantModelConstructible`; its full docstrings,
  `HasFiniteConstantLocalModel`, `IsFiniteConstantStratified`, and the affine-local
  convention were read. This recorded dependency is usable as it stands.
- def-weil-abstract-derived-category: Mathlib.Algebra.Homology.DerivedCategory.Basic,
  `DerivedCategory`, `HasDerivedCategory`, and `DerivedCategory.singleFunctor`;
  HomologySequence's `DerivedCategory.homologyFunctor`. The existing module-object
  framework supplies the ordinary derived-category instance, with no new size equality.
- Generic Mathlib interfaces: CategoryTheory.ObjectProperty.Ind `ObjectProperty.ind`,
  Algebra.DirectSum.Basic `DirectSum.toAddMonoid`, Preadditive.Basic
  `Preadditive.rightComp`, and Limits.Shapes.Products `Cofan`.

Already-stated proof dependencies are imported without `public`:
WeilConjectures.CategoryTheory.TruncationTriangle (`DerivedCategory.truncation_triangle`,
read in full through `scompile.py --source`), Mathlib.Algebra.Homology.Embedding.CochainComplex
(`quasiIsoAt_ιTruncLE`), and Mathlib.CategoryTheory.Triangulated.Pretriangulated
(`Pretriangulated` and `Triangle.coyoneda_exact₂`/`coyoneda_exact₁`). The remaining proof
nodes det-def-localizing-closure-existence, det-ind-heart-ii-sums, and
 det-ambient-ind-derived-sums have no recorded declarations in the inspected DAG, so have
no proof import yet. Their proof steps are retained in both theorem docstrings.

Edge cases checked before stating: I may be empty, and the conclusion then uses the zero
coproduct with the map between zero Hom groups. Zero C and all-zero K are allowed. X may
be empty. Width zero a=b is included, as are negative a,b and every positive, negative or
zero shift s. Uniform vanishing is required only in cohomology, not termwise; individual
complexes need not be bounded as complexes. The finite coefficient case includes E=ℚ_ℓ.
The closure coefficient uses finite-subextension sections even on infinite profinite sets.

Searches for an existing declaration:

- msearch.py leanfinder, query `constructible sheaf Hom commutes with direct sums of
  uniformly bounded ind constructible complexes`: eight unrelated results, including
  SheafOfModules.mapFree, LightCondensed.instIsGrothendieckAbelianLightCondMod, and
  CompHausLike.LocallyConstantModule.functor; no statement match.
- msearch.py leansearch, query `Hom from constructible sheaf to direct sum of uniformly
  cohomologically bounded complexes`: eight general Hom definitions, including
  CategoryTheory.Sheaf.Hom, SheafOfModules.Hom and HomologicalComplex.Hom; no match.
- msearch.py loogle, query `DirectSum.toAddMonoid, PreservesColimitsOfShape`: no hits,
  diagnostic unknown identifier PreservesColimitsOfShape; not treated as absence evidence.
  DirectSum.toAddMonoid was located and read directly in the pinned Mathlib source.
- msearch.py grep, query `constructible.*compact|compact.*constructible`: 13 hits
  about constructible topological spaces and prime spectra, none about this theorem.
- rg in upstream WeilConjectures and side lean/Sheaf for the same conceptual patterns:
  existing finite-coefficient etale and integral-adic compactness results have other
  coefficient categories or completion conditions; none is this rational condensed,
  ordinary-derived, uniformly bounded-family comparison. Exact blueprint-id grep in
  upstream returned no hit. The upstream-name index has no matching declaration.
- rg `IndConstructible|indConstructible|indCons|IndCons` in side and upstream sources
  located Sheaf.Paper.IndConstructibleFilteredColimits; its statements use precisely
  Mathlib `ObjectProperty.ind.{u+1}` of IsConstantModelConstructible. Read that module
  and Mathlib.CategoryTheory.ObjectProperty.Ind in full for the definition, rather than
  introducing a second IndCons notion. It is a different theorem, not a statement match.

Validation uses only the prescribed scompile.py and deliver2.py wrappers. The final
module has explicit universe binders, `set_option autoImplicit false`, no private/local
notions, no data `sorry`, and only the two named postponed theorems. Maintainer independent
review is the review required by the dispatcher's direct-delivery workflow.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
