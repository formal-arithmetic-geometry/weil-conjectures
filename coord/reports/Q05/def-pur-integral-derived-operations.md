## Worker report

The item is stated in `Sheaf.Paper.IntegralDerivedOperations`. It defines the three
ambient integral operations, with the two natural representative comparisons that
normalize the pullback and completed tensor descents. All five declarations have real
data. There are no new theorems or `sorry`s in the item's module. The dependency repairs
below have named postponed theorems with source references and proof plans; no proof
was attempted.

The item's natural-language statement is unchanged. No definition is copied privately.
The finite-field datum and an inequality with a characteristic are not binders: this
node fixes only a prime, its finite p-adic extension, and arbitrary schemes. It uses the
already recorded unrestricted completion, definitionally the common core of the
completion with the auxiliary global finite-field convention.

Clause-by-clause correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`; the finite extension is `(E : Type u)
  [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The valuation ring,
  chosen uniformizer, quotient rings and quotient transition homomorphisms are exactly
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionRing`, and `coefficientExtensionTransition`, reexported through
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`.
- `W : AlgebraicGeometry.Scheme.{t}` is arbitrary, with its actual small site
  `W.ProEt` and `Scheme.ProEt.topology W`. Site objects have universe `t+1`, morphisms
  universe `t`, and coefficients/modules universe `max u (t+1)`; neither a field nor
  a site universe is identified with another.
- The inverse-limit ring sheaf is `completedIntegralCoefficientSheafUnrestricted l E W`.
  Its commutative enhancement `completedIntegralCommRingSheafUnrestricted l E W`
  forgets to that same ring sheaf definitionally. `integralTowerModules l E W`
  is its full module category, and `DerivedCategory (integralTowerModules l E W)`
  is the ambient category in all three signatures, with the standard localization.
- Natural-number index `n` in the dependencies denotes positive exponent `n+1`.
  `integralCoefficientSheaf l E W n` is the constant quotient-ring sheaf at that
  exponent, and `completedIntegralCommRingProjectionUnrestricted` is its actual
  inverse-limit projection. `integralOperationsRestrict l E W n` applies restriction
  of scalars along that projection degree by degree. Its underlying sheaves and maps
  are unchanged; its compatible completed action is the one in the node.
- The good representatives are exactly `integralOperationsGoodComplex l E W`:
  `CochainComplex.IsKFlat` AND flatness of every term (`IsFlatOnSite`). There is no
  boundedness condition. The existence input is the dependency
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
- `unrestrictedIntegralFiniteComplex l E W n` applies the canonical ordinary scalar
  extension along the projection termwise. On good representatives it is precisely
  `P_n`, representing the derived reduction `K_n`. The original recorded
  `integralDerivedReduction` remains imported; the unrestricted reduction interface
  in the well-definedness dependency uses the same canonical change of rings without
  imposing the auxiliary finite-field datum.
- The tower transitions are the dependency's uniquely prescribed generator maps:
  `integralOperationsPullbackTransition` on module-pullback generators, and
  `integralOperationsTensorTransition` on each pure tensor in each total summand.
  They reduce the coefficients and the input sections. They are not arbitrary
  morphisms between levels in a triangulated category.
- `integralOperationsRoos` is the actual `CochainComplex.mappingCocone` of
  `towerTransitionEndomorphism`: the shifted cone of `1-s` on termwise products.
  `integralOperationsRoosFunctor` gives its functorial diagonal product maps. The
  dependency `integralOperationsDerivedLimitProperty` states exactly
  `CategoryTheory.IsDerivedLimit` for the localized strict tower. Exact countable
  products and the derived-limit existence/computation dependencies justify that
  interpretation; no categorical limit in the triangulated category is substituted.
- The morphism is `(f : X ⟶ Y)` for arbitrary schemes. At level `n`,
  `integralOperationsLevelPullback l E f n` is
  `Scheme.coefficientProEtaleModulePullback` along the canonical constant-section
  coefficient map. Its sheafified module Kan extension is the module inverse image
  `f⁻¹(-) ⊗ A_X` from the statement, using the adjoint coefficient structure map.
- `integralDerivedPullback l E f` selects the descended functor `F` from
  `integralOperationsWellDefined l E f X`. The accompanying
  `integralDerivedPullbackComparison` selects the SAME witness's natural comparison
  `GoodLocalization ⋙ F ≅ PullbackOnGood`, so its value on every good representative
  is the prescribed `Rlim Res_n f*(P_n)` up to the normalized comparison.
- `integralCompletedTensor l E W` selects `G` from
  `integralOperationsWellDefined l E (𝟙 W) W`, and
  `integralCompletedTensorComparison` selects that same witness's comparison `d`.
  The identity is used only to instantiate the theorem's unrelated pullback
  parameter; `G` is its completed tensor functor on W. `TensorOnGood` localizes the
  direct-sum total tensors of the two finite reductions and then their strict Roos
  complex. Thus its value is exactly `Rlim Res_n(P_n ⊗ Q_n)` with the stated
  differential and coefficient-reduction transitions.
- Both chosen witnesses include uniqueness of a natural isomorphism COMPATIBLE
  with their representative comparisons, as the well-definedness node specifies.
  This is the universal-property choice authorized in AGENTS.md §5, not a choice
  from a bare `Nonempty` functor, an arbitrary tower map, or a noncanonical cone.
  The theorem also gives the derived-limit property for every representative and
  every representative isomorphism. Arbitrary cone-completion maps are never used.
- `integralDerivedInternalHom l E W` is the universe-generalized dependency
  `CategoryTheory.derivedInternalHomOfUniverses` applied to the completed commutative
  ring sheaf on the same small site. Its source is `D(O)ᵒᵖ × D(O)` and target is
  `D(O)`. The data are `Localization.lift` of the EXISTING `homComplexFunctor`
  after the EXISTING canonical `CochainComplex.kInjectiveResolutionFunctor` in the
  second argument. The Grothendieck property comes from the repaired K-injective
  dependency. Consequently this is ambient sheaf Hom among all completed-ring
  modules, without a completion applied to its result or a complete-subcategory
  restriction. The Hom complex still has product terms and differential
  `d_M φ - (-1)^n φ d_L`.
- The two completions are definitions on the full ambient categories. Agreement
  with Bhatt--Scholze's completion construction on complete objects is not added
  as a defining hypothesis or a theorem of this delivery.

Dependency declarations read and used (including contextual imports):

| Node | Module and declarations |
| --- | --- |
| def-weil-l-adic-coefficient-extension | `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, the coefficient constructions above and `Padic.finite_coefficientExtensionRing` |
| def-weil-pbc-proetale-site | `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`, `Scheme.proEtaleDerivedCategory`; the same site and constant-sheaf construction |
| def-weil-completed-integral-coefficients | `Sheaf.Paper.CompletedIntegralCoefficients`, unrestricted completion, commutative enhancement and projections |
| lem-weil-restriction-of-scalars-exact | `Sheaf.Paper.RestrictionOfScalarsExact`, `completedIntegralRestrictScalars_exact`; termwise unrestricted restriction is also explicitly constructed by the well-definedness module |
| def-pc-kflat-complex | `Sheaf.Algebra.Homology.KFlat`, `CochainComplex.IsKFlat`, `IsKFlatResolution` and the recorded independent-universe tensor/sheafification instances |
| lem-pc-kflat-resolution | `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`, `CochainComplex.exists_isKFlatResolutionIndependentCoefficients` |
| def-pur-sheaf-tensor-product | `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`, `SheafOfModules.siteSheafTensorRight`; the dependency's canonical sheaf tensor is used by the level total tensor |
| def-weil-integral-derived-reduction | `Sheaf.Paper.IntegralDerivedReduction`, `integralDerivedReduction`, its K-flat comparison, and the common unrestricted scalar-extension interface in `IntegralReductionTowerUnrestricted` |
| lem-pur-kflat-change-of-rings | `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`, `SheafOfModules.changeOfRings_isKFlat_of_flat_terms` |
| def-weil-derived-limit | `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`, `CategoryTheory.IsDerivedLimit` |
| lem-weil-proetale-countable-products-exact | `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`, `Scheme.ProEt.countableProducts_exact` |
| lem-weil-derived-limit-existence | `Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence`, `CategoryTheory.exists_isDerivedLimit_and_iso`, `derivedCategory_countableProducts_and_towerLimit` |
| def-weil-scheme-morphism-properties | Recorded convention node, with no declaration of its own; the item only needs Mathlib's `Scheme` and its morphisms |
| def-weil-proetale-inverse-image | `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`, `Scheme.proEtaleSheafInverseImage`; the well-definedness module uses its coefficient-sized `coefficientProEtaleModulePullback` interface |
| prop-weil-pbc-proetale-constant-exact | No recorded Lean declaration. The contextual exactness fact is part of the proof plan of the already stated `integralOperationsWellDefined`; defining its normalized descent does not require a separate exactness proof or an extra assumption |
| def-weil-derived-tensor | `Sheaf.Algebra.Homology.DerivedTensor`, `Scheme.derivedTensor`; the same direct-sum total tensor is used by `integralOperationsTensorLevel` |
| lem-pur-integral-operations-well-defined | `Sheaf.Paper.IntegralOperationsWellDefined`, `integralOperationsWellDefined`, good representatives, actual strict towers, Roos functor and the two localized complex constructions |
| def-pur-derived-internal-hom | Repaired module `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`, `CategoryTheory.derivedInternalHomOfUniverses`; original interface retained by import |
| prop-pur-kinjective-resolutions-exist | Added landed dependency, repaired as described below |

The contextual scalar restriction theorem and original derived reduction use the
finite-field convention, but their actual constructions factor through the unrestricted
coefficient sheaf already provided by their dependencies. The item uses that recorded
unrestricted core, exactly as the well-definedness dependency does. No finite-field
hypothesis is introduced just to fit an older interface.

Edge cases checked before writing: exponent one is index zero, so the zero coefficient
quotient at exponent zero is never included; l=2 and E=ℚ_l satisfy the binders; empty
schemes and zero complexes are allowed; unbounded complexes are allowed throughout;
no separatedness, finite type, qcqs, constructibility, derived completeness, or flatness
of f is required. The identity pullback is still completed pullback on arbitrary ambient
objects; it is not silently identified with the identity functor. The tensor uses
all pairs of degrees summing to the total degree, including infinitely many pairs.
The completed ring sheaf is never replaced by the discrete constant integer-ring sheaf.

Searches for existing declarations:

- `msearch.py`, LeanFinder: “derived completed tensor product and completed pullback
  of integral l adic sheaves defined by inverse limits of finite coefficient reductions”.
  Eight hits, all ordinary adic completion/tensor results; no sheaf-derived operation.
- `msearch.py`, Loogle: `integralDerivedPullback, integralCompletedTensor, derivedInternalHom`.
  No hit; the first identifier is unknown.
- `msearch.py`, grep in Mathlib `Algebra/Homology`:
  `completedTensor|derivedInternalHom|integralDerivedPullback`. No hits.
- `msearch.py`, LeanSearch: “derived completed tensor product of sheaves of modules
  inverse limit”. Service unavailable, Internal Server Error; no mathematical verdict
  inferred from this failure.
- `rg` of the upstream source and `lean/Sheaf` for integral derived operations,
  completed tensor and the node id found the finite reduction and well-definedness
  modules, but no descended integral operation. A direct node-id search of upstream
  returned no match. Existing finite-coefficient and condensed module-object
  operations do not define these inverse-limit integral operations.
- Read the current server source of `Sheaf.Algebra.Homology.DerivedInternalHom` with
  `scompile.py --source`; it confirms the site/coefficient universe specialization.
  The current server source of `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`
  confirms the distinguished-triangle predicate, rather than a chosen-limit functor.
- For the repairs, searched existing generalized Grothendieck/K-injective and internal
  Hom declarations in `lean/Sheaf` and upstream. The generalized Hom complex is already
  present and reused; the recorded K-injective and derived internal Hom interfaces
  were restricted to one universe. No duplicate notion or new DAG node is introduced.

Source verification: read [Bhatt--Scholze](https://arxiv.org/pdf/1309.1198),
Definition 3.4.10 and Lemmas 3.4.11, 3.4.12(4), 6.5.9(4), and
[Stacks 099N](https://stacks.math.columbia.edu/tag/099N), clause (5).
For the dependency repair read [07A5](https://stacks.math.columbia.edu/tag/07A5)
and [08J7](https://stacks.math.columbia.edu/tag/08J7). Section 6.5's qcqs hypotheses
belong to its comparison/preservation results; the node's strict reduction-and-Roos
construction on arbitrary schemes is already specified by its well-definedness node.

Validation: all four delivered modules pass `scompile.py` together, separately in
import order, with no errors or warnings. The final item takes about 14 seconds on
the server, below the 60-second per-file limit. No global build was run. The initial
compile failures (universe metavariables and a stale K-flat artifact) were repaired;
there is no unresolved statement dispute.

## Dependency modules

Current second-reading addition: `lem-pur-integral-operations-well-defined` is supplied
in `Sheaf.Paper.IntegralOperationsWellDefined`. Its legacy K-flat and tensor
infrastructure calls did not support the published independent-coefficient interface.
The repair uses the existing `KFlatIndependentCoefficients` declarations and explicitly
installs its monoidal-localization witness in the pure-tensor section helper. It
retains the strict towers, canonical generator maps, Roos functor, both invariance
clauses, both normalized descents, both uniqueness clauses and both derived-limit
clauses. The final packet reuses the published K-flat and reduction-tower modules
as existing instead of delivering their stale replacements.


`def-pur-derived-internal-hom`: its recorded `derivedInternalHom` has `[SmallCategory C]`
and coefficient/module universe equal to the site object universe. This cannot express
our `Type (t+1)`/`Category.{t}` pro-etale site with independent coefficient field size.
`DerivedInternalHomOfUniverses` imports and retains that interface, then supplies the
same localization of the existing Hom-complex functor after canonical functorial
K-injective replacement, with coefficients in `max c v r`. Its one postponed theorem,
`derivedInternalHomOfUniverses_inverts`, is precisely the quasi-isomorphism-invariance
clause of this definition node and has the localization proof plan in its docstring.

`prop-pur-kinjective-resolutions-exist`: added as an already landed dependency to
support that repair. The recorded theorem again identifies the site and coefficient
universes. `RingedSiteKInjectiveResolutionsOfUniverses` imports its original module and
states all the source clauses in independent site universes: Grothendieck abelianness,
the specified free-sheaf generator, and functorial K-injective resolutions with injective
terms. The free sheafified lifted representable is the localized-unit extension:
its sections before sheafification are the finite formal linear combinations of arrows
V→U with coefficients in O(V). This is the same generator, with an innocuous lift of
its indexing type. The theorem `grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`
is postponed with its complete generator/small-object proof plan.

`def-pc-kflat-complex`: compiling the complete packet exposed an older published artifact
in which `IsKFlatResolution` only accepted site-sized coefficients. The current recorded
source already has the correct independent-universe declarations. The delivered `KFlat`
file is that source, with only a documentation note about this application added; it
recompiles the canonical interface in the paired overlay. All declarations and proof
plans are unchanged. Its five existing postponed tensor/sheafification infrastructure
theorems remain recorded, together with `IsKFlat` and `IsKFlatResolution`.

There are no new nodes and no statement correction.


`def-weil-integral-reduction-tower` (returned-head repair): the published artifact
specializes K-flat resolution to site-sized coefficients, so the canonical tower
is supplied in the paired packet. All three resolution hypotheses explicitly use
site object universe t+1, morphism universe t and coefficient universe max u (t+1).
The inverse system, canonical augmentation maps, compatibility statement and cone
retain their original data and hypotheses. Its node's `lean.note` explains the
unusable artifact; the item adds this already landed statement dependency.

## Earlier second reading (a previous round; superseded)

I independently read the item node, all nineteen statement-dependency records,
their available source declarations (including the unrestricted completion/reduction
and coefficient-sized inverse-image interfaces), and all four delivered modules.
This item has no `statement_change` and introduces no new DAG node. Its natural
statement is unchanged. The dependency repairs change only `lean` records; the
additional K-injective-resolution dependency is an already recorded node.

Source reading: the local literature checkout contains only catalogs. I therefore
obtained the Stacks project's actual `proetale.tex`, `sites-cohomology.tex`, and
`sites-modules.tex` from its official repository into the sandbox scratchpad and
read the cited passages, together with the Bhatt--Scholze PDF. In particular:

- [099N](https://stacks.math.columbia.edu/tag/099N), `lemma-pushforward-Noetherian-case`,
  assumes a Noetherian ring and an ideal, and concerns complete objects in (5).
  The preceding naive-completion lemma defines the reduction-limit construction
  for arbitrary objects. Here the coefficients come from a finite extension's DVR;
  Noetherianness is a property of that coefficient construction, not an extra
  scheme hypothesis. The node explicitly separates the ambient definitions from
  their comparison with completion on complete objects.
- [Bhatt--Scholze](https://arxiv.org/pdf/1309.1198), Definition 3.4.10, defines
  completed tensor for arbitrary ambient inputs. Lemma 3.4.11 assumes completeness
  of the second argument for its preservation/adjunction conclusions, not for
  defining ambient internal Hom. Lemma 3.4.12(4) is the Koszul-tower criterion;
  it alone is not a general identification with ordinary quotient reductions.
  The actual quotient-reduction construction here is fixed by the node and its
  well-definedness dependency, with the DVR coefficients and Stacks 099N context.
- Section 6.5 assumes qcqs schemes for its constructibility and comparison results.
  The present node defines strict reduction/Roos constructions for arbitrary
  schemes, relying on its already stated well-definedness node; it does not assert
  the section's preservation or adjunction theorems on arbitrary schemes.
- [07A5](https://stacks.math.columbia.edu/tag/07A5) gives the localized-unit
  generator and functorial K-injective resolutions on a ringed site.
  [08J7](https://stacks.math.columbia.edu/tag/08J7) constructs internal Hom using
  any source representative and any K-injective target representative. These
  are exactly the clauses relevant to the dependency repair below.

The following is my object/hypothesis/conclusion list, matched against the Lean.
Every row has verdict PASS after the repair described below.

| Node object or clause | Lean rendering and check |
| --- | --- |
| Prime ell; finite extension E/Q_ell | `l : ℕ`, `[Fact l.Prime]`, `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`; no field characteristic of a scheme or finite-field datum is added. |
| Integers, one chosen uniformizer, quotient rings, quotient reductions | The imported `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, `coefficientExtensionRing`, `coefficientExtensionTransition` are the recorded coefficient datum; finite-level constants use exponent `n+1`. |
| Arbitrary W and the small pro-etale site | `W : Scheme.{t}`, `W.ProEt`, `Scheme.ProEt.topology W`; objects live in `t+1`, morphisms in `t`. |
| Actual inverse-limit completed ring sheaf, projections | `completedIntegralCoefficientSheafUnrestricted`, its commutative presentation and projections; the old finite-field convention factors through this same construction definitionally. It is not the discrete constant sheaf of integers. |
| Full ambient derived module category | `DerivedCategory (integralTowerModules.{t, u} l E W)` with the standard localization; module universe `max u (t+1)`. |
| Exact restriction of scalars applied termwise | `integralOperationsRestrict` applies the recorded `SheafOfModules.restrictScalars` along the completed projection via `mapHomologicalComplex`; the underlying abelian sheaf and its maps are retained. No exactness assumption is introduced. |
| K-flat resolutions with flat terms, unbounded | `integralOperationsGoodComplex` is exactly `IsKFlat` together with `∀ i, IsFlatOnSite (P.X i)`; `exists_isKFlatResolutionIndependentCoefficients` supplies these representatives. |
| Finite reduction P_n representing K_n | `unrestrictedIntegralFiniteComplex` is ordinary scalar extension along the actual projection, applied termwise; the reduction dependency identifies it with derived reduction on these good representatives. |
| Finite-reduction transition maps | `unrestrictedIntegralTransition` is the unique natural chain map prescribed on sheafified pure tensors, not a chosen derived-category arrow. |
| Rlim is Cone(1-s)[-1] on termwise products | `integralOperationsRoos` uses `mappingCocone` of `towerTransitionEndomorphism`; `RoosFunctor` maps both summands by the diagonal product map. `integralOperationsDerivedLimitProperty` is the recorded distinguished-triangle predicate `IsDerivedLimit`, not a categorical limit. |
| Arbitrary scheme morphism f | `{X Y : Scheme.{t}} (f : X ⟶ Y)`; no flatness, qcqs, finite-type, separation or properness instance. A common sufficiently large scheme universe includes all pairs. |
| Finite module inverse image along the canonical coefficient map | `integralOperationsLevelPullback` is `coefficientProEtaleModulePullback`; its adjoint direct image is sectionwise pushforward with action through the constant-section map. Thus it is the node's sheafified module Kan extension, canonically equivalent to its tensor formula. |
| Pullback value Rlim Res_n f*(P_n) | `integralDerivedPullback` chooses F from `integralOperationsWellDefined`; `integralDerivedPullbackComparison` chooses e from the same witness. The compared functor is exactly `integralOperationsPullbackOnGood`. |
| Tensor value Rlim Res_n Tot(P_n tensor Q_n) | `integralCompletedTensor` chooses G and `integralCompletedTensorComparison` chooses its d from the same theorem witness. `integralOperationsTensorLevel` uses the direct-sum total tensor and its usual signed differential, then restriction. |
| Tensor and pullback transition normalization | The well-definedness module's two `existsUnique` generator formulas are used by its tower functors. Tensor transitions reduce both factors on every (p,q) summand; pullback transitions respect the adjunction-unit generators. |
| Independence, functoriality, uniqueness compatible with comparisons | The selected witness includes natural comparisons e,d, unique compatible natural isomorphisms with all other such descents, and the derived-limit property for all representatives and representative isomorphisms. No bare existence choice of an arbitrary functor is made. |
| Ambient internal Hom, contravariant in M, covariant in N | `integralDerivedInternalHom` applies `derivedInternalHomOfUniverses.{t+1,t,u}` to the same completed commutative sheaf. It localizes the existing `homComplexFunctor` after canonical functorial K-injective replacement in the second argument. Source is D(op) times D and target is the same full D. |
| Internal Hom terms, differential, independence of representatives | The imported Hom-complex terms are products of localized sheaf Hom with differential d_N phi - (-1)^n phi d_M. The generalized comparison and arbitrary-representative theorem added in this reading expose the node's remaining independence clauses without a universe restriction. |
| Comparison with completion is not a defining hypothesis | None of the five main declarations requires completeness or constructibility, and none asserts preservation, an adjunction, or that identity completed pullback is the identity on all ambient objects. |

Dependency-module review (H13):

- `def-pc-kflat-complex`: read its Stacks 06YN definition and 06YS terminology
  against both `IsKFlat` and `IsKFlatResolution`. They respectively quantify over
  every acyclic tensor test and require `QuasiIso f ∧ IsKFlat K`. The independent
  coefficient universe is retained. Compared with the current shared source, this
  delivered module differs only by its application note; its named infrastructure
  theorem statements and proof plans are unchanged. The paired source recompilation
  addresses the recorded artifact mismatch without defining another K-flat notion.
- `prop-pur-kinjective-resolutions-exist`: read the original specialized declaration,
  the whole node, and the generalized module. All three clauses are present:
  Grothendieck abelianness, the specified generator, and functorial resolutions
  with injective terms. `uliftYoneda` followed by the free module functor has sections
  consisting of finite formal linear combinations of arrows V→U with coefficients
  in O(V); sheafification is precisely the localized-unit extension generator of
  07A5. The lift changes only size. A natural transformation from the identity and
  universal quantification over all complexes give the stated functoriality.
- `def-pur-derived-internal-hom`: the original interface really does require
  `[SmallCategory C]` and site-sized coefficients, whereas the Hom-complex dependency
  already supports independent universes. The generalized definition reuses that
  Hom complex and the source library's actual K-injective replacement, then
  `Localization.lift`; there is no data-valued `sorry` or second Hom-complex notion.
  I found that its comparison and arbitrary-representative clauses were exposed
  only at the original specialized universes. I added
  `derivedInternalHomOfUniverses_comparison` and
  `derivedInternalHomOfUniverses_obj_iso`, with exactly the clauses already in this
  dependency node and its three proof steps. Both are postponed theorems with
  source/blueprint docstrings and full proof plans. Their names are added to
  `lean.declarations` and their purpose to `lean.note`. This supersedes the worker
  report's description of this repair as having only one postponed theorem.

Edge cases: index zero is exponent one, so all positive exponents and every
successor transition are covered; the construction never demands an exponent-zero
quotient. The infinite tower is fixed and nonempty; there is no extra nonempty
hypothesis on an input index type. Empty schemes, zero complexes and unbounded
complexes are allowed. The total tensor includes every integral-degree pair with
the prescribed sum, using coproducts rather than finite sums. Ell=2 and E=Q_ell
are allowed, as are schemes in characteristic ell. No inequality ell≠char(W) is
present. The universe maximum contains site objects, site morphisms and coefficient
sections independently; no equality of these universes is imposed. The empty site
case of the generator is its zero coproduct, a separator in the trivial sheaf
category. Identity completed pullback retains completion on ambient inputs.

Independent searches (H4):

- LeanFinder via `msearch.py`: “Derived completion of tensor products of integral
  proetale sheaves and inverse image via reduction towers”. Eight results, all
  ordinary adic tensor/completion or unrelated algebra statements; none constructs
  these operations on completed-ring module sheaves.
- Loogle via `msearch.py`: `CategoryTheory.derivedInternalHom`. Unknown identifier,
  zero results; no conclusion about project declarations inferred from that index.
- LeanSearch via `msearch.py`: “completed derived pullback sheaves integral
  coefficients inverse limit”. Service unavailable (Internal Server Error), recorded
  as unavailable rather than as evidence of absence.
- Direct `rg` of Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf` for
  `completed.?tensor`, `derived.?completion`, `integralDerived`, integral pullback,
  and universe-general K-injective/internal-Hom interfaces. Upstream completion
  diagrams in `CategoryTheory/DerivedCategory/Complete` concern constant R-module
  sheaves, not modules over the inverse-limit ring sheaf; the condensed/module-object
  framework is another category. The project has the strict reduction/descent
  dependencies and specialized internal Hom, but no existing copy of this item's
  three descended operations. The two new generalized comparison names are absent
  from both source trees and Mathlib.

No mismatch in the item's statement, hypotheses, resolution choices, tower maps,
or three definitions required changing them. I repaired only the incomplete
universe-general internal-Hom dependency interface. The node's `lean.statement`
continues to be verbatim its main declaration's signature, and the same check is
made for each dependency record. Every new theorem is `by sorry`; no proof was
attempted. All definitions contain actual data, including universal-property choices
with their normalizing comparisons. There are no private declarations or local
notation in the delivered modules, and every line is within 100 columns.

Validation after the repair: `scompile.py` compiled all four delivered modules in
one paired packet, separately in import order, with no errors or warnings.
Timings were 2.4 s (KFlat), 1.6 s (K-injective resolutions), 2.5 s (internal
Hom), and 13.8 s (the item); every invocation used nice 19, two threads and
the 60-second limit. No global build was run. Verbatim signature checks for
all four node records and declaration-inventory checks passed.

## Repair of the returned immutable head

The return reported (1) coefficient-universe mismatches at all three uses of
`IsKFlatResolution` in `IntegralReductionTower`, followed by missing declarations
because its first definition failed, and (2) `nt_compile.py` exhausting storage
while creating its private overlay. This repair does not change any mathematical
statement, identify universes, or add a finite-field hypothesis to the operations.

For (1), the delivery now includes the canonical `IntegralReductionTower` source
as a dependency module. Each of its three resolution hypotheses explicitly uses
`CochainComplex.IsKFlatResolution.{t + 1, t, max u (t + 1)}`. Including this
module makes it a sibling compiled after the delivered `KFlat` interface; the
local overlay must no longer auto-compile it before that sibling exists, against
the stale site-sized published artifact. Its definitions and the complete proof
plan of `integralReductionTowerMap_naturality` are unchanged. That restores both
`integralReductionTowerMap` and its subsequent uses in the compatibility theorem
and augmented cone.

Dependency module `def-weil-integral-reduction-tower`: the old compiled dependency
cannot accept the coefficient universe of the actual completion. The replacement
states the same inverse system, its maps `[q]⁻¹ ≫ [γ_n]`, compatibility on every
opposite-natural-number arrow, and the resulting cone. It uses the recorded
`integralTowerComplex`, `integralTowerTransition`, `integralTowerAugmentationIso`
and `integralTowerUnit` from `IntegralReductionTowerWellDefined`. The prime,
finite extension, finite-field datum and inequality remain only in that legacy
tower interface. The item's unrestricted operations remain free of the datum
and inequality. Natural-number zero still denotes exponent one; every complex
and coefficient universe is independent. Its node is added to the item's
statement dependencies; only its `lean` record is repaired.

For (2), the prescribed compilation and dry-run wrappers will be retried. The
reported storage traceback is a tool failure rather than a Lean error; no tool,
shared checkout, compiler limit or live artifact is edited by this worker.

Repair validation: the five delivered files compiled cleanly as one prescribed
`scompile.py` packet, each file separately in dependency order. The wrapper also
rebuilt the unrestricted tower, coefficient pullback and operation-well-definedness
imports. Reported times were 2.5 s for KFlat, 1.7 s for K-injective resolutions,
3.1 s for internal Hom, 2.7 s for the repaired reduction tower and 14.7 s for the
item. All files used nice 19, two threads and the 60-second limit. All five node
signatures exactly match their source signatures and all lines fit 100 columns.


## Local compiler diagnostic after the repair

The required wrapper confirms the repaired five-file packet on the server, but
its local path still has a compiler-tool ordering fault. Read-only Python tracing
of the unchanged `scompile.py` wrapper captured the discarded local diagnostic:

```
overlay Sheaf.Paper.IntegralReductionTowerUnrestricted
error: object file 'Sheaf/Paper/IntegralReductionTower.olean' of module
Sheaf.Paper.IntegralReductionTower does not exist
```

`nt_local_compile.run` calls `ensure` for outside dependencies before compiling
any supplied sibling. It skips `IntegralReductionTower` because it is a supplied
sibling, then compiles its outside consumer `IntegralReductionTowerUnrestricted`
before that sibling exists. Thus the explicit-universe repair removes the
returned stale-interface elaboration, but the immutable-head local compiler
cannot validate this dependency packet with its current ordering. The ordinary
wrapper correctly falls back to server confirmation, which succeeds. No module
is missing from the source or from the delivered packet. No tool or live artifact
was edited. This tooling fault must be handled by the maintainer; a duplicate
canonical tower definition or a site-universe restriction is not a valid repair.

## Earlier second reading (a previous round; superseded)

This is a fresh second reading of the returned five-module packet. I read the
item's unchanged statement, the twenty current dependency-node records, the
signatures and constructions used by the item, and all five delivered modules.
There are no new nodes and no statement_change. The item is a definition node
with an empty proof plan: it defines the operations, while its recorded
well-definedness dependency states their invariance and normalized descent.

I read the actual source text in the sandbox: Bhatt--Scholze, Definition 3.4.10,
Lemmas 3.4.11, 3.4.12(4), and 6.5.9(4); Stacks proetale.tex,
lemma-naive-completion and lemma-pushforward-Noetherian-case (099N);
sites-cohomology.tex, definition-K-flat (06YN), section-unbounded (07A5),
and section-internal-hom (08J7). The source's Noetherian coefficient hypothesis
is satisfied by these DVR coefficients; it is not a Noetherian scheme
hypothesis. The qcqs assumptions of Section 6.5 and the complete-object
assumptions of 099N(5) belong to their comparisons and adjunctions. The node
explicitly defines ambient reduction/Roos operations and leaves their agreement
with completion on complete objects to a separate comparison. No such comparison
or completeness assertion is silently made by these definitions.

The object, hypothesis and clause list, with its Lean rendering and verdict:

| Node object, hypothesis or clause | Lean rendering | Verdict |
| --- | --- | --- |
| A prime ell | `l : ℕ`, `[Fact l.Prime]` | Exact. |
| A finite field extension E/Q_ell | `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` | Exact, no topology supplied as an additional hypothesis. |
| Integers, chosen uniformizer, positive quotient rings and quotient reductions | The dependency's `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, `coefficientExtensionRing` and `coefficientExtensionTransition`; tower level n is exponent n+1 | Exact, including all positive exponents. |
| An arbitrary scheme W and its small pro-etale site | `W : AlgebraicGeometry.Scheme.{t}`, `W.ProEt`, `Scheme.ProEt.topology W` | Exact; object universe t+1 and morphism universe t remain distinct. |
| The completed ring sheaf, not the discrete constant integer sheaf | `completedIntegralCoefficientSheafUnrestricted l E W`, the actual limit of `integralCoefficientSheafSystem` | Exact. The commutative enhancement forgets to the same ring sheaf. |
| All modules and their unbounded derived category | `integralTowerModules.{t,u} l E W`, `DerivedCategory` with the standard localization | Exact. No complete or constructible subcategory is substituted. |
| Restriction along the actual projection pi_n, applied termwise | `integralOperationsRestrict`, using `completedIntegralCommRingProjectionUnrestricted` and `mapHomologicalComplex` | Exact. Underlying sheaves and maps are unchanged. |
| A K-flat representative with flat terms, with no boundedness restriction | `integralOperationsGoodComplex` is `CochainComplex.IsKFlat` conjoined with `∀ i, SheafOfModules.IsFlatOnSite (P.X i)` | Exact; existence is `exists_isKFlatResolutionIndependentCoefficients`. |
| Termwise reduction P_n and its canonical maps | `unrestrictedIntegralFiniteComplex`, based on ordinary scalar extension along pi_n; `unrestrictedIntegralTransition_existsUnique` fixes each transition on s tensor x | Exact; no arbitrary transition morphism is chosen. |
| Cone(1-s)[-1] on termwise products, interpreted as Rlim | `integralOperationsRoos` is `CochainComplex.mappingCocone (towerTransitionEndomorphism ...)`; `integralOperationsDerivedLimitProperty` is `CategoryTheory.IsDerivedLimit` | Exact; not a categorical limit in a triangulated category. |
| Arbitrary scheme morphism f:X to Y | `{X Y : Scheme.{t}} (f : X ⟶ Y)` | Exact; no separatedness, finite type, flatness or characteristic hypothesis. |
| Module inverse image along the canonical coefficient structure map | `integralOperationsLevelPullback` is `coefficientProEtaleModulePullback` on the constant finite quotient, with its constant-section adjoint map | Exact; it is the sheafified module Kan extension, not the unrelated scheme-module pullback. |
| Lf* K = Rlim Res_n f*(P_n) | `integralDerivedPullback` selects F from `integralOperationsWellDefined`; `integralDerivedPullbackComparison` selects the same witness's e | Exact on all good representatives and their maps. |
| The completed tensor = Rlim Res_n(P_n tensor Q_n) | `integralCompletedTensor` selects G from the same normalized-descent theorem; `integralCompletedTensorComparison` selects its d | Exact. The identity morphism instantiates only the theorem's unrelated pullback parameter. |
| The total tensor, its differential, and the coefficient-reduction transitions | `integralOperationsTensorLevel` uses `map₂CochainComplex`; `integralOperationsTensorTransition_existsUnique` fixes every pure tensor in every (p,q) summand | Exact: coproduct totalization, differential d_P tensor 1 + (-1)^p 1 tensor d_Q. |
| Functoriality and independence of representative choices up to unique compatible isomorphism | The selected witnesses are actual functors; the accompanying e and d are natural isomorphisms, and their defining theorem includes uniqueness compatible with these comparisons | Exact. This is universal-property choice, not choice of an arbitrary functor from bare existence. |
| Ambient internal Hom, contravariant in M and computed with a K-injective resolution of N among all modules | `integralDerivedInternalHom` applies `derivedInternalHomOfUniverses.{t+1,t,u}` to the completed commutative ring sheaf | Exact. Source is D(O)^op times D(O); target is D(O). No completion is applied to the result. |
| The derived internal-Hom construction and independence clauses of its dependency | `Localization.lift` of the existing `homComplexFunctor` after canonical K-injective replacement; generalized `_inverts`, `_comparison`, and `_obj_iso` | Exact. Any source representative and any K-injective target representative are covered. |

I independently checked the dependency modules against their own nodes (H13).
The generalized K-injective theorem retains Grothendieck abelianness, the specified
generator, functorial replacement, quasi-isomorphisms, K-injectivity and injective
terms. The free sheaf on lifted Yoneda at U is the sheafification of the localized
unit's extension: over V its generators are the arrows V to U with coefficients
in O(V). Thus its generator is the source's generator, not an arbitrary separator.
All three site/ring sizes fit max c v r. The generalized internal Hom retains
all four clauses of its definition node, including the two comparison clauses;
its only chosen data are canonical replacement and localization. The KFlat
packet states the existing acyclicity definition and K-flat resolution definition
verbatim; its named infrastructure theorems have their source proof plans.
The paired reduction tower uses the same localized pure-tensor reductions,
[q] inverse followed by gamma_n, compatibility on every opposite-natural arrow,
and the resulting augmented cone. Each of its three K-flat-resolution binders
explicitly has universes t+1, t, max u (t+1).

Current-base mismatch found and repaired: the worker's reduction-tower note did
not discuss Q29's newer `SfIntegralReductionTower` record. I read that module:
its scheme and coefficient field both have universe u, whereas the unrestricted
strict-tower import required here has independent t/u. I updated the dependency
note and module documentation to explain precisely why the paired legacy repair
is still necessary. The newer Sf module and its declarations remain untouched
in the library. A trial public import of it exposed a separate universe-inference
failure in that outside module; I removed the trial import, since none of this
packet's constructions use that specialization. This adds no assumption to the
item and does not replace its unrestricted completion or reduction construction.
No mathematical signature or data of the item required a change.

Edge cases: index zero means exponent one, so no exponent-zero quotient enters;
ell=2 and E=Q_ell are allowed. Schemes in characteristic ell, empty schemes,
zero objects, zero complexes and arbitrary unbounded complexes are allowed.
No finite-field datum or ell-not-equal-characteristic hypothesis is introduced.
The tensor sums over all integer pairs, including infinitely many summands.
An empty underlying site has the empty generator coproduct, a separator in the
trivial sheaf category. There is no optional nonempty or finite indexing
hypothesis. Identity completed pullback still includes completion on ambient
objects. The coefficient universe max u (t+1) retains independent scheme and
field universes; the internal-Hom repair also retains independent site object
and morphism universes and a variable derived-category universe.

Independent searches in this reading (H4):

- LeanFinder through msearch.py: "Derived completed pullback and tensor of l-adic
  module sheaves from quotient coefficient towers". Eight hits in classical
  AdicCompletion tensor algebra, including `AdicCompletion.ofTensorProduct`;
  no operation on the completed-ring module derived categories.
- Loogle through msearch.py: `"completion", "tensor"`. The results concern
  ordinary adic tensor/completion maps; none defines these derived operations.
- LeanSearch through msearch.py: "Completed derived inverse image functor on
  pro-etale sheaves from finite quotient reductions". Service unavailable,
  Internal Server Error; no absence verdict inferred.
- Direct rg in Mathlib Algebra/Homology, the upstream WeilConjectures source,
  and the project lean/Sheaf with `derived.*complet`, `complet.*tensor`,
  `derived.*inverse.image`, `internal.*hom`, and the three proposed declaration
  names. The existing ordinary adic-completion algebra and generic internal-Hom
  and constant-coefficient completion frameworks use other categories or do not
  supply these operations. The project's strict good-representative/Roos
  machinery is reused. Its specialized derivedInternalHom was opened and does
  not type the small pro-etale site with independent coefficient size; the
  delivered generalized interface supplies the same construction. There is no
  exact existing declaration of the three operations to record instead.

All delivered declarations have source/blueprint docstrings. Every postponed
proof is a named theorem with the corresponding node's proof plan; no theorem
was proved. Definitions have actual data, with universal-property choices only
where the normalizing comparisons determine the object up to the equality used
downstream. The primary lean.statement fields were checked against the literal
file signatures, and no variable or universe is auto-bound. No target or unit
statement changes.

Final validation for this reading: all five delivered modules pass the prescribed
scompile.py packet separately in dependency order, with no errors or warnings.
Reported times are 2.5 s (KFlat), 1.6 s (K-injective resolutions), 2.6 s
(internal Hom), 2.9 s (paired reduction tower), and 14.2 s (the item).
The wrapper also successfully checked its unrestricted-tower, coefficient-pullback
and well-definedness imports. Nice 19, two threads and the default 60-second limit
were retained; no global build was run. All five primary signatures match their
node records literally, and the final dry run printed OK and passed preflight.

## Second reading by Q05

This reading checks the final packet against the current source and published library;
it supersedes the earlier rounds above. I did not write the submitted operations.
I read the item node, every statement-dependency record and the relevant declaration
signatures, all delivered modules, and the canonical coefficient, strict-tower,
coefficient-pullback and Hom-complex constructions. There is no new node and no
statement correction. No unit or target statement changes.

Source reading: Bhatt--Scholze Definition 3.4.10, Lemmas 3.4.11, 3.4.12(4), the
setup of Section 6.5, and Lemma 6.5.9(4), in the scratchpad PDF text; Stacks
proetale.tex, lemma-naive-completion and lemma-pushforward-Noetherian-case (099N);
sites-cohomology.tex, definition-K-flat (06YN), section-unbounded (07A5), and
section-internal-hom (08J7). The coefficients are the finite extension's DVR.
The arbitrary ringed-site constructions of tensor completion and internal Hom
apply here; Section 6.5's qcqs assumptions concern its comparison/preservation
results. The item's ambient strict reduction/Roos definitions make no claim of
that comparison on every ambient object. The complete-input assumption of
099N(5) is likewise not silently turned into a hypothesis of these definitions.

Object, hypothesis and conclusion checklist, with Lean rendering and verdict:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Prime ell | `l : ℕ`, `[Fact l.Prime]` | Exact. |
| Finite extension E/Q_ell | `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` | Exact; no extra topology binder. |
| Integer ring, uniformizer, positive quotient rings and reductions | `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`, `coefficientExtensionRing`, `coefficientExtensionTransition` through `CoefficientExtensionFinite` | Same canonical coefficients; level n means exponent n+1. |
| Arbitrary scheme W and its small pro-etale site | `W : Scheme.{t}`, `W.ProEt`, `Scheme.ProEt.topology W` | Exact; objects t+1, morphisms t. |
| Completed coefficient sheaf | `completedIntegralCoefficientSheafUnrestricted l E W` | Actual inverse limit of the constant quotient ring sheaves, not the discrete constant integer ring. |
| Commutative presentation of the same ring | `completedIntegralCommRingSheafUnrestricted` | Forgetting commutativity gives the same ring sheaf; data unchanged. |
| All module sheaves and their unbounded derived category | `integralTowerModules.{t,u} l E W`, `DerivedCategory` with standard localization | Exact ambient category, with coefficient size max u (t+1). |
| Restriction along pi_n, term by term | `integralOperationsRestrict` using `completedIntegralCommRingProjectionUnrestricted` | Exact, leaves underlying sheaves/maps unchanged. |
| K-flat representatives with flat terms | `integralOperationsGoodComplex`, now using the published `IsKFlatIndependentCoefficients`, and `∀ i, IsFlatOnSite (P.X i)` | Exact acyclic-total-tensor predicate, no boundedness restriction. |
| Termwise reductions P_n representing derived reductions | `unrestrictedIntegralFiniteComplex` and its scalar-extension witness | Actual sheafified scalar extension along pi_n, with prescribed objects and maps. |
| Canonical reduction transition | `unrestrictedIntegralTransition_existsUnique` on s tensor x | Exact coefficient-reduction formula, rather than an arbitrary map. |
| Rlim of a strict tower via Cone(1-s)[-1] | `integralOperationsRoos`, `towerTransitionEndomorphism`, `integralOperationsRoosFunctor` | Termwise products, shifted cone and diagonal product maps; not a categorical limit in a triangulated category. |
| Interpretation as a derived limit | `integralOperationsDerivedLimitProperty`, the final clauses of `integralOperationsWellDefined` | Exact `IsDerivedLimit` for the localized strict transitions. |
| Arbitrary morphism f:X to Y | `{X Y : Scheme.{t}} (f : X ⟶ Y)` | Exact; no finite type, flatness, separatedness, qcqs or characteristic binder. |
| Finite module inverse image | `integralOperationsLevelPullback`, `coefficientProEtaleModulePullback` and its canonical adjunction unit | Sheafified module inverse image along the constant-section coefficient map. |
| Pullback tower maps | `integralOperationsPullbackTransition_existsUnique` | Fixed on pullback unit generators by the actual reduction of P_n. |
| Lf* K = Rlim Res_n f*(P_n) | `integralDerivedPullback`, `integralDerivedPullbackComparison` | The same normalized-descent witness supplies F and its comparison on every good representative. |
| Completed tensor = Rlim Res_n Tot(P_n tensor Q_n) | `integralCompletedTensor`, `integralCompletedTensorComparison` | Same normalized-descent witness supplies G and its comparison; identity f only fills an unrelated parameter. |
| Total tensor and its transitions | `integralOperationsTensorLevel` with `map₂CochainComplex`; `integralOperationsTensorTransition_existsUnique` | Coproduct totalization, differential d_P tensor 1 + (-1)^p 1 tensor d_Q, correct reduction on every pure tensor summand. |
| Functoriality and independence | `integralOperationsWellDefined` gives F,e,G,d and unique natural isomorphisms compatible with e,d | Exact normalized uniqueness; chosen data are determined up to the equality used downstream. |
| Ambient internal Hom | `integralDerivedInternalHom`, applying `derivedInternalHomOfUniverses.{t+1,t,u}` to the completed ring | Source D(O)^op times D(O), target D(O); all module sheaves. |
| K-injective target computation and representative independence | Existing `homComplexFunctor`, canonical `kInjectiveResolutionFunctor`, `Localization.lift`, generalized `_inverts`, `_comparison`, `_obj_iso` | Exact; product Hom terms and the signed differential, with no completion applied to its output. |

Dependency modules were checked against their own nodes (H13):

- `def-pc-kflat-complex`: the current published
  `Sheaf.Algebra.Homology.KFlatIndependentCoefficients` already supplies the exact
  total-tensor acyclicity definition and quasi-isomorphism conjunction at arbitrary
  coefficient size relative to the site. I read its complete source with
  `scompile.py --source`, including the proved monoidal/zero-map infrastructure.
  Its associated `KFlatCoefficientUniverse` also supplies the proved sheafification
  interfaces. This dependency is now recorded as existing; its duplicate sandbox
  KFlat module is removed. The independent predicates are existing canonical data.
- `def-weil-integral-reduction-tower`: reuse the current canonical module's three
  `IsKFlatResolutionIndependentCoefficients` binders, matching
  `IntegralReductionTowerWellDefined`. Its inverse system is still the localized
  strict reductions; its maps are [q] inverse followed by the tensor unit, its
  naturality covers every opposite-natural arrow, and its cone packages those maps.
  Its legacy finite-field convention remains confined to that legacy interface;
  the item's unrestricted core needs no such datum.
- `lem-pur-integral-operations-well-defined`: added this already recorded dependency's
  module to the packet. It now imports and uses the published independent K-flat,
  tensor-localization and tensor-zero interfaces. I checked its entire node statement
  against its seven-step proof docstring and theorem: quasi-isomorphism invariance
  for both strict constructions, F,e,G,d, both unique-compatible-isomorphism clauses,
  and both derived-limit clauses are all retained. Its coefficient reductions,
  generator formulas, total tensor, transition maps, product/cone data and descent
  are unchanged. The only predicate change names the same total-tensor acyclicity
  condition in the required coefficient universe.
- `prop-pur-kinjective-resolutions-exist`: the generalized theorem retains
  Grothendieck abelianness, the specified generator, functorial resolution and natural
  quasi-isomorphism, K-injectivity and injectivity in every degree. The free module
  on lifted Yoneda at U is the extension of the localized rank-one unit: at V its
  free generators are arrows V to U with coefficients in O(V). Sheafification and
  the coproduct therefore give exactly the source's generator, not an arbitrary one.
- `def-pur-derived-internal-hom`: the generalized module retains all clauses of the
  node: the canonical K-injective replacement in the second variable, localization
  inverting quasi-isomorphisms, comparison with any functorial replacement, and
  computation on any source/K-injective target representatives. Its three theorem
  docstrings give the corresponding three proof steps. Only the source and ring
  sizes are generalized, to max c v r; no site-universe equality is imposed.

Mismatches found and final repairs:

1. The sandbox dependency files and records predated recent K-flat landings.
   Initially restoring the side source exposed a duplicate-declaration error:
   the current live library owns `IsKFlatIndependentCoefficients` in its separate
   published module. I read that exact module rather than treating the source/artifact
   difference as a blocker. The final repair reuses that existing module, drops the
   duplicate KFlat file, retains the current independent resolution predicates in
   IntegralReductionTower, and repairs the well-definedness consumer in this delivery.
2. The source's newly recorded exactness dependency
   `Sheaf.AlgebraicGeometry.ProEtaleConstantExact` was absent from the item's imports
   because the earlier report described it as unstated. I opened its actual theorem
   and coefficient category and added its module import. The independent coefficient
   pullback used in the construction remains the canonical constant-sheaf interface;
   no false equality with the continuous-function presentation is asserted.
3. Restored literal primary signatures in every delivered node record, including
   the tower and well-definedness records that had normalized single-line signatures.
   Current dependency metadata outside `lean` is preserved.

Edge cases: natural-number zero is exponent one, so every positive exponent and
successor transition is covered without including the exponent-zero quotient.
The tower itself is fixed, infinite and nonempty; no nonempty or finite hypothesis
is imposed on an external index set. All integral total-degree pairs are present,
including infinitely many summands. The empty scheme, zero complex, arbitrary
unbounded complexes, ell=2, E=Q_ell and schemes in characteristic ell are allowed.
For an empty site the generator is the zero coproduct in the trivial sheaf category.
Identity pullback still includes completion on ambient inputs. Site objects,
site arrows and coefficient fields retain independent universes; their maximum
contains the required sections and Hom complexes.

Independent H4 searches in this reading:

- LeanFinder via `msearch.py`: “Homotopy inverse limit of quotient module sheaves
  defining derived adic pullback and tensor functors”. Eight results, ordinary
  adic-completion tensor maps and local cohomology; no matching operation.
- Loogle via `msearch.py`: `"adic", "tensor"`. Twelve ordinary adic tensor/completion
  declarations, none on this derived category of completed-ring module sheaves.
- LeanSearch via `msearch.py`: “Derived adic tensor of ringed site module sheaves
  computed using a strict reduction tower”. Service unavailable (Internal Server
  Error); no absence verdict inferred.
- Independent `rg` searches in Mathlib, upstream WeilConjectures, and project
  lean/Sheaf for completion/tensor/derived-limit names and the five proposed names.
  I opened the upstream constant-module `derivedCompletionDiagram` and the exact
  newer pro-etale ModuleObject/Derived/Tensor and Hom modules in the shared clone,
  together with coord/pefw-upstream-framework.md. Those concern constant ModuleCat
  sheaves or condensed coefficient module objects, not the three normalized ambient
  operations on modules over this inverse-limit ring sheaf. The generic Hom complex
  and the strict reduction/descent machinery are reused. The live K-flat declarations
  found during compilation are reused instead of restated.

All four delivered modules use real definition data and named postponed theorems.
There are no new proofs, private definitions or file-local notation. Every declaration
has a source/blueprint docstring; postponed statements carry their proof plans.
The item's five definitions and natural-language statement remain unchanged.

The final packet reuses `IntegralReductionTower` as existing as well: its current
published source already has the independent resolution binders, so its stale
sandbox replacement is removed. Four modules remain: the item, the repaired
well-definedness module, the generalized K-injective theorem and generalized
internal Hom. Both existing K-flat and tower declarations receive the wrapper's
actual compiler checks during the dry run.

Validation: the final operations and dependency repairs passed the prescribed
`scompile.py` packet with no error or warning. The four final modules took
2.2 s (generalized K-injective theorem), 2.7 s (generalized internal Hom),
7.0 s (well-definedness) and 14.2 s (the item). The same successful run also
compiled the canonical tower and the unrestricted reduction/coefficient-pullback
imports, together with the newly imported exactness module. Every file used
nice 19, two threads and the default 60-second limit. Literal signature checks,
100-column checks and authorized-node-field checks passed. No global build ran.

The first dry run passed compilation and identified two report/record defects:
the well-definedness signature extractor stopped at a named-argument `:=`, and
the original Dependency modules section did not name that repaired node. The
record now contains the entire literal theorem signature through its final
conclusion, and that section explicitly names and explains the dependency repair.
No Lean statement or construction changed for these preflight repairs.
