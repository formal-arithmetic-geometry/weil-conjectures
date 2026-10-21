## Worker report

Item: lem-weil-pbc-flat-common-quotient-reduction-tower. The delivery states
`SheafOfModules.CommonQuotientReduction.nonempty_comparison` with `sorry` and
supplies a real-data definition of the common-quotient tower presentation.
There are no proved theorems and no data definitions containing sorry. The only
postponed theorem belongs to the item and its docstring contains all six proof steps.
No statement correction or disputed statement is needed.

Sources read: proetale.tex, Tag 099L, section-derived-completion-noetherian
(the opening flatness/common-quotient assertion and the finite-reduction formula);
sites-cohomology.tex, Tags 06YS (lemma-K-flat-resolution), 06YT
(lemma-derived-tor-quasi-isomorphism-other-side), 06YY (lemma-derived-base-change).
The node itself supplies the general common-quotient calculation from 03EK and its
strict normalization, rather than attributing that whole general statement to 099L.
The Stacks tag-to-label entries were checked locally.

Hypotheses and setup:

- A small site is `C : Type u`, `Category.{v} C`, `J : GrothendieckTopology C`,
  with `EssentiallySmall.{r} C` and the recorded module-sheafification instances.
  Object and Hom universes are independent; the coefficient universe is `r`.
  The derived Hom universes `wR`, `wB`, `wS` remain independent as well.
- The commutative ring sheaves and map are `R B : Sheaf J CommRingCat.{r}`,
  `φ : R ⟶ B`. `hflat` is exactly `IsFlatOnSite` of the regular B-module
  restricted along φ, i.e. B is flat over R in the recorded sheaf-tensor sense.
- The descending ideals and their stipulated quotient identifications are encoded
  by `D : CommonQuotientTowerPresentation φ`. `D.S` is the actual tower of
  common quotient ring sheaves; `D.q`, `D.b` are the quotient projections, including
  their naturality in all tower arrows. `D.q_surjective` is local surjectivity,
  not surjectivity of sections or the weaker categorical ring epimorphism condition.
- The ideal at U is exactly `D.ideal n U = RingHom.ker (q_n(U))`. These are ideal
  subsheaves because q_n is a sheaf morphism; membership is local since vanishing
  in a sheaf is local. Naturality of q makes these ideals descending.
- `D.pushout n : IsPushout φ q_n b_n (𝟙 S_n)` specifies B/I_n B, with the induced
  identification with S_n. It is equivalent to the stated common-quotient hypothesis:
  the pushout of the quotient projection R→R/I along φ is B/I B, since maps out of
  it are exactly ring-sheaf maps killing the image of I. Conversely, the quotient
  isomorphisms in the informal statement give precisely this pushout square.
  This introduces no extra flatness, finite-generation or section-lifting assumption.
  Starting with any descending ideal sheaves and their quotient identifications gives
  D by their actual sheaf quotients; starting with D recovers those ideals as kernels.
- The index zero in Lean denotes the paper's first quotient; there is no additional
  level with a separately prescribed I_0. All transitions are retained.
- `a n`, `b n` are arbitrary presentations of the EXISTING universal derived
  change-of-rings models for q_n and b_n. Their ordinary objects and maps are fixed
  by the models' `obj_eq`/`map_eq`, and the derived functor and counit by `universal`.
  They are presentations of already existent canonical constructions, not new
  arbitrary scalar-extension functors or additional mathematical hypotheses.

Conclusions, field by field in `Comparison`:

- `res`, `resFactors` specify derived restriction as the localization of the actual
  termwise `SheafOfModules.restrictScalars`. The factorization is a natural isomorphism
  `Q_B ⋙ res ≅ restrictionComplex ⋙ Q_R`, so res cannot be an unconstrained functor.
- `ordinary n` is an S_n-linear natural isomorphism on complexes from termwise scalar
  extension of Res P over R to termwise extension of P over B. It uses exactly
  `(a n).E.mapHomologicalComplex` and `(b n).E.mapHomologicalComplex`. Its naturality
  includes each B-linear chain map and hence the termwise differential comparisons.
- `ordinary_sections` fixes each degree component on actual pure sections:
  `s ⊗ p ↦ s ⊗ p`. `scalarSection` is the sheafification-unit image of the balanced
  tensor in `changeOfRingsPresheaf`, transported only by the model's `obj_eq`.
  The library puts the scalar first; this is the paper's `p ⊗ s` after symmetry.
  No second tensor or scalar-extension object is defined. The inverse formula follows
  from this equality and the inverse law, so no inverse normalization is lost.
- `derived n : res ⋙ (a n).T ≅ (b n).T` states the S_n-linear isomorphism
  Res M tensor_R^L S_n ≅ M tensor_B^L S_n, naturally in ALL morphisms of D(B).
- `computes` ties this isomorphism to the ordinary comparison using the two existing
  universal counits and `resFactors`, for every flat-term K-flat P. This explicitly
  states canonicity and resolution independence, instead of asserting only an
  uncharacterized Nonempty natural isomorphism.
- `representatives` gives, for every M, one cochain complex P, its recorded
  `IsKFlatIndependentCoefficients`, flatness of every B-term via `IsFlatOnSite`, and
  an isomorphism Q_B(P)≅M. P is chosen before all n and used at every level.
- `strict` quantifies over every such P. `leftLevel` and `rightLevel` are precisely
  the two scalar extensions, subsequently restricted to R through the SAME q_n.
  The maps tL and tR assemble into actual functors `Functor.ofOpSequence` to the
  category of R-module cochain complexes, as required by def-weil-inverse-system.
- The tower isomorphism e has degree-level components equal to the restriction of
  `ordinary n`; its naturality therefore asserts ALL strict transition squares.
  The following two conjuncts fix both adjacent transitions as
  `s ⊗ p ↦ t_n(s) ⊗ p` using `D.S.map`. Thus no arbitrary transition is substituted.
- ηL and ηR are natural transformations from the constant tower on Res P. Their
  component equations fix both quotient cones by `p ↦ 1 ⊗ p`. The equation
  `ηL ≫ e.hom = ηR` asserts equality of strict cones before localization.
- The final two conjuncts assert that every degree component of ηL is an epimorphism
  and that its kernel is exactly local I_n P. `D.locallyInIdealProduct` uses a covering
  sieve and the submodule spanned by products `j • p`, rather than a sectionwise
  quotient. In the abelian module category this says precisely that the left tensor
  is P/I_n P with its canonical quotient map. The tower iso and cone equation give
  the SAME identification for the right tensor, so both use that identical quotient.

Dependency declarations read and used:

- Sheaf.CategoryTheory.RingedSiteModules: `CategoryTheory.ringedSiteModules` is the
  transparent recorded alias of Mathlib `SheafOfModules`. `Modules` abbreviates it.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`,
  `HasDerivedCategory`, and its localization functor `DerivedCategory.Q`.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses: the existing
  `SheafOfModules.cochainModulesMonoidal` and independent-universe tensor API.
- WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct (publicly imported):
  `changeOfRingsPresheaf`, `changeOfRings`, `changeOfRingsHom`. Their full sectionwise
  signatures were read; the existing derived model fixes exactly those objects/maps.
- Mathlib.Algebra.Homology.BifunctorShift: recorded `CochainComplex.mapBifunctor`;
  K-flatness imports its total tensor rather than defining another total complex.
- Sheaf.Algebra.Homology.KFlatIndependentCoefficients:
  `CochainComplex.IsKFlatIndependentCoefficients`, including its actual acyclic-total-
  tensor definition with independent coefficient universe.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite: `IsFlatOnSite`, whose defining
  condition is `exactFunctor _ _ (siteSheafTensorRight F)`.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings: `restrictScalars` and its
  additive instance, read with the underlying sectionwise action.
- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel:
  `DerivedChangeOfRingsCochainModel`, `nonempty_derivedChangeOfRingsCochainModel`;
  all ordinary object/map, universal derived, and K-flat counit fields were read.
- Sheaf.Paper.RingedTopoiTensorSections: `RingedTensor.pure`, `tensorFunctor`,
  `tensorAdjunction`, `tensorUnit`, the sheafification section calculus. Its displayed
  pure_R is a same-ring tensor. The cross-ring generator here is the actual unit of
  the same module sheafification in changeOfRings, with independent site universes;
  `scalarSection` simply transports this existing section to the given model.
- Mathlib.CategoryTheory.Functor.OfSequence: `Functor.ofOpSequence` and
  `NatTrans.ofOpSequence`; strict towers here are functors and morphisms are natural
  transformations, not merely towers in the derived category.
- Proof-only imports: Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
  (`CochainComplex.exists_isKFlatResolutionIndependentCoefficients`) and
  WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
  (`Functor.leftDerived_from_resolvingClass`). Their conclusions supply the resolving
  class and descent used in the proof docstring. The proof dependency
  lem-weil-pbc-flat-scalar-restriction-kflat currently has no recorded module, so no
  nonexistent import is inserted. No declaration of it is needed to state this item.
- Presheaf module sheafification is the recorded Mathlib
  `PresheafOfModules.sheafification` and its adjunction, publicly available through the
  actual change-of-rings construction, not a private copy.

Edge cases checked before drafting and again against the specification: I_n=0
(the common quotient forces φ to be an isomorphism), I_n=R (zero quotient rings and
zero tensor levels), constant/repeated ideals, the zero complex, unbounded complexes,
and the empty site. No nonempty site, nonzero quotient, boundedness, enough points,
Noetherian or finite-generation assumption was added. Adjacent quotient maps need not
be surjective on sections. Explicit universes permit a site with different object
and morphism universes and independent localization sizes. All binders are explicit
under `set_option autoImplicit false`.

Searches performed:

- msearch leanfinder: "For a flat morphism of commutative ring sheaves with common
  quotient rings, derived reduction gives naturally isomorphic strict towers compatible
  with quotient units". Eight results about ordinary ring-map flatness and scheme
  flatness; no sheaf-module derived tower comparison.
- msearch loogle: "SheafOfModules.restrictScalars, SheafOfModules.changeOfRings".
  Zero hits, with changeOfRings unknown to the Mathlib-only index; the actual upstream
  declaration was found and read directly, so this is not treated as nonexistence.
- msearch grep: "common.?[Qq]uotient|[Tt]ensor.*[Qq]uotient". Twenty-five hits, about
  ordinary module/ring tensor quotients; none gives the general sheaf tower theorem.
- The three additional exact queries and raw results for the new presentation node
  are stored in its mathlib_searches: LeanSearch (eight general pushout results),
  LeanFinder (eight module-presentation results), grep (zero common-quotient records).
- Direct rg over lean/WeilConjectures and lean/Sheaf for common quotient found only
  unrelated chart/valuation references. Search by this item's full id in
  lean/WeilConjectures found no attachment. Broader quotient/tower searches found
  ConstantCompletionEquivalence and IntegralTensorReductionTowerComparison, but
  those concern constant Noetherian/adically completed coefficients, or geometric
  integral operations; neither states this arbitrary ring-sheaf/ideal-tower result.
- DAG search plus tools/blueprint_refs.py search 'common quotient' (zero blueprint
  matches); tools/blueprint_refs.py ancestor returns def-weil-pbc-completed-pullback.
  The existing geometric ringed-common-quotient-pullback-comparison was read: it has
  two sites and ringed pullbacks and no recorded Lean declaration. It is not this
  node's general coefficient-restriction statement.
- The existing def-weil-pbc-ringed-site-ideal and its RingedSiteIdeal source were read.
  It gives individual ideals, their extensions and a local quotient-isomorphism
  predicate, with no chosen quotient projections or strict ring tower. This delivery
  defines no alternative ideal-subsheaf structure: `ideal` is simply RingHom.ker
  evaluated on the supplied projection. The new datum packages the quotient tower
  missing from that interface. Existing Scheme.idealModuleProduct is scheme-specific.

Validation: both modules compiled separately in dependency order through scompile.py,
including their actual library module names, with no errors or warnings (about 2 s
for the presentation and 16 s for the comparison). Explicit object families were
supplied to Functor.ofOpSequence after elaboration initially left its family unsolved.
No local builds, live edits, direct Git commands or tool modifications were used.

## New nodes

`def-weil-pbc-common-quotient-tower-presentation` supplies the missing quotient-tower
input, its canonical kernel-ideal evaluation and local ideal-product membership.
It contains only real-data definitions, uses the existing module category and inverse-
system definition nodes, and cites the exact 099L/03EK source places. The searches
above found the existing individual ideal notion but no presentation giving the
common quotient ring objects, quotient maps and all transitions needed here. Its
blueprint ancestor and via path come from the existing item's ancestor record.

## Second reading by Q27

Author's second pass, with the node, source extracts and both modules open; this is
not a claim of independent review. The maintainer performs that review under the
dispatcher brief. I checked every hypothesis and clause using the mapping above.
In particular I checked the orientation of the pushout square, the two derived
counits in computes, and the direction of each tower and cone map. I also checked
that the kernel clause uses local ideal-product membership and that e has the
actual restricted ordinary comparison as its component. The quotient presentation
uses universal properties of the specified quotient maps and does not assume a
sectionwise-surjective projection. The ordinary scalar convention is s tensor p;
all transition, cone and comparison formulas use that same convention. The inverse
comparison follows from its isomorphism and forward generator formula. There are
no weakened conclusions, hypotheses about arbitrary replacement maps, or silent
source corrections. After the successful compile I added the public import and
transparent recorded module-category alias in the definition module so its listed
module-category dependency is used directly; the delivery checks recompile this.
