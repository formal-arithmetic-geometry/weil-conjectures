## Worker report

Item: lem-sfb-identity-open-derived-restriction. Module:
`Sheaf.Paper.IdentityOpenDerivedRestriction`. Namespace:
`AlgebraicGeometry.ProEtale.CondensedRing`.

The module constructs the canonical underived and derived common-open restriction
maps, and states their invertibility, their sectionwise and K-injective
normalizations, transitivity, and identity normalization. The three theorems have
exactly `by sorry` proofs. The three helper definitions have real data: existing
adjunction mates, existing identity comparisons, and an explicit fibre-product
lift. There is no chosen arbitrary isomorphism or unspecified map.

The TeX statement and Lean module are unchanged. The returned delivery's H2
fault is repaired: its added theorem dependency
`lem-sfb-derived-direct-image-open-coherence` is removed and replaced by the
new definition node `def-sfb-open-square-restriction-mates`. That node has an
`existing: true` record on the unchanged Q13 module
`Sheaf.Paper.DerivedDirectImageOpenCoherence`, listing the five plain definitions
for the underived and derived pullback comparisons, their restriction mates,
and the section coprojection. No definitions are copied and Q13's module is not
edited. The restricted rational finite-type theorem is not assumed. The
original dependency `lem-sfb-module-derived-compositor-coherence` remains the
source of `moduleDerivedCompositor` and `moduleDerivedIdentity`. No statement
correction or dependency-module repair is needed.

Hypothesis and clause correspondence:

- The prime and admissible commutative condensed coefficient ring are
  `(ℓ : ℕ) [Fact ℓ.Prime]`, the explicit condensed abelian sheaf `Λ`,
  `[MonObj Λ] [IsCommMonObj Λ]`, and
  `hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ`. This uses the recorded
  coefficient predicate unchanged, including both existing algebraic-closure
  conventions; no finite-subextension hypothesis is substituted for the
  continuous-map algebraic-closure case.
- Schemes and size: `universe u`, `U Z Z' Z'' : Scheme.{u}`, small sites
  `Scheme.ProEt.topology T`, and `AddCommGrpCat.{u + 1}`. These are the
  published framework universes implementing def-weil-size-convention.
- The actual pulled-back coefficient ring is `condensedRingObj Λ T`, i.e.
  the underlying ring object of `coefficientRing T (Mon.mk Λ)`.
  Modules are Mathlib's `Mod (Sheaf ...) (condensedRingObj Λ T)`.
- `D_T` is the ordinary Mathlib `DerivedCategory` of precisely those modules.
  `Rh_*` is `(lowerStar Λ h).rightDerivedFunctor`; open restriction `j^*`
  is `(upperStar Λ j).mapDerivedCategory`, the levelwise exact module
  pullback. No bounded, constructible, completed, or localizing subcategory
  replaces this derived category.
- `j,j'` are explicit morphisms from the same `U`, with
  `[IsOpenImmersion j] [QuasiCompact j]` and the corresponding two
  instances for `j'`. Quasi-compactness uses the recorded Mathlib class,
  not a finite-type or separatedness assumption on either scheme.
- `h : Z' ⟶ Z` and `w : j' ≫ h = j` express `hj'=j` in Lean's
  diagrammatic composition order.
- `hw : h ⁻¹' Set.range j = Set.range j'` expresses equality of the
  inverse-image open and the source open. Both maps are open immersions,
  so equality of these open subsets is precisely equality of the open
  subschemes with their restricted structure sheaves. This does not
  demand equality of unrelated chosen presentations of an open scheme.
- `identityOpenRestriction Λ j j' h w` is the already defined
  `directImageOpenRestriction` for `CommSq j' (𝟙 U) h j`, followed by
  `lowerStarId` and the functor right unitor.
- `identityOpenDerivedRestriction` is the corresponding existing derived
  mate followed by `moduleDerivedIdentity Λ U` and the right unitor.
  Its type is `Rh_* ⋙ D(j^*) ⟶ D(j'^*)`, exactly `j^*Rh_* → j'^*`.
  The first conjunct of `identity_open_derived_restriction` says this
  specified map is an isomorphism (`IsIso`), hence supplies the claimed
  canonical natural isomorphism via `asIso`. The second conjunct also
  states invertibility of its underived counterpart.
- `identityOpenSectionArrow` constructs the arrow from `V` over `Z'` to
  the base change of `V` over `Z`. Its projections are `𝟙 V.left` and
  `V.hom ≫ j'`, literally the inverse `(1_V,j'v)` of the fibre-product
  identification in the node. The next conjunct states this arrow is
  an isomorphism for every `V : U.ProEt`.
- The section formula quantifies over every module `M`, every site
  object `V`, and every section `s` on that fibre product. The left side
  applies the canonical common-open comparison, using
  `openCoherenceSectionCoprojection` to identify open pullback sections.
  The right side restricts `s` along `identityOpenSectionArrow` and
  makes the same canonical identification for `j'`. This says the map
  is identity on sections after identifying the fibre product with `V`.
  In particular it applies to each term of any K-injective complex.
- The final conjunct quantifies over every unbounded cochain complex `I`
  with `[I.IsKInjective]`. It identifies the component at `Q.obj I` with
  `Q.map` of the termwise `identityOpenRestriction`, inserting
  `rightDerivedFunctorObjQIso` and `mapDerivedCategoryFactors`. This is
  the exact representative normalization, rather than existence of an
  unnormalized natural isomorphism.
- Every map is a morphism of the actual module objects. The imported
  `lowerStar`, `upperStar`, open-square mates and identity comparisons
  already retain extension/restriction along the canonical coefficient
  morphisms. Thus the section formula does not forget the coefficient
  action or replace it with an arbitrary action.
- `identity_open_derived_restriction_comp` binds the third common-open
  embedding `j''`, an arbitrary `k : Z'' ⟶ Z'`, and precisely the same
  commutativity and inverse-image conditions for `k`. No quasi-compactness
  assumption on `j''` is added. Its left side is `r_{hk}`; the supplied
  equality witness is obtained by associativity from `w'` and `w`.
  Its right side first applies `D(j^*)` to the recorded
  `moduleDerivedCompositor Λ k h`, then the explicit functor
  associator, then `Rk_*` whiskered with `r_h`, then `r_k`.
  This is exactly the displayed equation in the node, as an equality
  of natural transformations on the whole unbounded category.
- `identity_open_derived_restriction_id` sets `h = 𝟙 Z` and `j'=j`,
  and says the comparison is the whiskering of the recorded
  `moduleDerivedIdentity Λ Z`, followed by the left unitor. For a
  separately named `j'` the relation `j' ≫ 𝟙 Z = j` identifies it
  with `j`, so this includes that presentation of the identity case.
- No theorem binds properness, density, a field of definition,
  Noetherian hypotheses, separatedness, or finite type of the schemes.

Dependency interfaces read and used:

- `Sheaf.Paper.LocalizingAdmissibleCoefficients`:
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, the canonical coefficient morphisms.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `Functor.rightDerivedFunctorOfQuasiIsoResolutions` and its normalized
  universal total-derived interface. The actual Grothendieck module
  categories use the upstream `Functor.rightDerivedFunctor`, exactly as
  the dependency's note specifies.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `lowerStar`, `upperStar`, `upperStarLowerStarAdjunction`, exactness,
  and `lowerStarComp`; the companion `Coherence` module supplies
  `lowerStarId` and equality transports.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`,
  imported through the recorded FiniteType module. The latter also
  records `LocallyOfFiniteType`, which is not an additional assumption here.
- `Sheaf.Paper.ModuleDerivedCompositorCoherence`:
  `moduleDerivedCompositor`, `moduleDerivedIdentity`, and their
  K-injective, composition and identity normalizations.
- New definition dependency `def-sfb-open-square-restriction-mates`, existing
  module `Sheaf.Paper.DerivedDirectImageOpenCoherence`:
  `openCoherencePullbackSquare`, `directImageOpenRestriction`,
  `derivedOpenCoherencePullbackSquare`, `derivedDirectImageOpenRestriction`,
  `openCoherenceSectionCoprojection`. These five plain constructions have no
  finite-type or coefficient-admissibility assumptions. The module import
  remains unchanged; the DAG now cites their definition node.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`:
  `rightDerivedFunctorObjQIso`; Mathlib's exact-derived functor interface:
  `mapDerivedCategoryFactors` and termwise maps of natural transformations.

All stated proof dependencies are imported, including localized ringed sites,
finite sheaf direct image, coefficient-sections localization, exact module
pullback, internal/sectionwise module transport, weakly-etale localization,
K-injective resolutions, the K-injective Hom bijection, the exact-left-adjoint
preservation criterion, and `CondensedModuleDerivedPushpull`. The theorem
docstrings give the six node proof steps and identify the dependencies used.

Sources checked: the node's six proof steps; Stacks `sites-cohomology.tex`,
`lemma-restrict-direct-image-open` (0D6G) and
`lemma-derived-pushforward-composition` (0D6E), including the adjacent
base-change mate construction; the main-20261015 blueprint's
`det-sf-comp-coherence-cocycle.proof.md`, Refinement isomorphisms and
Independence. The unit and source require no correction.

Edge cases checked: empty common open (all section comparisons are the unique
ones on the empty site objects), identity maps and identity open embeddings,
zero modules and complexes, and arbitrary unbounded K-injectives. The
inverse-image condition is essential: the fold `U ⊔ U → U` fails it and
would give two copies rather than the required identity restriction. The
conditions are stable under composing `k` and `h`. The third open's
quasi-compactness is not imposed as an extra hypothesis. No nonempty,
nonzero, positive-dimensional, field, or boundedness condition is used.

Searches (2026-10-21, via the prescribed msearch wrapper):

- LeanFinder: "Derived direct image restricted to an open subscheme where
  a scheme morphism is identity, canonical restriction isomorphism and
  composition coherence". Eight results on `morphismRestrictRestrict`,
  affine open restriction and structure-sheaf identities; no unbounded
  internal-module common-open theorem.
- Loogle: `AlgebraicGeometry.Scheme.Modules.restrictFunctor, CategoryTheory.Iso`.
  Eight results: `restrictFunctorIsoPullback`, `restrictFunctorId`,
  `restrictFunctorAdjCounitIso`, `restrictFunctorCongr`,
  `restrictFunctorComp`, `restrictStalkNatIso`, `overFunctorEquiv`,
  `overMapCompOverEquiv`. These concern underived Zariski modules.
- Mathlib grep: `restrict.*[Pp]ushforward|[Ii]dentity.*[Oo]pen|[Oo]pen.*[Bb]ase[Cc]hange`
  in AlgebraicGeometry. Six hits: open immersion stability under base
  change and underived Zariski module restriction; no exact match.
- LeanSearch: "unbounded derived direct image restriction to identity
  open subscheme". Eight results on `morphismRestrict_id` and underived
  restriction/structure-sheaf identity formulas; no exact match.
- `rg` of the project and upstream pro-etale framework for identity-open,
  open-restriction, pushforward/pullback and base-change names found
  `DerivedDirectImageOpenCoherence` and `ModuleDerivedCompositorCoherence`.
  Their source signatures and docstrings were read. We reuse their
  generic maps and normalized compositor rather than duplicate them;
  neither states this node on arbitrary schemes/admissible coefficients.
- `rg` of Mathlib, upstream and Sheaf for the proposed declaration names
  found no existing names; `rg` for the item id in upstream found none.

No STATEMENT-DISPUTED flag or statement correction. Initial compilation
reported only the defProp style warning on an auxiliary square; that helper
was removed and the existing `CommSq` constructor is used directly.

## Second reading by N9

This is the dispatcher's single worker's second pass, not a claim of an
independent second worker review. The brief assigns the independent review
to the maintainer and prohibits starting other agents.

I reread the node and the final module together. The coefficient and site
universes match the recorded framework. The main theorem keeps both open
immersions quasi-compact and retains both substantive hypotheses on `h`.
The fibre-product arrow has the specified two projections, and the section
equation uses this arrow in the contravariant direction. The K-injective
formula has source `D(j^*) Rh_* QI` and target `Q(j'^* I)` on both sides.
In the composition formula the derived compositor is in its recorded
inverse-underived direction, and the associator and whiskering order is
`j^* κ`, then `r_h Rk_*`, then `r_k`. The identity formula uses exactly
`moduleDerivedIdentity`. No assumption from the rational finite-type
main theorem in the reused helper module is imported into these statements.
The rereading removed the unnecessary explicit quasi-compactness assumption
on `j''`; the identity comparison of a separately named `j'` is explained
above. No semantic mismatch or unresolved node fault remains.


## New nodes

`def-sfb-open-square-restriction-mates` records the five existing definitions
in `Sheaf.Paper.DerivedDirectImageOpenCoherence`: the canonical comparison
`openCoherencePullbackSquare`, its exact-derived comparison
`derivedOpenCoherencePullbackSquare`, their adjunction mates
`directImageOpenRestriction` and `derivedDirectImageOpenRestriction`, and
`openCoherenceSectionCoprojection`. Source: Stacks 09A5 (pro-etale
functoriality) and 0D6G (restriction of direct image to an open). The first
four use an arbitrary commutative square and arbitrary commutative condensed
coefficients; the last additionally binds an open immersion, a module and a
site object, and is the displayed adjunction unit followed by site restriction.
The new node asserts no theorem about their invertibility. Its `existing: true`
record lists exactly those five declarations on Q13's unchanged module; no new
Lean file is needed. The theorem node that happened to export these definitions
states a restricted rational finite-type theorem and does not provide their
generic defining notion as a DAG statement dependency.

Fresh searches for this node: LeanSearch query "canonical base change mate for
module sheaves in a commutative square and open restriction section coprojection"
returned eight underived Zariski-module or generic sheaf-adjunction results.
LeanFinder query "underived and derived base change restriction mates for module
objects on small pro etale sites" returned eight Zariski pseudofunctor or scalar
change results. Mathlib grep `openCoherence|directImageOpenRestriction|derivedDirectImageOpenRestriction`
returned no hits. Project/upstream `rg` found all five definitions only in
`DerivedDirectImageOpenCoherence.lean:69-131` and no upstream definitions. DAG
search of those declaration names found only the restricted theorem node;
`tools/blueprint_refs.py search "open restriction"` found six blueprint nodes,
none defining these generic module-object constructions. Full search results
are preserved in the new node's `mathlib_searches`; the live module was checked
with `scompile.py --source`. The ancestor tool confirms
`det-sf-comp-coherence-cocycle`, with via beginning at this item.

Repair self-check by N9: read the new node against all five existing definitions
and their real data. The directions are `j^* f'^* → f^* i^*`, with mate
`j^* f_* → f'_* i^*`, and the exact-derived counterpart uses the same direction.
The section coprojection's two operations match the existing definition in
order, including the contravariant site map. Empty sites, identity maps, zero
modules and arbitrary unbounded derived objects are covered. The new node's
coefficient ring is arbitrary, so it covers every admissible coefficient case
of this item. There are no finite-type or field binders. Compared the saved
packet with the current base: the item changes only `lean` and the authorized
addition of this new definition node to `stmt_deps`; all of the item's source,
statement, proof and proof dependencies remain unchanged. The saved Lean module
is retained verbatim. The required independent maintainer review remains separate.
