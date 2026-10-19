## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction` states the ordinary,
unbounded coefficient-change theorem, including canonical comparison maps and the precise
adjunct identity. All postponed proofs are named theorems with proof plans. Definitions
contain actual restriction functors, mates, localization comparisons, or choices from
uniquely characterized universal properties; no arbitrary natural isomorphism is chosen.

Hypotheses and clauses:

- `U V : Scheme.{u}` and `f : U ⟶ V` give the scheme morphism; `ProEt.topology` is the original
  small site, with object universe u+1 and morphism universe u. The size convention is
  preserved through the existing `proEtaleSiteModel` interface, without identifying these
  universes.
- `RV SV` and `RU SU` are arbitrary commutative ring sheaves on the respective sites in
  `CommRingCat.{u+1}`. The module and derived categories are the dependency's
  `proEtaleRingModules` and its ordinary `DerivedCategory`, not condensed modules,
  constructible subcategories, bounded categories, or completed categories.
- `aV aU` are precisely the two ring maps. `cR cS` are the two specified inverse-image
  coefficient identifications. `comm : cR.hom ≫ aU = inverseImage.map aV ≫ cS.hom` renders
  exactly the coefficient-square condition, in Lean's diagrammatic composition order.
- `proEtaleRingRestrictScalars` is Mathlib `SheafOfModules.restrictScalars` after forgetting
  commutativity on the ring map. `proEtaleRingRestrictScalars_properties` states exactness
  and conservativity before derivation. Its finite-limit/colimit instances permit the
  actual termwise induced `mapDerivedCategory`; the final theorem asserts that each of
  the two derived restrictions reflects isomorphisms.
- The dependency's `proEtaleRingDerivedPullback` and `proEtaleRingDerivedDirectImage` give
  L_R, R_R, L_S, R_S. The supplemental operations interface specifies their canonical
  adjunctions as `proEtaleRingDerivedAdjunction`.
- `proEtaleRingRestrictionDirectImage` is uniquely characterized as identity on every
  section `N(U ×_V W)` of the underived direct images. The compatibility equation is
  used in its linearity proof. Thus its input is the specified coefficient square.
- `proEtaleRingRestrictionPullbackInv` is the ordinary mate of that identity, using the
  normalized ordinary module units and counits. Its invertibility theorem uses the
  equality of inverse-image scalar actions. `proEtaleRingRestrictionDerivedPullback`
  is its inverse descended termwise through localization, hence the stated b.
- `proEtaleRingRestrictionDerivedDirectImage` is the unique d compatible with the
  right-derived units and the ordinary identity on direct images. Its existence theorem
  explicitly gives this universal normalization on every complex; its proof plan uses
  the two equal composites of ringed-topos morphisms. On K-injective representatives
  it yields precisely the direct image of the intermediate resolution, and never assumes
  that restricted K-injectives remain K-injective.
- For every derived `M`, `N`, and `t`, the final equation applies `homEquiv` over R to
  `b.inv.app M ≫ rU.map t`; its right side is `rV.map (homEquiv over S t) ≫ d.hom.app N`.
  These are exactly the node's two adjuncts, including the directions of b and d.

Dependency declarations: `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` supplies the
small-site derived-category convention; `Sheaf.AlgebraicGeometry.ProEtaleOperations`
supplies `proEtaleRingModules`, the four ordinary/derived operations, their exactness and
K-injective resolution instances. Mathlib `Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`
supplies `SheafOfModules.restrictScalars`. The module imports each recorded proof-dependency
module, including the ringed-topos derived composition theorem and the general canonical
pre-derived adjunction theorem.

Edge cases: coefficient maps need not be flat, surjective or injective; zero rings and
zero modules are allowed. The scheme morphism can be an identity or involve an empty
scheme. The two coefficient identifications need not be identity maps. Complexes can
have cohomology in arbitrarily positive and negative degrees. No equalization of the
site object and morphism universes is imposed. The module adjunction is normalized by
pure tensor generators, so arbitrary scalar automorphisms cannot change its unit.

Searches: msearch LeanFinder, query “Restriction of scalars between sheaves of rings
commutes with derived pullback and derived pushforward compatibly with adjunction”,
returned eight underived pullback/pushforward adjunction and composition declarations;
none is the unbounded coefficient-change statement. Loogle query
`SheafOfModules.restrictScalars, Adjunction` returned zero hits (unknown identifier
Adjunction). msearch grep `restrictScalars.*[Dd]erived|[Dd]erived.*restrictScalars` in
`Algebra/Category/ModuleCat` returned zero hits. LeanSearch for restriction of ring-sheaf
scalars commuting with derived inverse/direct image was unavailable (Internal Server
Error); no mathematical verdict is inferred from that failure. Source-tree and side-library
rg searches found constant-coefficient restriction in `TraceFormula.Adic`, etale integral
coefficients, and several ring-module comparisons, but no arbitrary ring-sheaf comparison
on the small pro-etale site. The item-id search found no upstream implementation.

The Stacks source was read at sites-cohomology.tex, lemma-derived-pullback-composition,
lemma-adjoint and lemma-derived-pushforward-composition. These use ordinary unbounded
module derived categories and their canonical composite adjunctions, as does the delivery.
No statement correction or dispute is required.

## Dependency modules

`def-weil-pbc-proetale-operations`: the recorded module gives only existence of ordinary
and derived adjunctions as `Nonempty`. An arbitrary adjunction would allow twisting the
unit and would not state the requested canonical mate equality. The supplement
`Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction` imports those exact
operations, then states uniqueness of the ordinary adjunction whose transpose is computed
by first evaluating on the sheafified pure tensor `1 ⊗ m`, then taking the existing
small-model pullback adjunct. This fixes the Hom equivalence section by section and thus
the adjunction. Its uniquely specified choice gives `proEtaleRingModuleAdjunction`;
Mathlib/upstream `Adjunction.mapDerivedCategoryRightDerivedAdjunction` induces
`proEtaleRingDerivedAdjunction`. Only the node's lean record changes. Its original
operations remain available through the supplement's public import.

Validation: scompile.py compiled each delivered module separately in dependency order,
including the library-path check, with no errors or warnings. The canonical-adjunction
supplement took 4.6 seconds and the coefficient-change module took 9.8 seconds in the final
local overlay pass. No global build was run. The delivery dry run is required before READY;
the independent second reading is reserved for the next worker.

## Second reading by NA

Independent reading of the node, both delivered modules, the recorded dependency
signatures, and the cited Stacks passages found no mathematical mismatch. No Lean
statement or node field needed changing. This reading adds only this report section.

Object/hypothesis/conclusion checklist (each verdict: matches):

1. A scheme morphism u:U→V: `{U V : Scheme.{u}} (f : U ⟶ V)`.
   `ProEt.topology` is the original small pro-etale site, not the etale site or a
   condensed coefficient category. I opened `ProEtaleDerivedCategory` and
   `ProEtaleInverseImage`; the model `AsSmall.{u+1} X.ProEt` enlarges Hom size
   for the module pullback API and transports back to the original site.
2. Four arbitrary commutative ring sheaves: `RV SV` on V and `RU SU` on U,
   all `Sheaf (ProEt.topology ...) CommRingCat.{u+1}`. This follows the recorded
   site's size convention: schemes in u, sites with object size u+1/Hom size u,
   and coefficients/modules in u+1. There is no assumption of constant coefficients.
3. Two coefficient maps: `(aV : RV ⟶ SV) (aU : RU ⟶ SU)`.
   No flatness, injectivity, surjectivity, nonzero-ring, or finiteness binder occurs.
4. Specified inverse-image identifications: `cR` and `cS` are isomorphisms from
   the existing `proEtaleSheafInverseImage f CommRingCat.{u+1}` to RU and SU.
5. Compatibility: `comm : cR.hom ≫ aU = inverseImage.map aV ≫ cS.hom`.
   In diagrammatic composition order this is precisely a_U c_R = c_S u⁻¹(a_V).
6. Ordinary unbounded module derived categories and operations: I opened
   `ProEtaleOperations`. `proEtaleRingModules` abbreviates the existing general
   `ringedSiteModules`/`SheafOfModules`, `proEtaleRingDerivedPullback` is exact
   `mapDerivedCategory`, and `proEtaleRingDerivedDirectImage` is the ordinary
   `rightDerivedFunctor`. The category uses `HasDerivedCategory.standard`.
   No boundedness, completion, constructibility, or K-flatness hypothesis is added.
7. Exact termwise restriction r_T: `proEtaleRingRestrictScalars` is only an
   abbreviation for the recorded Mathlib `SheafOfModules.restrictScalars`, after
   applying the forgetful ring-sheaf functor to a_T. I read that Mathlib definition:
   its underlying sheaf is unchanged, and its maps are restricted linear maps.
   `proEtaleRingRestrictScalars_properties` supplies finite-limit/colimit preservation
   and underived conservativity; the two instances expose exactly those properties.
   The final theorem's first two conjuncts assert derived conservativity at U and V.
8. Canonical b:r_U L_S≅L_R r_V: the functor-composition order in
   `proEtaleRingRestrictionDerivedPullback` has exactly these endpoints.
   Its inverse is induced by `proEtaleRingRestrictionPullbackApp`, the explicit
   unit/counit mate of the sectionwise direct-image identity. The coefficient-square
   action calculation makes that mate invertible before termwise localization.
9. Canonical d:r_V R_S≅R_R r_U: `proEtaleRingRestrictionDirectImage_existsUnique`
   requires the ordinary comparison to act identically on every section of every N.
   `proEtaleRingRestrictionDerivedDirectImage_existsUnique` fixes the derived map by
   its equation with the ordinary comparison and the canonical right-derived units
   on every complex. This is the normalized comparison for the equal ringed-topos
   composites, not a bare choice of an isomorphism. Its proof description uses
   directImage(j) for the further RU K-injective resolution; it does not assume that
   scalar restriction preserves K-injectivity.
10. Adjunction compatibility for every M,N,t: the final theorem quantifies
    `M : DerivedCategory (proEtaleRingModules V SV)`,
    `N : DerivedCategory (proEtaleRingModules U SU)`, and `t : L_S.obj M ⟶ N`.
    Its left side is the R `homEquiv` of `b.inv.app M ≫ rU.map t`; its right side
    is `rV.map (S.homEquiv M N t) ≫ d.hom.app N`. Thus the adjuncts, comparison
    directions, and quantifier order are exactly the node's last clause.

Dependency-module review (H13): the existing operations node specifies the actual
module actions and their canonical adjunction. Its old Lean file provided only
`Nonempty` ordinary/derived adjunctions, inadequate to fix a mate. The supplement
imports that file without replacing its categories or functors. I checked its
`proEtaleRingModuleAdjunction_existsUnique` formula against the original small-model
pullback and `proEtaleModelRingUnit` declarations: g is h precomposed with the
sheafification of m↦1⊗m, transported to the model, and the transpose is Mathlib's
`SheafOfModules.pullbackPushforwardAdjunction` transpose evaluated on original
sections. This fixes the Hom equivalence, so the selected adjunction is uniquely
determined. I also opened upstream `RightDerivedFunctor.Adjunction`: its
`mapDerivedCategoryRightDerivedAdjunction` derives that very adjunction using the
exact left adjoint and the canonical right-derived unit. The dependency repair is
therefore faithful to its node and needed for clause 10; no private copied notion
or additional hypothesis is introduced. There are no new definition nodes.

Source review: sites-modules.tex, `lemma-adjoint-push-pull-modules`, uses arbitrary
sites, a topos morphism, a ring sheaf and module sheaves, and restricts the abelian
adjunction to linear maps. sites-cohomology.tex lines 3657–3680, 3989–4007 and
4010–4030 state derived pullback composition, the unbounded derived adjunction,
and derived pushforward composition for arbitrary ringed-topos morphisms. Their
proofs use K-flat representatives and uniqueness of adjoints, with no properness,
Noetherian, torsion, or boundedness assumption. The identified-coefficient
specialization and compatible ring square in this node supply exactly the data
used in the two modules. No statement correction or citer audit is necessary.

Edge cases: identity f and nonidentity coefficient identifications are admitted;
either scheme may be empty when a morphism exists. Zero coefficient rings and
zero modules are admitted. Both coefficient maps may be nonflat; no flatness is
needed because cR/cS are isomorphisms. All integer cochain degrees, including zero
and arbitrarily negative degrees, occur. There is no index set, characteristic,
or nonemptiness restriction. No independent universe equality or assumption
identifying the original site's object and Hom universes appears. All variables
and the universe u are explicitly bound.

Independent searches: msearch LeanFinder query "Natural base change isomorphism for
restriction of ring sheaf scalars and derived pushforward adjunction" returned eight
underived results, including `SheafOfModules.pushforwardCongr`,
`pushforwardNatIso`, and pullback Hom-equivalence lemmas. None gives the arbitrary
ring-sheaf unbounded comparison with its adjunct identity. Loogle query
`"restrictScalars", "pushforward"` returned zero hits. I also searched Mathlib's
module-category tree, the upstream `WeilConjectures` tree, and project `lean/Sheaf`
with `restrictScalars.*(derived|adjunction)`, `derived.*restrictScalars`, and
`restriction.*(coefficient|scalar)`. Existing hits concern constant-ring sheaves,
finite/completed coefficients, ordinary algebraic restriction, or individual tensor
comparisons. They do not state this theorem. I used the existing Mathlib restriction
and existing upstream derived-adjunction construction rather than replacing them.
The worker's LeanSearch service failure is recorded above and is not a claimed
negative search result.

H5/H6/H8/H9 checks: definitions contain actual functors, mates and localization maps,
or choices from uniquely normalized universal properties. Every postponed theorem
has a source/blueprint docstring and natural-language proof, covering the node's
five proof steps across the helper statements and the final theorem. Every theorem
proof remains `sorry`; no theorem was proved in this delivery. Both modules use
public exported names, explicit universes and lines at most 100 characters.
