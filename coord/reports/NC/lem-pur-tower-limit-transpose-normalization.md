## Worker report

Statement-only delivery for lem-pur-tower-limit-transpose-normalization, in
`Sheaf.CategoryTheory.TowerLimitTransposeNormalization`. The only postponed proof is
`CategoryTheory.TowerLimitTransposeNormalization.tower_limit_transpose_normalization`.
Every helper is a transparent abbreviation, an instance supplied by existing data/theorems,
or a fully written proposition; none chooses mathematical data from a sorry.

The module uses the existing canonical localization constructions, not abstract adjunctions
chosen independently of the module adjunction. Its theorem supplies the naturally varying
comparison `a` together with the exact common-underived-composite equation from the recorded
pushforward/limit comparison. This equation uniquely identifies that comparison: both sides
are right-derived comparisons of the same composite, and their K-injective components are
isomorphisms. Thus its existential presentation is precisely the stipulated `a`, not a
choice of a different isomorphism of right adjoints. No projection-detection assumption is used.

Hypothesis and clause correspondence (Lean site J is the paper's Y; K is X):

| Node hypothesis/clause | Lean rendering |
| --- | --- |
| Commutative Noetherian A | `{A : Type u} [CommRing A]`, `[IsNoetherianRing A]` |
| Any ideal I, positive quotient indices | `(_I : Ideal A)`; the quotient rings are not used by this assertion. There is no assumption on I or its powers. `op n` encodes level n+1, so op 0 is level 1. |
| A geometric morphism between small presented topoi | `C D : Type u`, `SmallCategory`, `J`, `K`, `L`, `U`, `adj : L ⊣ U`, `hL : PreservesFiniteLimits L`. Small skeleta live in the module universe. |
| Canonical constant-coefficient inverse and direct images | `d : ConstantLeftModuleInverseImageLift J K A L U adj hL`, the exact existing record owned by def-pur-constant-module-inverse-image-lift. Its module functors, scalar and underlying-sheaf identifications, and unit compatibility specify the canonical lift. Existence for every displayed geometric adjunction is the recorded `constant_left_module_inverse_image`, not an extra restriction on the morphism. |
| Constant rings, module sheaves and ordinary unbounded derived categories | Existing `Modules J A` and `Modules K A` abbreviate `ringedSiteModules` of `constantSheaf ... (RingCat.of A)`; `DerivedCategory.{w}`, with explicit localization instances for both categories and both strict tower categories. No adic or completed category is substituted. |
| u* left adjoint to P=Ru*, with its actual counit | `moduleAdjunction d` is exactly `d.moduleAdj.mapDerivedCategoryRightDerivedAdjunction`. Its `homEquiv` and inverse use the actual unit and counit. ProjectionMateExact is a proof-context import; none of its declarations occurs in this assertion's maps. |
| Strict constant-A towers, Delta, termwise G, and P^J | `ℕᵒᵖ ⥤ Modules ...`, `(Functor.const ℕᵒᵖ).mapDerivedCategory`, `towerInverse d` followed by exact localization, `towerDirect d` followed by `rightDerivedFunctor`. `towerAdjunction d` derives the actual termwise ordinary adjunction. |
| Total derived inverse limit | `(towerLimit ...).rightDerivedFunctor`, with `towerLimit` transparently Mathlib's `lim`. The published module/tower K-injective-resolution instances apply. |
| Derive Delta left adjoint to lim from the ordinary module adjunction | `limitAdjunction` is the existing `mapDerivedCategoryRightDerivedAdjunction` applied to the actual `constLimAdj`. |
| Diagonal K-injective identity normalization L Delta = 1 | The two `IsIso ...unit` conclusions provide the natural comparison with identity. Both `ConstantUnitNormalization` conclusions identify that unit on every diagonal K-injective representative with the localized ordinary cone of identity maps followed by the canonical limit comparison. Its inverse is exactly the source identification used in the node. |
| a is exactly the derived common-direct-image comparison | The first universally quantified equation uses `preservesLimitNatIso d.moduleDirect`, whose components are `limit.post`, and the existing `UnboundedExactTower.cochainUnit`. It is the same equation as the recorded comparison theorem, with its generic units specialized to the canonical right derived functors. |
| Equality of the displayed composite Hom bijection | The penultimate forall M,V,c composes inverse `limitAdjunction J.homEquiv`, inverse `towerAdjunction.homEquiv`, the inverse of `constantInterchange`, then `limitAdjunction K.homEquiv`. It equals inverse `moduleAdjunction.homEquiv` after `c ≫ a.inv.app V`. The orientations were checked against the types of every intermediate arrow. |
| Arbitrary tower objects Z,V, b:GZ -> V, and augmentation j:Delta M -> Z | The last forall binds exactly M,Z,V,b,j. Its left side is the ordinary adjunct of the limit transpose of `G.map j ≫ b`, transported by `constantInterchange.inv`. Its right side is `unit.app M ≫ L.map j ≫ L.map (towerAdjunction.homEquiv Z V b) ≫ a.inv.app V`. |
| Source of the limit map identified with u*M | `constantInterchange.inv.app M` supplies the descended identity G Delta = Delta u*. The constant/limit Hom equivalence inserts the actual unit, whose inverse is the normalized L Delta identification. The visible unit on the right is exactly the source identification suppressed in the TeX formula. |
| Actual counits and naturality in all displayed arguments | All three adjunctions are the specified ordinary-to-derived constructions. Their actual `homEquiv` values determine the counits (take the inverse image of the identity), so the equalities include them. The comparisons and units are natural transformations; Hom equivalences are natural; the two equations hold for every morphism, including every j and b. This is a pointwise equality of natural operations, hence retains all their naturality squares. |
| No perfectness/completeness/boundedness | No such parameter, predicate, or subcategory occurs. There is also no assumption about exact countable products. |

Dependency declarations read and used:

- def-weil-size-convention: no Lean object; universes u,w are explicit, with sites small
  in u and independently chosen derived morphism universe w.
- Mathlib.CategoryTheory.Sites.ConstantSheaf: `CategoryTheory.constantSheaf`.
- Mathlib.RingTheory.Noetherian.Defs: `IsNoetherianRing`.
- Sheaf.CategoryTheory.RingedSiteModules: `CategoryTheory.ringedSiteModules`, transparently
  Mathlib `SheafOfModules`, with the existing small-site abelian structures.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`, `HasDerivedCategory`, `Q`.
- Sheaf.Paper.ProjectionMateExact: proof-context import for the recorded dependency
  `SheafOfModules.ringedProjectionMateExact`; no declaration from it occurs in the statement.
- Sheaf.CategoryTheory.DiagramSiteRealization: `CategoryTheory.exists_diagramSite_realization`.
- Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`, the actual unbounded
  strict-tower total right-derived limit, not a product-exactness replacement.
- Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison:
  `CategoryTheory.ringedTowerPushforwardLimitComparison`, especially its normalization equation
  involving eta_f, eta_R, the ordinary c, eta_S, eta_t, and a.
- Sheaf.CategoryTheory.ConstantLeftModuleTransport: `ConstantLeftModuleInverseImageLift`,
  its moduleFunctor, moduleDirect, moduleAdj, exactness fields, and
  `ConstantLeftModuleInverseImage.Modules`, now owned by the new definition node
  def-pur-constant-module-inverse-image-lift. ConstantLeftModuleInverseImage is retained as
  a proof import for the recorded inverse-image existence theorem.
- Sheaf.CategoryTheory.UnboundedExactAdjunctionSquare: existing `UnboundedExactTower.cochainUnit`,
  `constantInterchange`, `moduleResolutions`, `towerResolutions`. The first two are now owned
  by def-pur-tower-derived-localization-comparisons. The latter two are existing resolution
  instances, not uses of the adjunction-square theorem conclusion.
- Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction:
  `SheafOfModules.module_pullback_pushforward_adjunction` (proof context).
- Mathlib.CategoryTheory.Abelian.FunctorCategory: `Abelian.functorCategoryAbelian` and evaluation
  exactness; Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor: `mapDerivedCategory`,
  `mapDerivedCategoryFactors`.
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp:
  `Adjunction.preservesKInjectiveComplexes`; its Adjunction companion provides
  `Adjunction.mapDerivedCategoryRightDerivedAdjunction`, read in full.
- Sheaf.CategoryTheory.KInjectiveTotalDerived:
  `CategoryTheory.exists_rightDerived_of_enough_isKInjective` (proof context).
- Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
- Mathlib.Algebra.Homology.DerivedCategory.KInjective:
  `CochainComplex.IsKInjective.Qh_map_bijective`.
- WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction:
  `Adjunction.mapHomologicalComplex`, `Adjunction.mapHomotopyCategory`.
- Mathlib.CategoryTheory.Functor.Derived.Adjunction: `Adjunction.derived`,
  `derivedη_fac_app`, `derivedε_fac_app` (the mathlib_match of
  lem-sc-derived-adjunction-from-underived).

Edge cases checked before writing and again after elaboration:

- The zero ring and zero objects cause no excluded case: all functors and Hom equations are
  defined, and the canonical units remain invertible on constant towers.
- I=0 and I=A are allowed; no quotient, inverse transition, nonzero-ring or separatedness
  condition occurs. The positive first index is op 0, so there is no accidentally missing level.
- Identity geometric morphisms and constant towers reduce to the ordinary constant/limit
  adjunction, retaining its units rather than requiring definitional equalities of functors.
- Taking b to be the actual tower counit, or j the identity on Delta M, gives the stipulated
  counit/augmentation specializations without choosing unrelated adjunctions.
- Towers with zero or non-surjective transitions are included. No exact products or limits
  are assumed. Equality of ordinary complex limit maps in the proof does not invoke detection
  by projections in the derived category.
- The empty site is allowed. The tower index is the nonempty fixed positive naturals, as
  specified, not an arbitrary empty diagram.

Searches made for an existing statement:

1. msearch.py leansearch, query `Derived inverse limit constant diagram adjunction compatible
   with derived pushforward transpose`: 8 hits, including constLimAdj, derived_unit, derived',
   sheaf pushforward/pullback adjunctions. None identifies this fixed total-limit comparison
   with the composite Hom bijection and all augmented-arrow transposes.
2. msearch.py leanfinder, query `Derived inverse limit pushforward comparison identifies
   adjunction transposes of constant tower maps`: 8 underived sheaf comparison and counit hits,
   including SheafOfModules.pushforwardPushforwardAdj_counit_app_val_app; no exact match.
3. msearch.py loogle, query `CategoryTheory.Adjunction.comp, CategoryTheory.Limits.constLimAdj`:
   0 hits for the joint query. The individual generic constructions were read and reused.
4. msearch.py grep, regexp `tower.*[Tt]ranspose|[Ll]imit.*[Nn]ormalization`, subdirectory
   CategoryTheory: 0 hits. Direct rg of lean/WeilConjectures and lean/Sheaf with that regexp
   returned general tower/normalization modules, including UnboundedExactAdjunctionSquare
   (reused), RingedTowerPushforwardLimitAcyclic and RingedStrictTowerProjectionMorphism;
   none already states this item. Exact-id search in WeilConjectures had no match.
5. Exact declaration-name rg for tower_limit_transpose_normalization and
   ConstantUnitNormalization in project/upstream/Mathlib: no collision. Read the existing
   DAG records for related constant-tower normalization and derived-composition normalization;
   those are different statements, as the item's stage-1 review also observes.

The source read is literature/stacks-project/sites-cohomology.tex, lemma-adjoint and
lemma-Rf-commutes-with-Rlim (0A07), first proof, together with the existing node's seven-step
normalization argument. The sample CompactObject module is now withdrawn (empty module);
its node's recorded definition was read for the record conventions.

No mathematical statement correction, disputed statement, or unusable dependency was found.
The returned H2 ownership fault is repaired by two new definition records pointing to unchanged
live declarations. The statement text, theorem signature, proof, proof_deps and all other
existing metadata are preserved; only lean and the authorized definition-node additions to
stmt_deps change.

Initial-delivery validation: scompile.py compiled both its sandbox probe and the real module
with no errors or warnings (10.8 s and 14.6 s in the clean run). All definitions have real terms and the single
sorry is the whole named theorem proof, with all seven natural-language proof steps above it.
The prescribed delivery dry run and final delivery are run after this report is written.

## Second reading by NC

Author's separate second pass, not an independent-worker review: the dispatcher explicitly
forbids starting another agent, and the maintainer independently reviews this delivery.
I reopened the node and module and checked the types in both Hom chains. In particular the
constant/interchange map must be its inverse (Delta F M -> G Delta M), `a.inv` is postcomposed
on the target-Y side, and Lean composition j then b-sharp is the paper's b-sharp composed with j.
The remaining visible constant/limit unit is necessary because Rlim Delta = identity is an
isomorphism rather than definitional equality. I added the explicit ConstantUnitNormalization
clauses so the diagonal identity normalization is asserted, not merely inferred from unit
invertibility. The compile found a misplaced projection dot and the countable-shape instance
needed by preservesLimitNatIso; both were repaired, and the final clean run also checked the
100-character line limit. No mathematical statement mismatch remains in this pass.


## New nodes

def-pur-constant-module-inverse-image-lift records the type of normalized constant-ring
left-module lifts, rather than the theorem that this type is inhabited. Its existing:true
record points to ConstantLeftModuleInverseImageLift and its Modules/forgetful/operation
helpers in Sheaf.CategoryTheory.ConstantLeftModuleTransport. No Lean module is added or
copied. The source is Stacks 00YV (2), (5), (6), including the fixed-ring endomorphism
paragraph. The node introduces the small sites, ring, and specified geometric adjunction;
it spells out the constant-ring and point comparisons, ring and scalar normalizations,
module and abelian adjunctions, exactness, underlying-sheaf comparisons and both unit
compatibilities. The original theorem lem-pe-constant-left-module-transport owns an
existence assertion, not this definition. The related def-trf-abelian-inverse-image-presentation
only specifies an abelian functor and its graph normalization: it has neither module
scalars nor adjunctions, so cannot serve as this definition. Zero rings, noncommutative
rings, empty sites, and identity geometric morphisms are retained. This datum has no
existence assertion, unique-choice construction, or new postponed proof.

def-pur-tower-derived-localization-comparisons records the specified constant interchange
and cochain unit in Sheaf.CategoryTheory.UnboundedExactAdjunctionSquare, with existing:true.
Its primary declaration is constantInterchange; lean.declarations also names cochainUnit.
For arbitrary abelian A,B with independently chosen localization universes, the first is
the three exact-localization isomorphisms descending the ordinary constant/termwise identity.
For an additive G with K-injective resolutions in its source, the second is the four-arrow
composite from Q(GI) to RG(QI), using quotientCompQhIso, mapHomotopyCategoryFactors, and the
homotopy-level rightDerivedFunctorUnit. This is exactly the unchanged live source, without
a theorem asserting adjunction compatibility. The source is Stacks 015F/0DVC/070K and the
0A07 common-derived-limit application. It adds no assumption on exact countable products,
no relation between localization universes, and no choice of a replacement comparison.
Zero functors and complexes, constant and zero towers, and identity functors are allowed.

For both nodes the three logged msearch kinds were run during this repair. The first
node used leansearch and leanfinder with query `Normalized constant ring module inverse
image lift of a geometric morphism with transported addition scalar action and adjunction
unit`. LeanSearch returned eight hits, including SheafOfModules pullback adjunctions and
presheaf pullback; LeanFinder returned eight hits including scheme normalization and
module pullback. They do not define this transported, unit-normalized datum. The second
used both tools with `Canonical cochain unit of total right derived functor and derived
constant diagram exact functor interchange`. LeanSearch returned eight hits including
totalRightDerivedUnit; LeanFinder returned eight including mapDerivedCategoryFactors.
These are general ingredients. Both nodes record the logged Mathlib grep query
`ConstantLeftModuleInverseImageLift|constantInterchange|cochainUnit`, which returned zero
hits. Direct rg across lean/WeilConjectures and lean/Sheaf located the reused definitions
in ConstantLeftModuleTransport:41/134 and UnboundedExactAdjunctionSquare:102/141. A parsed
search of all definition nodes found no node owning these interfaces. The sole related
result def-trf-abelian-inverse-image-presentation is distinguished above. The theorem
records listing these helpers are the ownership problem identified by the return.
Blueprint searches `inverse.image.*constant|constant.*inverse.image` and
`cochain.*unit|constant.*interchange` both returned zero matches. The ancestor command
returned thm-pur-rational-and-qbar-purity; both new records use that ancestor and the
item's existing blueprint path.

## Returned delivery repair

H2, immutable head 2697b770ba8c: removed the two added theorem-node statement dependencies
lem-pe-constant-left-module-inverse-image and lem-sbc-unbounded-exact-adjunction-square.
Replaced them with the two definition nodes above, whose existing:true records own
exactly the reused live definitions. The item's original nine statement dependencies
are unchanged. No theorem conclusion from either removed dependency occurs in the
statement. The theorem statement and its single sorry proof remain unchanged.

The advisory on imports is addressed: the constant lift is publicly imported directly
from ConstantLeftModuleTransport; the inverse-image theorem module is a proof import.
ProjectionMateExact, RingedTowerPushforwardLimitComparison, and
RingedStrictTowerHomotopyLimitIndependentCoefficients are ordinary proof imports.
UnboundedExactAdjunctionSquare remains public because it supplies the two actual map
definitions now bound to the definition node. The live module sources were also read
with scompile.py --source; their defining signatures and composites agree with the local
read clone. The first required dry run of the saved packet passed as c1bebf032c7;
the returned ownership fault still needed and received the concrete repair above.

## Second reading by NC (repair)

This is the author's separate pass; no second worker was started, as the dispatcher forbids
it. I compared the sandbox node with current main: before repair only lean and the two
added theorem-node stmt_deps differed. After repair the original statement and proof
remain equal, as does the theorem signature read from its module. I reopened both live
interfaces and compared all fields of the lift with its new definition statement:
ringUnderlying/ring_add/ring_mul/pointIso/constant_scalar; moduleFunctor/moduleDirect/
moduleAdj/additive/preservesFiniteLimits/preservesFiniteColimits; abelianInverse/
abelianDirect/abelianAdj/abelianSetIso/abelianDirectSetIso/abelian_addition/abelian_unit;
underlyingIso/directUnderlyingIso/moduleSetIso/moduleSetIso_compatibility;
scalar_compatibility/unit_compatibility. Every field is represented, and no inhabitedness
claim was imported into the definition. I then checked the order and orientation of all
three constantInterchange factors and all four cochainUnit factors. The new definition
states those composites and does not assert the unrelated square-mate theorem. The Hom
chain, arbitrary-augmentation formula, canonical comparison equation, unit IsIso and
ConstantUnitNormalization clauses have not changed from the independently accepted
mathematics of the returned packet. The A=0, I=0/A, empty-site, u=id and b=counit cases
and explicit u/w universes still apply. The only issue found was the returned ownership
fault; both owning definition records and their statement dependency edges now repair it.

Repair validation: scompile.py compiled the sandbox probe and actual module cleanly
(19.2 s and 19.8 s). The record signature equals the theorem signature verbatim;
there is one whole-theorem sorry, maximum Lean line width 95, and both new
definition records cite exactly their bracketed definition dependencies.
