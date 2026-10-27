/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.SpaceChartTensorRealization
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
import Sheaf.AlgebraicGeometry.StackQuasiCoherentSchemeRestriction
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

public import Sheaf.CategoryTheory.CochainCoefficientUniverseTransport

/-!
# Module operations with ambient-size coefficients on algebraic spaces

Source: Stacks Project, Properties of Spaces, Tags 03G8, 03H7 and 03LV;
Morphisms of Algebraic Spaces, Tag 03M8; Modules on Sites, Tag 03D7
(blueprint: lem-sfb-fibred-fppf-space-module-comparisons).

A direct image is specified by a limit of sections on ALL étale scheme charts, together
with the restriction and module-map identities for the limit projections. This universal
property determines the functor up to its unique normalized natural isomorphism. Tensor
pullback is the left adjoint to this direct image, with its adjunction unit retained.
These are item-local coefficient extensions of the existing chart construction.
The chart categories are reused; the normalized bridge below relates both pullbacks.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.checkUnivs false
set_option synthInstance.maxSize 2048

universe u v w m

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}

/-- The existing canonical coefficient lift of the small étale regular-function sheaf.
Source: Stacks 03G8 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
abbrev ambientModuleRing (X : AlgebraicSpace S) :
    Sheaf X.etaleTopology RingCat.{max (u + 1) v w} :=
  (sheafCompose X.etaleTopology
    (forget₂ CommRingCat.{max (u + 1) v w} RingCat.{max (u + 1) v w})).obj
    (CategoryTheory.moduliTargetStructureSheaf.{u, v, w} X)

/-- Modules in the ambient universe, with the unchanged regular-function scalar action.
Source: Stacks 03G8 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
abbrev AmbientModules (X : AlgebraicSpace S) :=
  SheafOfModules.{max (u + 1) v w} (ambientModuleRing.{u, v, w} X)

/-- The actual map of regular functions from `V` to a chart of `X ×_Y V`.
Source: Stacks, Tags 03G8 and 03M8 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def ambientModuleChartScalar (f : X ⟶ Y) (V : Y.EtaleSite) (q : ModuleChart f V) :
    (ambientModuleRing.{u, v, w} Y).obj.obj (op V) ⟶ (ambientModuleRing.{u, v, w} X).obj.obj (op
    q.left) :=
  RingCat.ofHom (Scheme.Γ.map q.hom.left.left.op).hom.ulift

/-- A chart restriction is linear over the functions on `V`.
Source: Stacks, Tag 03M8 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons).
Proof: semilinearity of the module restriction, followed by functoriality of the two
pullbacks of regular functions along the commuting triangle of chart schemes. -/
theorem ambientModuleChartMap_smul (f : X ⟶ Y) (M : AmbientModules.{u, v, w} X) (V : Y.EtaleSite)
    {q r : ModuleChart f V} (a : q ⟶ r)
    (b : (ambientModuleRing.{u, v, w} Y).obj.obj (op V)) (m : M.val.obj (op r.left)) :
    M.val.map a.left.op (ambientModuleChartScalar.{u, v, w} f V r b • m) =
      ambientModuleChartScalar.{u, v, w} f V q b • M.val.map a.left.op m := by
  sorry

/-- Restriction between chart sections, viewed as a linear map over `Γ(V,𝒪_V)`.
Source: Stacks, Tag 03M8 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def ambientModuleChartMap (f : X ⟶ Y) (M : AmbientModules.{u, v, w} X) (V : Y.EtaleSite)
    {q r : ModuleChart f V} (a : q ⟶ r) :
    (ModuleCat.restrictScalars (ambientModuleChartScalar.{u, v, w} f V r).hom).obj
        (M.val.obj (op r.left)) ⟶
      (ModuleCat.restrictScalars (ambientModuleChartScalar.{u, v, w} f V q).hom).obj
        (M.val.obj (op q.left)) :=
  ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (ambientModuleChartScalar.{u, v, w} f V r).hom).obj
      (M.val.obj (op r.left)))
    (Y := (ModuleCat.restrictScalars (ambientModuleChartScalar.{u, v, w} f V q).hom).obj
      (M.val.obj (op q.left)))
    { toFun := fun m ↦ M.val.map a.left.op m
      map_add' := (M.val.map a.left.op).hom.map_add
      map_smul' := ambientModuleChartMap_smul.{u, v, w} f M V a }

/-- Identity law for the chart diagram.
Source: Stacks, Tag 03M8 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons).
Proof: the restriction of `M` along the identity is the identity on every section. -/
theorem ambientModuleChartMap_id (f : X ⟶ Y) (M : AmbientModules.{u, v, w} X) (V : Y.EtaleSite)
    (q : ModuleChart f V) : ambientModuleChartMap.{u, v, w} f M V (𝟙 q) = 𝟙 _ := by
  sorry

/-- Composition law for the chart diagram.
Source: Stacks, Tag 03M8 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons).
Proof: both maps are the iterated module restriction along the composite chart map. -/
theorem ambientModuleChartMap_comp (f : X ⟶ Y) (M : AmbientModules.{u, v, w} X) (V : Y.EtaleSite)
    {q r t : ModuleChart f V} (a : q ⟶ r) (b : r ⟶ t) :
    ambientModuleChartMap.{u, v, w} f M V (a ≫ b) = ambientModuleChartMap.{u, v, w} f M V b ≫
    ambientModuleChartMap.{u, v, w} f M V a := by
  sorry

/-- The diagram whose limit is the compatible sections on all scheme charts of `X ×_Y V`.
Source: Stacks, Tags 03H7 and 03M8 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def ambientModuleChartDiagram (f : X ⟶ Y) (M : AmbientModules.{u, v, w} X) (V : Y.EtaleSite) :
    (ModuleChart f V)ᵒᵖ ⥤ ModuleCat.{max (u + 1) v w} ((ambientModuleRing.{u, v, w} Y).obj.obj
    (op V)) where
  obj q := (ModuleCat.restrictScalars (ambientModuleChartScalar.{u, v, w} f V q.unop).hom).obj
    (M.val.obj (op q.unop.left))
  map a := ambientModuleChartMap.{u, v, w} f M V a.unop
  map_id q := ambientModuleChartMap_id.{u, v, w} f M V q.unop
  map_comp a b := ambientModuleChartMap_comp.{u, v, w} f M V b.unop a.unop

/-- A normalized direct image: its sections are limits of the actual chart module diagram;
its maps are characterized by their components on EVERY chart. The projection identities
include both restrictions in the test scheme and morphisms of modules.
Source: Stacks, Tags 03H7 and 03M8 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
structure AmbientModuleDirectImageModel (f : X ⟶ Y) where
  /-- Module direct image on the small étale sites. -/
  functor : AmbientModules.{u, v, w} X ⥤ AmbientModules.{u, v, w} Y
  /-- Projection of a section to a chart of the fibre product. -/
  projection (M : AmbientModules.{u, v, w} X) (V : Y.EtaleSite) :
    (Functor.const (ModuleChart f V)ᵒᵖ).obj ((functor.obj M).val.obj (op V)) ⟶
      ambientModuleChartDiagram.{u, v, w} f M V
  /-- Compatible sections are exactly the limit, with its specified projections. -/
  isLimit (M : AmbientModules.{u, v, w} X) (V : Y.EtaleSite) :
    IsLimit (Cone.mk ((functor.obj M).val.obj (op V)) (projection M V))
  /-- Naturality for module morphisms, on every chart section. -/
  map_projection {M N : AmbientModules.{u, v, w} X} (a : M ⟶ N) (V : Y.EtaleSite)
    (q : ModuleChart f V) (s : (functor.obj M).val.obj (op V)) :
    (projection N V).app (op q) ((functor.map a).val.app (op V) s) =
      a.val.app (op q.left) ((projection M V).app (op q) s)
  /-- Naturality for restrictions of the test scheme, on every chart section. -/
  restriction_projection (M : AmbientModules.{u, v, w} X) {V W : Y.EtaleSite} (a : V ⟶ W)
    (q : ModuleChart f V) (s : (functor.obj M).val.obj (op W)) :
    (projection M V).app (op q) ((functor.obj M).val.map a.op s) =
      (projection M W).app (op ((moduleChartPost f a).obj q)) s

/-- The compatible-chart-section universal property is realized by a module direct image.
Source: Stacks, Tags 03H7, 03G8 and 03M8
(blueprint: lem-sfb-fibred-fppf-space-module-comparisons).
Proof: extend each module to étale algebraic spaces by compatible sections. On a scheme
atlas this is the descent equalizer, so the result is a sheaf and is independent of the
atlas. Pullback of regular functions supplies the scalar action on every chart. Sections
on `V` are the compatible sections on `X ×_Y V`; restrictions and module maps act on
these same families componentwise. These are limits with the displayed projections.
The atlas and its overlaps are schemes in universe `u`; matching sections are
formed in the ambient module universe, which contains the atlas indexing sets.
The limit property and the two projection identities determine the functor up to its
unique normalized natural isomorphism; this is a universal-property construction. -/
theorem ambientModuleDirectImageModel_nonempty (f : X ⟶ Y) :
    Nonempty (AmbientModuleDirectImageModel.{u, v, w} f) := by
  sorry

/-- The chart universal property determines direct image up to a unique normalized iso.
Source: Stacks, Tags 03H7 and 03M8 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons).
Proof: the universal property gives the unique section map between the two limits on
`V`. The projection identities make these maps natural in `V` and in the module. Their
composites have the projections of the identity and hence equal the identity, by limit
uniqueness. The same argument proves uniqueness of the normalized natural isomorphism. -/
theorem ambientModuleDirectImageModel_unique (f : X ⟶ Y)
    (D E : AmbientModuleDirectImageModel.{u, v, w} f) :
    ∃! e : D.functor ≅ E.functor,
      ∀ (M : AmbientModules.{u, v, w} X) (V : Y.EtaleSite) (q : ModuleChart f V)
        (s : (D.functor.obj M).val.obj (op V)),
        (E.projection M V).app (op q) ((e.hom.app M).val.app (op V) s) =
          (D.projection M V).app (op q) s := by
  sorry

/-- The normalized direct-image model, selected by its complete limit universal property.
Source: Stacks, Tags 03H7 and 03M8 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def ambientModuleDirectImageModel (f : X ⟶ Y) : AmbientModuleDirectImageModel.{u, v, w} f :=
  Classical.choice (ambientModuleDirectImageModel_nonempty.{u, v, w} f)

/-- Canonical module direct image, retaining the compatible-section model above.
Source: Stacks, Tag 03G8 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def ambientModuleDirectImage (f : X ⟶ Y) :
    AmbientModules.{u, v, w} X ⥤ AmbientModules.{u, v, w} Y :=
  (ambientModuleDirectImageModel.{u, v, w} f).functor

/-- Tensor pullback exists as the left adjoint of the specified module direct image.
Source: Stacks, Tag 03D7 and Tag 03G8 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons).
Proof: on the enlarged étale ringed sites form the usual inverse image and extension of
scalars, and transport it through the scheme-chart equivalences. The tensor universal
property identifies its maps to `F` with maps to the compatible-section direct image.
This supplies the adjunction to the direct image already fixed above; uniqueness of a
left adjoint identifies any two such tensor constructions compatibly with their units. -/
theorem ambientModuleDirectImage_isRightAdjoint (f : X ⟶ Y) :
    (ambientModuleDirectImage.{u, v, w} f).IsRightAdjoint := by
  sorry

attribute [instance] ambientModuleDirectImage_isRightAdjoint

/-- The tensor pullback, specified by its adjunction to the canonical direct image.
Source: Stacks, Tags 03D7 and 03G8 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def ambientModuleTensorPullback (f : X ⟶ Y) :
    AmbientModules.{u, v, w} Y ⥤ AmbientModules.{u, v, w} X :=
  (ambientModuleDirectImage.{u, v, w} f).leftAdjoint

/-- The unit and counit fixing the normalization of tensor pullback.
Source: Stacks, Tag 03D7 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def ambientModuleTensorAdjunction (f : X ⟶ Y) : ambientModuleTensorPullback.{u, v, w} f ⊣
    ambientModuleDirectImage.{u, v, w} f :=
  Adjunction.ofIsRightAdjoint (ambientModuleDirectImage.{u, v, w} f)

/-- The local tensor `b ⊗ m`, for `m` represented on `V` and a chart over `V`.
The unit sends `m` to `1 ⊗ m`; projection to the chart and multiplication by `b` give
`b ⊗ m`. This uses the chosen adjunction, not a freely chosen map into the pullback.
Source: Stacks, Tags 03D7, 03LV (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def ambientModuleTensorSection (f : X ⟶ Y) (M : AmbientModules.{u, v, w} Y) (V : Y.EtaleSite)
    (q : ModuleChart f V) (b : (ambientModuleRing.{u, v, w} X).obj.obj (op q.left))
    (m : M.val.obj (op V)) : ((ambientModuleTensorPullback.{u, v, w} f).obj M).val.obj (op
    q.left) :=
  b • @id (((ambientModuleTensorPullback.{u, v, w} f).obj M).val.obj (op q.left))
    (((ambientModuleDirectImageModel.{u, v, w} f).projection ((ambientModuleTensorPullback.{u, v,
    w} f).obj M) V).app
      (op q) (((ambientModuleTensorAdjunction.{u, v, w} f).unit.app M).val.app (op V) m))

/-- The normalization of the tensor compositor on nested chart tensors.
Source: Stacks 03D8 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def AmbientTensorCompositionFormula (a : X ⟶ Y) (b : Y ⟶ Z)
    (μ : ambientModuleTensorPullback.{u, v, w} b ⋙
      ambientModuleTensorPullback.{u, v, w} a ≅
        ambientModuleTensorPullback.{u, v, w} (a ≫ b)) : Prop :=
  ∀ (M : AmbientModules.{u, v, w} Z) (E : Z.EtaleSite) (q : ModuleChart b E)
    (r : ModuleChart a q.left)
    (t : (moduleChartTarget (a ≫ b)).obj r.left ⟶ E.obj),
    t.left = r.hom.left ≫ q.hom.left →
    ∀ (x : (ambientModuleRing.{u, v, w} X).obj.obj (op r.left))
      (y : (ambientModuleRing.{u, v, w} Y).obj.obj (op q.left))
      (m : M.val.obj (op E)),
      (μ.hom.app M).val.app (op r.left)
        (ambientModuleTensorSection.{u, v, w} a
          ((ambientModuleTensorPullback.{u, v, w} b).obj M) q.left r x
            (ambientModuleTensorSection.{u, v, w} b M E q y m)) =
      ambientModuleTensorSection.{u, v, w} (a ≫ b) M E
        (CostructuredArrow.mk (Y := r.left) t)
          (x * ambientModuleChartScalar.{u, v, w} a q.left r y) m

/-- The tensor compositor is uniquely normalized by multiplication of coefficients.
Source: Stacks 03D8 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons).
Proof: use the scalar-extension associator on the enlarged ringed sites,
sending x tensor (y tensor m) to x a-sharp(y) tensor m, with inverse inserting
one. Balancing proves both identities on tensors; sheafification preserves them.
Transport by the unit-compatible left-adjoint identifications for the three chart
direct images. Their units insert ones, giving precisely the displayed formula.
Conversely this formula determines the adjoint on each chart-unit section, hence
all projections of its chart-limit cone. The adjunction makes the map unique. -/
theorem existsUnique_ambientTensorComp (a : X ⟶ Y) (b : Y ⟶ Z) :
    ∃! μ : ambientModuleTensorPullback.{u, v, w} b ⋙
      ambientModuleTensorPullback.{u, v, w} a ≅
        ambientModuleTensorPullback.{u, v, w} (a ≫ b),
      AmbientTensorCompositionFormula.{u, v, w} a b μ := by
  sorry

/-- The usual tensor compositor, fixed by its local tensor normalization.
Source: Stacks 03D8 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def ambientTensorComp (a : X ⟶ Y) (b : Y ⟶ Z) :
    ambientModuleTensorPullback.{u, v, w} b ⋙ ambientModuleTensorPullback.{u, v, w} a ≅
      ambientModuleTensorPullback.{u, v, w} (a ≫ b) :=
  (existsUnique_ambientTensorComp.{u, v, w} a b).choose

/-- The normalization of the identity pullback: its local tensor is multiplication.
Source: Stacks 03D7 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def AmbientTensorIdentityFormula (X : AlgebraicSpace S)
    (e : ambientModuleTensorPullback.{u, v, w} (𝟙 X) ≅ 𝟭 (AmbientModules.{u, v, w} X)) :
    Prop :=
  ∀ (M : AmbientModules.{u, v, w} X) (E : X.EtaleSite)
    (q : ModuleChart (𝟙 X) E) (r : q.left ⟶ E), r.hom = q.hom →
    ∀ (b : (ambientModuleRing.{u, v, w} X).obj.obj (op q.left))
      (m : M.val.obj (op E)),
      (e.hom.app M).val.app (op q.left)
        (ambientModuleTensorSection.{u, v, w} (𝟙 X) M E q b m) = b • M.val.map r.op m

/-- The tensor identity isomorphism is uniquely normalized by multiplication.
Source: Stacks 03D7 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons).
Proof: for the identity geometric morphism, scalar extension is tensor over the
same ring. Multiplication is inverse to insertion of one by balancing. Transport
this isomorphism by the normalized chart adjunction. Its local formula is the
displayed multiplication. That formula determines all chart-unit values and thus
the adjoint, proving uniqueness. -/
theorem existsUnique_ambientTensorId (X : AlgebraicSpace S) :
    ∃! e : ambientModuleTensorPullback.{u, v, w} (𝟙 X) ≅ 𝟭 (AmbientModules.{u, v, w} X),
      AmbientTensorIdentityFormula.{u, v, w} X e := by
  sorry

/-- The usual tensor unitor, fixed by its multiplication formula.
Source: Stacks 03D7 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def ambientTensorId (X : AlgebraicSpace S) :
    ambientModuleTensorPullback.{u, v, w} (𝟙 X) ≅ 𝟭 (AmbientModules.{u, v, w} X) :=
  (existsUnique_ambientTensorId.{u, v, w} X).choose

/-- The unlifted commutative regular-function presheaf is a sheaf.
Source: Stacks 03G7 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons).
Proof: an etale covering of a chart is an etale scheme covering. Descent for
regular functions gives the matching-family equalizer as commutative rings,
with precisely the same underlying presheaf as the existing structure sheaf. -/
theorem ambientSmallCommRing_isSheaf (X : AlgebraicSpace S) :
    Presheaf.IsSheaf X.etaleTopology ((etaleForget X).op ⋙ Scheme.Γ) := by
  sorry

/-- Repackage the existing regular functions as commutative rings for size transport.
Source: Stacks 03G7 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def ambientSmallCommRing (X : AlgebraicSpace S) : Sheaf X.etaleTopology CommRingCat.{u} :=
  ⟨(etaleForget X).op ⋙ Scheme.Γ, ambientSmallCommRing_isSheaf X⟩

/-- The existing sectionwise ULift functor embeds the universe-u module category.
Carriers are ULift M(T), restrictions send m to ULift.up (M(q) m.down), and
lifted scalars act through their down maps; no smallness hypothesis is imposed.
Source: Stacks 03DA (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def ambientModuleLift (X : AlgebraicSpace S) : Modules X ⥤ AmbientModules.{u, v, w} X :=
  SheafOfModules.CochainUniverseTransport.functor.{u + 1, u, u, u, max (u + 1) v w}
    (ambientSmallCommRing X)

/-- Ambient pullback extends Q24's pullback, with the same adjunction-unit tensors.
This relates the item-local interface to the unchanged recorded dependency and
fixes its identification on every chart, rather than postulating an arbitrary iso.
Source: Stacks 03DA, 03D7 (blueprint: lem-sfb-fibred-fppf-space-module-comparisons).
Proof: sectionwise ULift preserves balanced tensors and their sheafification:
lift b tensor m to ULift.up b tensor ULift.up m, and descend by ULift.down.
These maps respect balancing, chart restrictions and module morphisms and are
mutually inverse. Identify each tensor realization with the specified left
adjoint using its unit and the chart-limit projections. This produces the
natural isomorphism with the displayed formula. Conversely the formula on
chart-unit tensors determines the adjoint on every chart projection, so the
limit and adjunction universal properties prove uniqueness. This is the bridge
for applying the universe-u chart, etale and quasi-coherent lemmas after lifting. -/
theorem existsUnique_ambientModuleTensorLift (f : X ⟶ Y) :
    ∃! e : ambientModuleLift.{u, v, w} Y ⋙ ambientModuleTensorPullback.{u, v, w} f ≅
        moduleTensorPullback f ⋙ ambientModuleLift.{u, v, w} X,
      ∀ (M : Modules Y) (E : Y.EtaleSite) (q : ModuleChart f E)
        (b : X.structureSheaf.obj.obj (op q.left)) (s : M.val.obj (op E)),
        (e.hom.app M).val.app (op q.left)
          (ambientModuleTensorSection.{u, v, w} f
            ((ambientModuleLift.{u, v, w} Y).obj M) E q (ULift.up b) (ULift.up s)) =
          ULift.up (moduleTensorSection f M E q b s) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace

/-! # Small étale module comparisons for arbitrary fibred groupoids

Source: Stacks Project, stacks-sheaves.tex, Tags 075D, 076R, 06WH and 0GQD
(blueprint: lem-sfb-fibred-fppf-space-module-comparisons).

Restriction is literal precomposition followed by the canonical scalar identification.
Comparisons are uniquely characterized on chart tensors, retaining all site universes.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option linter.checkUnivs false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

namespace CategoryTheory

variable {S : Scheme.{u}} {C : BasedCategory.{v, w} (Over S)}
  (hC : IsFibredInGroupoids C)

/-- The actual functor from étale charts to the total category.
Source: Stacks 076R (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def moduliSpaceEtaleTest {V : AlgebraicSpace S}
    (z : BasedFunctor (discreteModuli V.obj.obj) C) : V.EtaleSite ⥤ C.obj :=
  ObjectProperty.ι _ ⋙ z.toFunctor

/-- A based test identifies the two regular-function presheaves canonically.
Source: Stacks 076R (blueprint: lem-sfb-fibred-fppf-space-module-comparisons).
Proof: z commutes with the projections to Sch/S. Apply global sections and the
same ULift ring functor to this equality; both restrictions are scheme pullbacks. -/
theorem moduliSpaceEtaleRing_eq {V : AlgebraicSpace S}
    (z : BasedFunctor (discreteModuli V.obj.obj) C) :
    (ambientModuleRing.{u, v, w} V).obj =
      (moduliSpaceEtaleTest z).op ⋙ (moduliModuleRings C hC).obj := by
  sorry

/-- Precomposition of a module, with its canonical regular-function scalar action.
Source: Stacks 076R (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def moduliSpaceRestrictionPresheaf {V : AlgebraicSpace S}
    (z : BasedFunctor (discreteModuli V.obj.obj) C)
    (K : SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC)) :
    PresheafOfModules.{max (u + 1) v w} (ambientModuleRing.{u, v, w} V).obj :=
  (PresheafOfModules.pushforward
    (F := moduliSpaceEtaleTest z) (eqToHom (moduliSpaceEtaleRing_eq hC z))).obj K.val

/-- The restricted presheaf satisfies the small étale sheaf condition.
Source: Stacks 076R (blueprint: lem-sfb-fibred-fppf-space-module-comparisons).
Proof: an étale covering of a chart is fppf. The test sends that covering and its
scheme fibre-product overlaps to the same covering diagram in C. The sheaf
condition of K is therefore exactly the matching-family equalizer for this
restriction. Scalar restriction does not change its underlying abelian groups. -/
theorem moduliSpaceRestriction_isSheaf {V : AlgebraicSpace S}
    (z : BasedFunctor (discreteModuli V.obj.obj) C)
    (K : SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC)) :
    Presheaf.IsSheaf V.etaleTopology (moduliSpaceRestrictionPresheaf hC z K).presheaf := by
  sorry

/-- The small étale restriction, with the original sections and original maps.
Source: Stacks 076R (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def moduliSpaceRestriction {V : AlgebraicSpace S}
    (z : BasedFunctor (discreteModuli V.obj.obj) C)
    (K : SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC)) :
    AmbientModules.{u, v, w} V :=
  ⟨moduliSpaceRestrictionPresheaf hC z K, moduliSpaceRestriction_isSheaf hC z K⟩

/-- On morphisms the restriction is the original sectionwise module map.
Source: Stacks 076R (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def moduliSpaceRestrictionMap {V : AlgebraicSpace S}
    (z : BasedFunctor (discreteModuli V.obj.obj) C)
    {K L : SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC)} (f : K ⟶ L) :
    moduliSpaceRestriction hC z K ⟶ moduliSpaceRestriction hC z L :=
  ⟨(PresheafOfModules.pushforward
    (F := moduliSpaceEtaleTest z) (eqToHom (moduliSpaceEtaleRing_eq hC z))).map f.val⟩

/-- The arrow whose restriction defines the comparison on a chart tensor.
Source: Stacks 076R (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def moduliSpaceChartArrow {V W : AlgebraicSpace S} (a : V ⟶ W)
    (z : BasedFunctor (discreteModuli V.obj.obj) C)
    (t : BasedFunctor (discreteModuli W.obj.obj) C)
    (θ : ModuliTwoIso z ((discreteModuliMap a.hom.hom).comp t))
    (E : W.EtaleSite) (q : ModuleChart a E) :
    z.toFunctor.obj q.left.obj ⟶ t.toFunctor.obj E.obj :=
  θ.val.hom.app q.left.obj ≫ t.toFunctor.map q.hom

/-- A comparison is uniquely determined by the ordinary restriction formula on
all local chart tensors; this also fixes its adjoint on every chart projection.
Source: Stacks 075D, 076R (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def ModuliSpaceComparisonFormula {V W : AlgebraicSpace S} (a : V ⟶ W)
    (z : BasedFunctor (discreteModuli V.obj.obj) C)
    (t : BasedFunctor (discreteModuli W.obj.obj) C)
    (θ : ModuliTwoIso z ((discreteModuliMap a.hom.hom).comp t))
    (K : SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC))
    (c : (ambientModuleTensorPullback.{u, v, w} a).obj
      (moduliSpaceRestriction hC t K) ⟶ moduliSpaceRestriction hC z K) : Prop :=
  ∀ (E : W.EtaleSite) (q : ModuleChart a E)
    (b : (ambientModuleRing.{u, v, w} V).obj.obj (op q.left))
    (m : (moduliSpaceRestriction hC t K).val.obj (op E)),
    c.val.app (op q.left)
      (ambientModuleTensorSection.{u, v, w} a (moduliSpaceRestriction hC t K) E q b m) =
        b • @id ((moduliSpaceRestriction hC z K).val.obj (op q.left))
          (K.val.map (moduliSpaceChartArrow a z t θ E q).op m)

/-- Existence and uniqueness of the normalized comparison.
Source: Stacks 075D, 076R (blueprint: lem-sfb-fibred-fppf-space-module-comparisons).
Proof: to give the adjoint K_t to a_*K_z, send a section m on E to the compatible
family K(θ_T followed by t(r))(m), for every chart (T,r) over E. Naturality of θ
and contravariant functoriality of K give compatibility, while semilinearity gives
linearity over Γ(E,O_E). The chart-limit property gives a unique map on E;
its projections show compatibility with restrictions. Transpose by the specified
tensor adjunction. Linearity gives b tensor m maps to b K(α)(m). Conversely that
formula at b=1 specifies every projection of the adjoint, so limit uniqueness
and the adjunction imply uniqueness of the comparison. -/
theorem existsUnique_moduliSpaceComparison {V W : AlgebraicSpace S} (a : V ⟶ W)
    (z : BasedFunctor (discreteModuli V.obj.obj) C)
    (t : BasedFunctor (discreteModuli W.obj.obj) C)
    (θ : ModuliTwoIso z ((discreteModuliMap a.hom.hom).comp t))
    (K : SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC)) :
    ∃! c : (ambientModuleTensorPullback.{u, v, w} a).obj
      (moduliSpaceRestriction hC t K) ⟶ moduliSpaceRestriction hC z K,
      ModuliSpaceComparisonFormula hC a z t θ K c := by
  sorry

/-- The canonical comparison selected by its unique restriction-induced formula.
Source: Stacks 075D, 076R (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def moduliSpaceComparison {V W : AlgebraicSpace S} (a : V ⟶ W)
    (z : BasedFunctor (discreteModuli V.obj.obj) C)
    (t : BasedFunctor (discreteModuli W.obj.obj) C)
    (θ : ModuliTwoIso z ((discreteModuliMap a.hom.hom).comp t))
    (K : SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC)) :
    (ambientModuleTensorPullback.{u, v, w} a).obj (moduliSpaceRestriction hC t K) ⟶
      moduliSpaceRestriction hC z K :=
  (existsUnique_moduliSpaceComparison hC a z t θ K).choose

/-- A change of test by a two-isomorphism acts by the original restriction of K.
Source: Stacks 075D, 076R (blueprint: lem-sfb-fibred-fppf-space-module-comparisons).
Proof: on every chart use K applied to the component of σ. This is linear:
σ lies over an identity scheme map and hence acts identically on regular
functions. Naturality of σ and functoriality of K give the module-map square
for every chart restriction. These component maps give the desired morphism,
and its prescribed components give uniqueness. -/
theorem existsUnique_moduliSpaceTestChange {V : AlgebraicSpace S}
    (z z' : BasedFunctor (discreteModuli V.obj.obj) C) (σ : ModuliTwoIso z z')
    (K : SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC)) :
    ∃! f : moduliSpaceRestriction hC z' K ⟶ moduliSpaceRestriction hC z K,
      ∀ (T : V.EtaleSite) (m : (moduliSpaceRestriction hC z' K).val.obj (op T)),
        f.val.app (op T) m = K.val.map (σ.val.hom.app T.obj).op m := by
  sorry

/-- The uniquely normalized identification under a two-isomorphism of tests.
Source: Stacks 075D, 076R (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def moduliSpaceTestChange {V : AlgebraicSpace S}
    (z z' : BasedFunctor (discreteModuli V.obj.obj) C) (σ : ModuliTwoIso z z')
    (K : SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC)) :
    moduliSpaceRestriction hC z' K ⟶ moduliSpaceRestriction hC z K :=
  (existsUnique_moduliSpaceTestChange hC z z' σ K).choose

/-- The identity test two-isomorphism lies over the identity of every chart.
Source: Stacks 075D (blueprint: lem-sfb-fibred-fppf-space-module-comparisons).
Proof: the identity functor and its identity natural isomorphism project to
identity arrows on Sch/S; this is the identity HomLift. -/
theorem moduliSpaceIdentityTwoIso_over {V : AlgebraicSpace S}
    (z : BasedFunctor (discreteModuli V.obj.obj) C) (x : (discreteModuli V.obj.obj).obj) :
    C.p.IsHomLift (𝟙 ((discreteModuli V.obj.obj).p.obj x)) (𝟙 (z.toFunctor.obj x)) := by
  sorry

/-- Identity two-isomorphism of an algebraic-space test.
Source: Stacks 075D (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def moduliSpaceIdentityTwoIso {V : AlgebraicSpace S}
    (z : BasedFunctor (discreteModuli V.obj.obj) C) :
    ModuliTwoIso z ((discreteModuliMap (𝟙 V : V ⟶ V).hom.hom).comp z) :=
  ⟨Iso.refl _, moduliSpaceIdentityTwoIso_over z⟩

/-- The composite two-isomorphism lies over identity base maps.
Source: Stacks 075D (blueprint: lem-sfb-fibred-fppf-space-module-comparisons).
Proof: whiskering a two-isomorphism over the base leaves every component over
an identity. Composing with θ composes two identity base maps, again an identity. -/
theorem moduliSpaceCompositeTwoIso_over {V W B : AlgebraicSpace S}
    (a : V ⟶ W) (b : W ⟶ B)
    (z : BasedFunctor (discreteModuli V.obj.obj) C)
    (t : BasedFunctor (discreteModuli W.obj.obj) C)
    (r : BasedFunctor (discreteModuli B.obj.obj) C)
    (θ : ModuliTwoIso z ((discreteModuliMap a.hom.hom).comp t))
    (η : ModuliTwoIso t ((discreteModuliMap b.hom.hom).comp r))
    (x : (discreteModuli V.obj.obj).obj) :
    C.p.IsHomLift (𝟙 ((discreteModuli V.obj.obj).p.obj x))
      (θ.val.hom.app x ≫ η.val.hom.app ((discreteModuliMap a.hom.hom).toFunctor.obj x)) := by
  sorry

/-- The actual pasting (η a) θ of two comparison triangles.
Source: Stacks 075D (blueprint: lem-sfb-fibred-fppf-space-module-comparisons). -/
def moduliSpaceCompositeTwoIso {V W B : AlgebraicSpace S}
    (a : V ⟶ W) (b : W ⟶ B)
    (z : BasedFunctor (discreteModuli V.obj.obj) C)
    (t : BasedFunctor (discreteModuli W.obj.obj) C)
    (r : BasedFunctor (discreteModuli B.obj.obj) C)
    (θ : ModuliTwoIso z ((discreteModuliMap a.hom.hom).comp t))
    (η : ModuliTwoIso t ((discreteModuliMap b.hom.hom).comp r)) :
    ModuliTwoIso z ((discreteModuliMap (a ≫ b).hom.hom).comp r) :=
  ⟨θ.val ≪≫ isoWhiskerLeft (discreteModuliMap a.hom.hom).toFunctor η.val,
    moduliSpaceCompositeTwoIso_over a b z t r θ η⟩

/-- The ambient module universe contains every étale slice, so sheafification exists.
Source: Stacks 06WH, 0GQD (blueprint: lem-sfb-fibred-fppf-space-module-comparisons).
Proof: the objects and arrows of the slice lie in max(u+1,v,w). Apply the ordinary
additive sheafification by two plus constructions in that universe. -/
@[instance] theorem moduliSpaceOverHasWeakSheafify [UnivLE.{u + 1, m}]
    (V : AlgebraicSpace S) (T : V.EtaleSite) :
    HasWeakSheafify (V.etaleTopology.over T) AddCommGrpCat.{m} := by
  sorry

/-- On the same slices, sheafification inverts exactly locally bijective maps.
Source: Stacks 06WH, 0GQD (blueprint: lem-sfb-fibred-fppf-space-module-comparisons).
Proof: the units of the two plus constructions are locally bijective. Local
lifts and local equality glue uniquely, so locally bijective maps sheafify to
isomorphisms. Conversely use the locally bijective units and an inverse after
sheafification to obtain local lifting and local equality for the original map. -/
@[instance] theorem moduliSpaceOverWEqualsLocallyBijective [UnivLE.{u + 1, m}]
    (V : AlgebraicSpace S) (T : V.EtaleSite) :
    (V.etaleTopology.over T).WEqualsLocallyBijective AddCommGrpCat.{m} := by
  sorry

/-- All clauses of the restriction-induced comparison calculus, with canonical
unitor and compositor and the local-presentation quasi-coherence predicate.
Source: Stacks 075D, 076R, 06WH, 0GQD
(blueprint: lem-sfb-fibred-fppf-space-module-comparisons).

Proof:
1. Étale coverings are fppf. Precomposition with a test and the original module
sheaf equalizers give the small étale restriction; the scalar identifications
are the based-functor equalities of regular-function rings.
2. On E send m to the family K(α)(m) over all charts (T,r) of V over E, where
α is θ_T followed by t(r). Naturality of θ makes it a compatible cone and
semilinearity makes it linear. The specified chart limit gives the adjoint;
transposition gives exactly b tensor m maps to b K(α)(m).
3. For a module map f, naturality on α gives the comparison square. For identity
triangles α is the chart restriction, giving the tensor unitor. For two triangles
α for the composite equals β after α by naturality. On nested local tensors,
semilinearity turns x K(α)(y K(β)(m)) into x a-sharp(y) K(βα)(m), the normalized
tensor compositor formula. The adjoint chart projections determine maps uniquely,
so these identities hold globally, including changes of tests by two-isomorphisms.
4. On scheme tests the same adjoint is ordinary restriction along the corresponding
arrow of C. This is the scheme comparison because both project to precisely that
restriction on every chart. For étale a, pullback is restriction on the localized
étale sites and the comparison is K(θ_T), with inverse K(θ_T inverse).
5. If K is quasi-coherent, its scheme-test Zariski modules are quasi-coherent by
lem-sfb-stack-quasi-coherent-scheme-restriction. Their associated étale modules
are quasi-coherent by lem-trf-scheme-zariski-etale-quasi-coherent-equivalence.
Local presentations on each chart are presentations on the corresponding slice
of V_et, hence give quasi-coherence of the restriction.
6. For arbitrary a, take an étale scheme atlas E of W, and then a scheme atlas T
of V times_W E. The restricted comparison is the scheme comparison for T to E,
by composition and the étale identifications. It is invertible by scheme-test
quasi-coherence and compatibility of Zariski/étale tensor pullback. Its local
inverses agree on double overlaps and glue by the sheaf equalizer. This proves
invertibility globally without flatness, finiteness or algebraicity assumptions. -/
theorem fibred_fppf_space_module_comparisons :
    (∀ (V W : AlgebraicSpace S) (a : V ⟶ W)
      (z : BasedFunctor (discreteModuli V.obj.obj) C)
      (t : BasedFunctor (discreteModuli W.obj.obj) C)
      (θ : ModuliTwoIso z ((discreteModuliMap a.hom.hom).comp t))
      (K : SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC)),
      ModuliSpaceComparisonFormula hC a z t θ K (moduliSpaceComparison hC a z t θ K)) ∧
    (∀ (V W : AlgebraicSpace S) (a : V ⟶ W)
      (z : BasedFunctor (discreteModuli V.obj.obj) C)
      (t : BasedFunctor (discreteModuli W.obj.obj) C)
      (θ : ModuliTwoIso z ((discreteModuliMap a.hom.hom).comp t))
      (K L : SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC)) (f : K ⟶ L),
      (ambientModuleTensorPullback.{u, v, w} a).map (moduliSpaceRestrictionMap hC t f) ≫
        moduliSpaceComparison hC a z t θ L =
          moduliSpaceComparison hC a z t θ K ≫ moduliSpaceRestrictionMap hC z f) ∧
    (∀ (V : AlgebraicSpace S) (z : BasedFunctor (discreteModuli V.obj.obj) C)
      (K : SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC)),
      moduliSpaceComparison hC (𝟙 V) z z (moduliSpaceIdentityTwoIso z) K =
        (ambientTensorId.{u, v, w} V).hom.app (moduliSpaceRestriction hC z K)) ∧
    (∀ (V W B : AlgebraicSpace S) (a : V ⟶ W) (b : W ⟶ B)
      (z : BasedFunctor (discreteModuli V.obj.obj) C)
      (t : BasedFunctor (discreteModuli W.obj.obj) C)
      (r : BasedFunctor (discreteModuli B.obj.obj) C)
      (θ : ModuliTwoIso z ((discreteModuliMap a.hom.hom).comp t))
      (η : ModuliTwoIso t ((discreteModuliMap b.hom.hom).comp r))
      (K : SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC)),
      (ambientTensorComp.{u, v, w} a b).hom.app (moduliSpaceRestriction hC r K) ≫
        moduliSpaceComparison hC (a ≫ b) z r
          (moduliSpaceCompositeTwoIso a b z t r θ η) K =
        (ambientModuleTensorPullback.{u, v, w} a).map
          (moduliSpaceComparison hC b t r η K) ≫ moduliSpaceComparison hC a z t θ K) ∧
    (∀ (V W : AlgebraicSpace S) (a : V ⟶ W)
      (z : BasedFunctor (discreteModuli V.obj.obj) C)
      (t : BasedFunctor (discreteModuli W.obj.obj) C)
      (θ : ModuliTwoIso z ((discreteModuliMap a.hom.hom).comp t))
      (K : SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC)),
      AlgebraicSpace.IsEtale a.hom.hom → IsIso (moduliSpaceComparison hC a z t θ K)) ∧
    (∀ (V W : AlgebraicSpace S) (a : V ⟶ W)
      (z : BasedFunctor (discreteModuli V.obj.obj) C)
      (t : BasedFunctor (discreteModuli W.obj.obj) C)
      (θ : ModuliTwoIso z ((discreteModuliMap a.hom.hom).comp t))
      (K : SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC))
      (E : W.EtaleSite) (q : ModuleChart a E)
      (m : (moduliSpaceRestriction hC t K).val.obj (op E)),
      ((ambientModuleDirectImageModel.{u, v, w} a).projection
        (moduliSpaceRestriction hC z K) E).app (op q)
        ((((ambientModuleTensorAdjunction.{u, v, w} a).homEquiv
          (moduliSpaceRestriction hC t K) (moduliSpaceRestriction hC z K))
            (moduliSpaceComparison hC a z t θ K)).val.app (op E) m) =
          K.val.map (moduliSpaceChartArrow a z t θ E q).op m) ∧
    (∀ (V W : AlgebraicSpace S) (a : V ⟶ W)
      (z z' : BasedFunctor (discreteModuli V.obj.obj) C)
      (t t' : BasedFunctor (discreteModuli W.obj.obj) C)
      (σ : ModuliTwoIso z z') (τ : ModuliTwoIso t t')
      (θ : ModuliTwoIso z ((discreteModuliMap a.hom.hom).comp t))
      (θ' : ModuliTwoIso z' ((discreteModuliMap a.hom.hom).comp t'))
      (K : SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC)),
      θ.val.hom ≫ whiskerLeft (discreteModuliMap a.hom.hom).toFunctor τ.val.hom =
        σ.val.hom ≫ θ'.val.hom →
      (ambientModuleTensorPullback.{u, v, w} a).map
        (moduliSpaceTestChange hC t t' τ K) ≫ moduliSpaceComparison hC a z t θ K =
      moduliSpaceComparison hC a z' t' θ' K ≫ moduliSpaceTestChange hC z z' σ K) ∧
    (∀ (K : SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC)),
      K.IsQuasicoherent →
      (∀ (V : AlgebraicSpace S) (z : BasedFunctor (discreteModuli V.obj.obj) C),
        SheafOfModules.IsQuasicoherent.{max (u + 1) v w, u, u + 1}
          (moduliSpaceRestriction hC z K)) ∧
      ∀ (V W : AlgebraicSpace S) (a : V ⟶ W)
        (z : BasedFunctor (discreteModuli V.obj.obj) C)
        (t : BasedFunctor (discreteModuli W.obj.obj) C)
        (θ : ModuliTwoIso z ((discreteModuliMap a.hom.hom).comp t)),
        IsIso (moduliSpaceComparison hC a z t θ K)) := by
  sorry

end CategoryTheory
