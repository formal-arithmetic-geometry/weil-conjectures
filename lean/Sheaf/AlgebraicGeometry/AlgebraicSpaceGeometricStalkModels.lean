module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedPullbackModels
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Sheaf.AlgebraicGeometry.SpacePointedEtaleNeighbourhoodsCofiltered
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Normalized geometric stalks on algebraic spaces
Source: Stacks Project, Tags 03G7 and 03D7.
(blueprint: def-sfb-space-geometric-stalk-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.AlgebraicSpace.SingleComplex
variable {S : Scheme.{u}}

/-- A pointed affine étale neighbourhood in the existing small affine basis.
Source: Stacks 03ED, 03G7 (blueprint: def-sfb-space-geometric-stalk-models). -/
abbrev Neighbourhood {X : AlgebraicSpace S} (G : Over S)
    (x : yoneda.obj G ⟶ X.obj.obj) :=
  StructuredArrow (CostructuredArrow.mk x)
    (X.smallEtaleInclusion ⋙ ObjectProperty.ι _)

/-- Forget the geometric lift but retain the actual scheme chart.
Source: Stacks 03ED (blueprint: def-sfb-space-geometric-stalk-models). -/
def neighbourhoodChart {X : AlgebraicSpace S} {G : Over S}
    {x : yoneda.obj G ⟶ X.obj.obj} : Neighbourhood G x ⥤ X.EtaleSite :=
  StructuredArrow.proj _ _ ⋙ X.smallEtaleInclusion

/-- The actual regular-function diagram of pointed affine étale neighbourhoods.
Source: Stacks 03G7 (blueprint: def-sfb-space-geometric-stalk-models). -/
def ringDiagram {X : AlgebraicSpace S} {G : Over S}
    (x : yoneda.obj G ⟶ X.obj.obj) : (Neighbourhood G x)ᵒᵖ ⥤ CommRingCat.{u} :=
  (neighbourhoodChart (x := x) ⋙ X.etaleForget).op ⋙ Scheme.Γ

/-- The section diagram of an original module sheaf on the pointed affine basis.
Source: Stacks 03G7 (blueprint: def-sfb-space-geometric-stalk-models). -/
def moduleDiagram {X : AlgebraicSpace S} {G : Over S}
    (x : yoneda.obj G ⟶ X.obj.obj) (M : X.Modules) :
    (Neighbourhood G x)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (neighbourhoodChart (x := x)).op ⋙ M.val.presheaf

/-- Normalized ring and module stalks: both are the colimits of actual sections.
The scalar equation specifies the module structure, and the naturality equation
specifies the functor on maps. Thus all data are determined up to the unique
isomorphism preserving germs; this is a universal-property construction.
Source: Stacks 03G7, 03D2 (blueprint: def-sfb-space-geometric-stalk-models). -/
structure StalkModel {X : AlgebraicSpace S} {G : Over S}
    (x : yoneda.obj G ⟶ X.obj.obj) where
  ringCocone : Cocone (ringDiagram x)
  ringIsColimit : IsColimit ringCocone
  modules : X.Modules ⥤ ModuleCat.{u} ringCocone.pt
  additive : modules.Additive
  germs (M : X.Modules) : moduleDiagram x M ⟶
    (Functor.const _).obj ((forget₂ _ AddCommGrpCat).obj (modules.obj M))
  moduleIsColimit (M : X.Modules) : IsColimit (Cocone.mk _ (germs M))
  map_germ {M N : X.Modules} (a : M ⟶ N) (V : Neighbourhood G x)
      (m : M.val.obj (op ((neighbourhoodChart (x := x)).obj V))) :
    modules.map a ((germs M).app (op V) m) =
      (germs N).app (op V) (a.val.app _ m)
  smul_germ (M : X.Modules) (V : Neighbourhood G x)
      (r : (ringDiagram x).obj (op V))
      (m : M.val.obj (op ((neighbourhoodChart (x := x)).obj V))) :
    (germs M).app (op V) (r • m) =
      (@id ringCocone.pt ((ringCocone.ι.app (op V)) r)) •
        (@id (modules.obj M) ((germs M).app (op V) m))

attribute [instance] StalkModel.additive

private theorem neighbourhood_cofiltered {X : AlgebraicSpace S} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) :
    IsCofiltered (Neighbourhood (Over.mk s) x) := by
  let := (pointedEtale_small_cofiltered X Ω s x).2.1
  let : X.smallEtaleInclusion.Full := by
    unfold smallEtaleInclusion
    infer_instance
  let : X.smallEtaleInclusion.Faithful := by
    unfold smallEtaleInclusion
    infer_instance
  let F := StructuredArrow.pre (CostructuredArrow.mk x)
    X.smallEtaleInclusion (ObjectProperty.ι _)
  apply IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful F
  intro V
  let a : Spec (.of Ω) ⟶ V.right.obj.left.left := V.hom.left.left
  obtain ⟨U, hU, haU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := V.right.obj.left.left) (x := a default) (U := ⊤) (by simp)
  have hr : Set.range a ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z default]
    simpa using haU
  let W : X.AffineEtaleCharts := ⟨(X.schemeOpens V.right).obj U, hU⟩
  let l : Over.mk s ⟶ W.obj.obj.left :=
    Over.homMk (IsOpenImmersion.lift U.ι a hr) (by
      change IsOpenImmersion.lift U.ι a hr ≫ (U.ι ≫ V.right.obj.left.hom) = s
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact Over.w V.hom.left)
  let q : W.obj ⟶ V.right := ObjectProperty.homMk
    (CostructuredArrow.homMk (Over.homMk U.ι rfl) rfl)
  let n : StructuredArrow (CostructuredArrow.mk x)
      ((ObjectProperty.ι _ : X.AffineEtaleCharts ⥤ X.EtaleSite) ⋙ ObjectProperty.ι _) :=
    StructuredArrow.mk (Y := W) (CostructuredArrow.homMk l (by
      change yoneda.map l ≫ (yoneda.map (Over.homMk U.ι rfl) ≫ V.right.obj.hom) = x
      rw [← Category.assoc, ← Functor.map_comp]
      have hl : l ≫ Over.homMk U.ι rfl = V.hom.left := by
        apply Over.OverMorphism.ext
        exact IsOpenImmersion.lift_fac _ _ _
      rw [hl]
      exact V.hom.w))
  let e := ((equivSmallModel X.AffineEtaleCharts).unitIso.app W).symm
  let e' := (ObjectProperty.ι _ : X.AffineEtaleCharts ⥤ X.EtaleSite).mapIso e
  let k := (equivSmallModel X.AffineEtaleCharts).functor.obj W
  let n' : Neighbourhood (Over.mk s) x := StructuredArrow.mk (Y := k)
    (n.hom ≫ (ObjectProperty.ι _).map e'.inv)
  refine ⟨n', ⟨StructuredArrow.homMk (e'.hom ≫ q) ?_⟩⟩
  change (n.hom ≫ (ObjectProperty.ι _).map e'.inv) ≫
    (ObjectProperty.ι _).map (e'.hom ≫ q) = V.hom
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_assoc]
  apply CostructuredArrow.hom_ext
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

/-- Pointed-neighbourhood colimits realize the normalized stalk universal properties.
Source: Stacks 03G7, 03D2 (blueprint: def-sfb-space-geometric-stalk-models).
Proof: the pointed affine étale neighbourhood category is cofiltered: lift the point
to an atlas, refine to affine opens, and equalize two chart maps on an étale
neighbourhood. Its objects and arrows are u-small. Take the filtered ring colimit
and the filtered additive-group colimits. Simultaneous representatives define
scalar multiplication, independently of refinement. Module maps act on these same
representatives, so give an additive functor. Colimit uniqueness proves that all
these data are uniquely determined up to germ-preserving isomorphism. -/
theorem stalkModel_nonempty {X : AlgebraicSpace S} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) : Nonempty (StalkModel x) := by
  let := neighbourhood_cofiltered s x
  let : InitiallySmall.{u} (Neighbourhood (Over.mk s) x) :=
    initiallySmall_of_essentiallySmall _
  let := hasColimitsOfShape_of_finallySmall (J := (Neighbourhood (Over.mk s) x)ᵒᵖ)
    (C := CommRingCat.{u})
  let := hasColimitsOfShape_of_finallySmall (J := (Neighbourhood (Over.mk s) x)ᵒᵖ)
    (C := AddCommGrpCat.{u})
  let c := colimit.cocone (ringDiagram x)
  let hc := isColimitOfPreserves (forget₂ CommRingCat RingCat) (colimit.isColimit
    (ringDiagram x))
  let D := SheafOfModules.forget X.structureSheaf ⋙
    PresheafOfModules.pushforward₀ (neighbourhoodChart (x := x)) _
  let L := PresheafOfModules.colimitFunctor hc
  have : D.Additive := by
    constructor
    intro M N f g
    ext U m
    rfl
  have : (PresheafOfModules.constFunctor
      ((forget₂ CommRingCat RingCat).mapCocone c)).Additive := by
    constructor
    intro M N f g
    ext U m
    rfl
  have : L.Additive := (PresheafOfModules.colimitAdjunction hc).left_adjoint_additive
  refine ⟨{
    ringCocone := c
    ringIsColimit := colimit.isColimit _
    modules := D ⋙ L
    additive := inferInstance
    germs := fun M ↦ (colimit.cocone (moduleDiagram x M)).ι
    moduleIsColimit := fun M ↦ colimit.isColimit _
    map_germ := ?_
    smul_germ := ?_ }⟩
  · intro M N a V m
    exact PresheafOfModules.ModuleColimit.map_apply hc _ _ (D.map a) m
  · intro M V r m
    exact (PresheafOfModules.ModuleColimit.smul_eq hc
      (colimit.isColimit ((D.obj M).presheaf)) r m).symm

/-- The normalized stalk model selected by its ring and module colimit properties.
Source: Stacks 03G7 (blueprint: def-sfb-space-geometric-stalk-models). -/
def stalkModel {X : AlgebraicSpace S} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) : StalkModel x :=
  Classical.choice (stalkModel_nonempty s x)

/-- The geometric local ring, a pointed-neighbourhood colimit.
Source: Stacks 03G7 (blueprint: def-sfb-space-geometric-stalk-models). -/
abbrev stalkRing {X : AlgebraicSpace S} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) :=
  (stalkModel s x).ringCocone.pt

/-- The geometric module stalk of the existing small affine model.
Source: Stacks 03G7 (blueprint: def-sfb-space-geometric-stalk-models). -/
def stalk {X : AlgebraicSpace S} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) :
    X.SmallModules ⥤ ModuleCat.{u} (stalkRing s x) :=
  X.smallModuleEquivalence.inverse ⋙ (stalkModel s x).modules

/-- Additivity of the small-model geometric stalk.
Source: Stacks 03G7 (blueprint: def-sfb-space-geometric-stalk-models).
Proof: the inverse of an additive equivalence of module categories preserves sums,
and the normalized stalk functor does so on every germ. -/
@[instance] theorem stalk_additive {X : AlgebraicSpace S} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) : (stalk s x).Additive := by
  let : X.smallModuleEquivalence.functor.Additive :=
    { map_add := fun {_ _} _ _ ↦ by ext U m; rfl }
  unfold stalk
  infer_instance

/-- Compatibility of a scheme map between two pointed charts with a space morphism.
Source: Stacks 03G7 (blueprint: def-sfb-space-geometric-stalk-models). -/
def Compatible {X Y : AlgebraicSpace S} (f : X ⟶ Y) {G : Over S}
    {x : yoneda.obj G ⟶ X.obj.obj}
    (U : Neighbourhood G x) (V : Neighbourhood G (x ≫ f.hom.hom))
    (a : ((neighbourhoodChart (x := x)).obj U).obj.left ⟶
      ((neighbourhoodChart (x := x ≫ f.hom.hom)).obj V).obj.left) : Prop :=
  yoneda.map a ≫ ((neighbourhoodChart (x := x ≫ f.hom.hom)).obj V).obj.hom =
    ((neighbourhoodChart (x := x)).obj U).obj.hom ≫ f.hom.hom ∧
    U.hom.left ≫ a = V.hom.left

/-- The stalk ring map is uniquely specified on compatible pointed-chart germs.
Source: Stacks 03G7 (blueprint: def-sfb-space-geometric-stalk-models).
Proof: every target pointed chart pulls back to an étale neighbourhood on the source
space. Lift its geometric point to an affine scheme chart and refine in the small
basis. Pullback of regular functions then gives a compatible cocone. Two refinements
have a common refinement, so the cocone is independent of them. The ring colimit
property gives the unique homomorphism with the displayed equations. -/
theorem stalkMap_existsUnique {X Y : AlgebraicSpace S} (f : X ⟶ Y) {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) :
    ∃! h : stalkRing s (x ≫ f.hom.hom) →+* stalkRing s x,
      ∀ (U : Neighbourhood (Over.mk s) x)
        (V : Neighbourhood (Over.mk s) (x ≫ f.hom.hom))
        (a : ((neighbourhoodChart (x := x)).obj U).obj.left ⟶
          ((neighbourhoodChart (x := x ≫ f.hom.hom)).obj V).obj.left),
        Compatible f U V a →
        h.comp ((stalkModel s (x ≫ f.hom.hom)).ringCocone.ι.app (op V)).hom =
          ((stalkModel s x).ringCocone.ι.app (op U)).hom.comp (Scheme.Γ.map a.left.op).hom :=
  by sorry

/-- The ring stalk map, selected from its uniquely specified germ equations.
Source: Stacks 03G7 (blueprint: def-sfb-space-geometric-stalk-models). -/
def stalkMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) :
    stalkRing s (x ≫ f.hom.hom) →+* stalkRing s x :=
  Classical.choose (stalkMap_existsUnique f s x)

/-- A compatible pointed chart, viewed as a chart of the relative direct image.
Source: Stacks 03G8 (blueprint: def-sfb-space-geometric-stalk-models). -/
def relativeChart {X Y : AlgebraicSpace S} (f : X ⟶ Y) {G : Over S}
    {x : yoneda.obj G ⟶ X.obj.obj}
    (U : Neighbourhood G x) (V : Neighbourhood G (x ≫ f.hom.hom))
    (a : ((neighbourhoodChart (x := x)).obj U).obj.left ⟶
      ((neighbourhoodChart (x := x ≫ f.hom.hom)).obj V).obj.left)
    (ha : Compatible f U V a) :
    ModuleChart f ((neighbourhoodChart (x := x ≫ f.hom.hom)).obj V) :=
  CostructuredArrow.mk (CostructuredArrow.homMk a ha.1)

/-- The normalized pullback-stalk comparison, characterized on local tensors.
Source: Stacks 03G7, 03D7, equation-bc before 0DKG
(blueprint: def-sfb-space-geometric-stalk-models). -/
def PullbackStalkFormula {X Y : AlgebraicSpace S} (f : X ⟶ Y) {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj)
    (e : (stalkModel s (x ≫ f.hom.hom)).modules ⋙
        ModuleCat.extendScalars (stalkMap f s x) ≅
      moduleTensorPullback f ⋙ (stalkModel s x).modules) : Prop :=
  ∀ (M : Y.Modules) (U : Neighbourhood (Over.mk s) x)
    (V : Neighbourhood (Over.mk s) (x ≫ f.hom.hom))
    (a : ((neighbourhoodChart (x := x)).obj U).obj.left ⟶
      ((neighbourhoodChart (x := x ≫ f.hom.hom)).obj V).obj.left)
    (ha : Compatible f U V a)
    (b : (ringDiagram x).obj (op U))
    (m : M.val.obj (op ((neighbourhoodChart (x := x ≫ f.hom.hom)).obj V))),
    (e.hom.app M)
      ((@id (stalkRing s x) ((stalkModel s x).ringCocone.ι.app (op U) b))
        ⊗ₜ[stalkRing s (x ≫ f.hom.hom),stalkMap f s x]
          (@id ((stalkModel s (x ≫ f.hom.hom)).modules.obj M)
            (((stalkModel s (x ≫ f.hom.hom)).germs M).app (op V) m))) =
      ((stalkModel s x).germs ((moduleTensorPullback f).obj M)).app (op U)
        (moduleTensorSection f M ((neighbourhoodChart (x := x ≫ f.hom.hom)).obj V)
          (relativeChart f U V a ha) b m)

/-- The germ-normalized pullback-stalk isomorphism exists and is unique.
Source: Stacks 03G7, 03D7 (blueprint: def-sfb-space-geometric-stalk-models).
Proof: send b tensor germ(m) to the germ of the local tensor defined using the
adjunction unit of the specified tensor pullback. Refinement makes this balanced
and independent of representatives. The same description of inverse image by
local representatives gives the inverse. Pure tensors generate the scalar extension,
so the formula fixes the map and its inverse uniquely, naturally in M. -/
theorem pullbackStalk_existsUnique {X Y : AlgebraicSpace S} (f : X ⟶ Y) {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) :
    ∃! e : (stalkModel s (x ≫ f.hom.hom)).modules ⋙
        ModuleCat.extendScalars (stalkMap f s x) ≅
      moduleTensorPullback f ⋙ (stalkModel s x).modules,
      PullbackStalkFormula f s x e := by
  sorry

/-- The original-site normalized pullback-stalk comparison.
Source: Stacks 03G7 (blueprint: def-sfb-space-geometric-stalk-models). -/
def pullbackStalkIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) :=
  Classical.choose (pullbackStalk_existsUnique f s x)

/-- Transport the germ-normalized comparison through the affine-basis equivalence.
Source: Stacks 03G7, 039Z (blueprint: def-sfb-space-geometric-stalk-models). -/
def smallPullbackStalkIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) :
    stalk s (x ≫ f.hom.hom) ⋙ ModuleCat.extendScalars (stalkMap f s x) ≅
      pullback f ⋙ stalk s x :=
  Functor.isoWhiskerLeft Y.smallModuleEquivalence.inverse (pullbackStalkIso f s x) ≪≫
    Functor.isoWhiskerLeft (Y.smallModuleEquivalence.inverse ⋙ moduleTensorPullback f)
      (Functor.isoWhiskerRight X.smallModuleEquivalence.unitIso (stalkModel s x).modules)

/-- A geometric germ of a small-model section, transported to the original site.
Source: Stacks 03G7, 039Z (blueprint: def-sfb-space-geometric-stalk-models). -/
def germ {X : AlgebraicSpace S} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj)
    (M : X.SmallModules) (V : Neighbourhood (Over.mk s) x)
    (m : M.val.obj (op V.right)) : (stalk s x).obj M :=
  ((stalkModel s x).germs (X.smallModuleEquivalence.inverse.obj M)).app (op V)
    ((X.smallModuleEquivalence.counitIso.inv.app M).val.app (op V.right) m)

end AlgebraicGeometry.AlgebraicSpace.SingleComplex
