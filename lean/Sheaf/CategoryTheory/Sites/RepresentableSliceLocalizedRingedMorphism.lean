module

public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.PullbackYoneda
public import Sheaf.CategoryTheory.RingedSheafSliceAdjunction
public import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral
public import Sheaf.CategoryTheory.Sites.LocalizedSetPullbackComparison
import all Sheaf.CategoryTheory.Sites.LocalizedSetPullbackComparison
public import Sheaf.CategoryTheory.Sites.LocalizedModulePullbackComparison
import Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.Limits
import all Sheaf.CategoryTheory.ElementSiteDescent
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import all Sheaf.CategoryTheory.ContinuousRingedToposModuleDirectImage

/-!
# Representable slices and localized ringed morphisms

Source: Stacks Project, Sites, Tags 03CF and 04D3; Modules on Sites,
Tags 04J0, 04IF and 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism).

The chart uses the actual elements of the represented sheaf. Its coefficient map
is identity on each ring of sections. Thus the module comparison concerns the
same restricted rings, including when the structural map is not invertible.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite Functor

namespace CategoryTheory

/-- The continuous direct image of set sheaves has a left adjoint.
Source: Mathlib's sheaf pullback construction
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
instance (priority := 30000) representableSlice_setRightAdjoint
    {E F : Type u} [SmallCategory E] [SmallCategory F]
    (T : GrothendieckTopology E) (T' : GrothendieckTopology F)
    (P : E ⥤ F) [P.IsContinuous T T'] :
    (P.sheafPushforwardContinuous (Type u) T T').IsRightAdjoint := inferInstance

/-- The continuous direct image of module sheaves has a left adjoint.
Source: Mathlib's continuous module pullback construction
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
instance (priority := 30000) representableSlice_moduleRightAdjoint
    {E F : Type u} [SmallCategory E] [SmallCategory F]
    (T : GrothendieckTopology E) (T' : GrothendieckTopology F)
    (P : E ⥤ F) [P.IsContinuous T T']
    (Q : Sheaf T RingCat.{u}) (Q' : Sheaf T' RingCat.{u})
    (phi : Q ⟶ (P.sheafPushforwardContinuous RingCat T T').obj Q') :
    (SheafOfModules.pushforward.{u} (F := P) (J := T) (K := T') phi).IsRightAdjoint :=
  inferInstance

/-- Composition with the forgetful functor preserves sheaves.
Source: Mathlib's preservation-of-limits instance
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
instance (priority := 30000) representableSlice_composeRing
    {E : Type u} [SmallCategory E] (T : GrothendieckTopology E) :
    T.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance

/-- Composition with the forgetful functor preserves sheaves.
Source: Mathlib's preservation-of-limits instance
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
instance (priority := 30000) representableSlice_composeCommSets
    {E : Type u} [SmallCategory E] (T : GrothendieckTopology E) :
    T.HasSheafCompose (forget CommRingCat.{u}) := inferInstance

/-- Composition with the forgetful functor preserves sheaves.
Source: Mathlib's preservation-of-limits instance
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
instance (priority := 30000) representableSlice_composeRingSets
    {E : Type u} [SmallCategory E] (T : GrothendieckTopology E) :
    T.HasSheafCompose (forget RingCat.{u}) := inferInstance

/-- Composition with the forgetful functor preserves sheaves.
Source: Mathlib's preservation-of-limits instance
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
instance (priority := 30000) representableSlice_composeAddSets
    {E : Type u} [SmallCategory E] (T : GrothendieckTopology E) :
    T.HasSheafCompose (forget AddCommGrpCat.{u}) := inferInstance

attribute [local instance 20000] hasSheafCompose_of_preservesLimitsOfSize
attribute [local irreducible] mateEquiv

/-- The canonical chart from the localized site to the element site of a represented sheaf.
Source: Stacks Tags 03CF, 04D3 and 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableRingedSliceChart
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} [J.Subcanonical]
    (V : C) {A : Sheaf J (Type u)} (e : A ≅ J.uliftYoneda.{u}.obj V) :
    Over V ⥤ A.obj.Elementsᵒᵖ where
  obj X := op ⟨op X.left, e.inv.hom.app (op X.left) (ULift.up X.hom)⟩
  map {X Y} b := Quiver.Hom.op ⟨b.left.op, by
    have h := e.inv.hom.naturality_apply b.left.op
      (show (J.uliftYoneda.{u}.obj V).obj.obj (op Y.left) from ULift.up Y.hom)
    change e.inv.hom.app (op X.left) (ULift.up (b.left ≫ Y.hom)) = _ at h
    rw [Over.w b] at h
    exact h.symm⟩

/-- The recorded representable isomorphism with its source written explicitly.
Source: Stacks Tag 04D3
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableRingedSliceImageIso
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.Subcanonical] [K.Subcanonical] (U : C ⥤ D) [U.IsContinuous J K] (V : C) :
    (U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V) ≅
      K.uliftYoneda.{u}.obj (U.obj V) :=
  (U.sheafAdjunctionContinuous (Type u) J K).uliftYonedaCompIso.app V

/-- The represented chart is a continuous equivalence of the indicated sites.
Source: Stacks Tags 03CF, 04D3 and 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism).
Proof: the inverse sends (W,s) to W equipped with the arrow e(s). Arrows are the
same commuting triangles by naturality of e. The two composites are identity up to
the inverse equations for e. Covering sieves agree because both topologies are
induced from J by forgetting the displayed element or the arrow to V. -/
theorem representableRingedSliceChart_properties
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} [J.Subcanonical]
    (V : C) {A : Sheaf J (Type u)} (e : A ≅ J.uliftYoneda.{u}.obj V) :
    (representableRingedSliceChart V e).IsEquivalence ∧
      (representableRingedSliceChart V e).IsContinuous (J.over V) (elementTopology A) := by
  let F := representableRingedSliceChart V e
  have : F.Faithful := ⟨by
    intro X Y f g h
    apply Over.OverMorphism.ext
    exact congrArg (fun k ↦ k.unop.1.unop) h⟩
  have : F.Full := ⟨by
    intro X Y g
    have h := e.inv.hom.naturality_apply
      (show op Y.left ⟶ op X.left from g.unop.1)
      (show (J.uliftYoneda.{u}.obj V).obj.obj (op Y.left) from ULift.up Y.hom)
    change e.inv.hom.app (op X.left) (ULift.up (g.unop.1.unop ≫ Y.hom)) =
      A.obj.map g.unop.1 (e.inv.hom.app (op Y.left) (ULift.up Y.hom)) at h
    have hg : A.obj.map g.unop.1
        (e.inv.hom.app (op Y.left) (ULift.up Y.hom)) =
        e.inv.hom.app (op X.left) (ULift.up X.hom) := g.unop.2
    have hh := (ConcreteCategory.bijective_of_isIso
      (e.inv.hom.app (op X.left))).1 (h.trans hg)
    refine ⟨Over.homMk g.unop.1.unop (congrArg ULift.down hh), ?_⟩
    apply Quiver.Hom.unop_inj
    apply Subtype.ext
    rfl⟩
  have : F.EssSurj := ⟨by
    intro X
    let Y : Over V := Over.mk (e.hom.hom.app X.unop.1 X.unop.2).down
    refine ⟨Y, ⟨(CategoryOfElements.isoMk X.unop (F.obj Y).unop (Iso.refl _) ?_).op⟩⟩
    change A.obj.map (𝟙 _) X.unop.2 =
      e.inv.hom.app X.unop.1 (ULift.up (e.hom.hom.app X.unop.1 X.unop.2).down)
    rw [Functor.map_id_apply]
    exact (congrArg (fun k ↦ k.hom.app X.unop.1 X.unop.2) e.hom_inv_id).symm⟩
  have hF : F.IsEquivalence := {}
  refine ⟨hF, (Functor.isContinuous_iff_coverPreserving).mpr ?_⟩
  constructor
  intro X S hS
  rw [(element_site_descent A).1]
  apply Functor.mem_restrictedTopology_of_functorPushforward_mem
  rw [← Sieve.functorPushforward_comp]
  exact hS

/-- Continuity of the canonical chart, as supplied by its site identification.
Source: Stacks Tag 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
instance representableRingedSliceChartContinuous
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} [J.Subcanonical]
    (V : C) {A : Sheaf J (Type u)} (e : A ≅ J.uliftYoneda.{u}.obj V) :
    (representableRingedSliceChart V e).IsContinuous (J.over V) (elementTopology A) :=
  (representableRingedSliceChart_properties V e).2

/-- The existing continuity of localization, exposed for the displayed comparison square.
Source: Stacks Tag 03CF
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
instance representableSlicePostContinuous
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (U : C ⥤ D) [U.IsContinuous J K] (V : C) :
    (Over.post (X := V) U).IsContinuous (J.over V) (K.over (U.obj V)) :=
  overPost_isContinuous J K U V

/-- Restriction through the chart has exactly the original coefficient ring at each object.
Source: Stacks Tags 04J0, 04IF and 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableRingedSliceCoefficientMap
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} [J.Subcanonical]
    (R : Sheaf J RingCat.{u}) (V : C) {A : Sheaf J (Type u)}
    (e : A ≅ J.uliftYoneda.{u}.obj V)
    :
    R.over V ⟶ ((representableRingedSliceChart V e).sheafPushforwardContinuous
      RingCat.{u} (J.over V) (elementTopology A)).obj (elementRing R A) :=
  ObjectProperty.homMk {
    app T := 𝟙 (R.obj.obj (op T.unop.left))
    naturality X Y b := by
      change R.obj.map b.unop.left.op ≫ 𝟙 _ = 𝟙 _ ≫ R.obj.map b.unop.left.op
      simp }


/-- The identity comparison between the two restrictions of a set sheaf.
Source: Stacks Tags 03CF and 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableRingedSliceRestrictionIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} [J.Subcanonical]
    (V : C) {A : Sheaf J (Type u)} (e : A ≅ J.uliftYoneda.{u}.obj V)
    :
    elementSheafPullback A ⋙
        (representableRingedSliceChart V e).sheafPushforwardContinuous (Type u)
          (J.over V) (elementTopology A) ≅ J.overPullback (Type u) V :=
  NatIso.ofComponents (fun _ ↦ ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun _ ↦ Iso.refl _) (by intros; rfl))) (by intros; rfl)

/-- The identity comparison between the two restrictions of a module sheaf.
Source: Stacks Tags 04J0 and 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableRingedSliceModuleRestrictionIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} [J.Subcanonical]
    (R : Sheaf J RingCat.{u}) (V : C) {A : Sheaf J (Type u)}
    (e : A ≅ J.uliftYoneda.{u}.obj V)
    :
    elementModulePullback R A ⋙
        SheafOfModules.pushforward.{u} (representableRingedSliceCoefficientMap R V e) ≅
      SheafOfModules.overFunctor.{u} R V :=
  NatIso.ofComponents (fun _ ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _))) (by intros; rfl)

/-- Set restriction through the represented chart.
Source: Stacks Tag 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
abbrev representableRingedSliceSets
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} [J.Subcanonical]
    (V : C) {A : Sheaf J (Type u)} (e : A ≅ J.uliftYoneda.{u}.obj V) :=
  (representableRingedSliceChart V e).sheafPushforwardContinuous (Type u)
    (J.over V) (elementTopology A)

/-- Module restriction through the represented chart, using the identity coefficient map.
Source: Stacks Tag 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
abbrev representableRingedSliceModules
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} [J.Subcanonical]
    (R : Sheaf J RingCat.{u}) (V : C) {A : Sheaf J (Type u)}
    (e : A ≅ J.uliftYoneda.{u}.obj V) :=
  SheafOfModules.pushforward.{u} (representableRingedSliceCoefficientMap R V e)

/-- The map of element sites induced by the global adjunction unit at `h_V`.
Source: Stacks Tags 03CF, 04IF and 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceElementFunctor
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} [J.Subcanonical]
    (U : C ⥤ D) [U.IsContinuous J K] (V : C) :
    (J.uliftYoneda.{u}.obj V).obj.Elementsᵒᵖ ⥤
      ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)).obj.Elementsᵒᵖ where
  obj X := op ⟨U.op.obj X.unop.1,
    ((U.sheafAdjunctionContinuous (Type u) J K).unit.app
      (J.uliftYoneda.{u}.obj V)).hom.app X.unop.1 X.unop.2⟩
  map {X Y} b := Quiver.Hom.op ⟨U.op.map b.unop.1, by
    have h := ((U.sheafAdjunctionContinuous (Type u) J K).unit.app
      (J.uliftYoneda.{u}.obj V)).hom.naturality_apply b.unop.1 Y.unop.2
    dsimp only [Functor.id_obj] at h
    exact (h.symm.trans (congrArg _ b.unop.2))⟩
  map_id X := by
    apply Quiver.Hom.unop_inj
    apply Subtype.ext
    exact U.op.map_id _
  map_comp b c := by
    apply Quiver.Hom.unop_inj
    apply Subtype.ext
    exact U.op.map_comp _ _

private theorem representableSlice_unit
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.Subcanonical] [K.Subcanonical]
    (U : C ⥤ D) [U.IsContinuous J K] (V W : C) (b : W ⟶ V) :
    ((U.sheafAdjunctionContinuous (Type u) J K).unit.app
      (J.uliftYoneda.{u}.obj V)).hom.app (op W) (ULift.up b) =
      (representableRingedSliceImageIso (J := J) (K := K) U V).inv.hom.app
        (op (U.obj W)) (ULift.up (U.map b)) := by
  change _ = ((U.sheafAdjunctionContinuous (Type u) J K).uliftYonedaCompHom V).hom.app
    (op (U.obj W)) (ULift.up (U.map b))
  rw [Adjunction.uliftYonedaCompHom, GrothendieckTopology.uliftYonedaEquiv_symm_app_apply]
  change _ = ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)).obj.map
    (U.map b).op (((U.sheafAdjunctionContinuous (Type u) J K).unit.app
      (J.uliftYoneda.{u}.obj V)).hom.app (op V) (ULift.up (𝟙 V)))
  have hn := (((U.sheafAdjunctionContinuous (Type u) J K).unit.app
    (J.uliftYoneda.{u}.obj V)).hom.naturality_apply b.op
      (show (J.uliftYoneda.{u}.obj V).obj.obj (op V) from ULift.up (𝟙 V)))
  change ((U.sheafAdjunctionContinuous (Type u) J K).unit.app
    (J.uliftYoneda.{u}.obj V)).hom.app (op W) (ULift.up (b ≫ 𝟙 V)) =
      ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)).obj.map
        (U.map b).op (((U.sheafAdjunctionContinuous (Type u) J K).unit.app
          (J.uliftYoneda.{u}.obj V)).hom.app (op V) (ULift.up (𝟙 V))) at hn
  simpa only [Category.comp_id] using hn

private def representableSlice_chartSquare
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.Subcanonical] [K.Subcanonical]
    (U : C ⥤ D) [U.IsContinuous J K] (V : C) :
    representableRingedSliceChart V (Iso.refl (J.uliftYoneda.{u}.obj V)) ⋙
        representableSliceElementFunctor (J := J) (K := K) U V ≅
      Over.post U ⋙ representableRingedSliceChart (U.obj V)
        (representableRingedSliceImageIso (J := J) (K := K) U V) :=
  NatIso.ofComponents (fun X ↦
    (CategoryOfElements.isoMk
      ((Over.post U ⋙ representableRingedSliceChart (U.obj V)
        (representableRingedSliceImageIso (J := J) (K := K) U V)).obj X).unop
      ((representableRingedSliceChart V (Iso.refl (J.uliftYoneda.{u}.obj V)) ⋙
        representableSliceElementFunctor (J := J) (K := K) U V).obj X).unop
      (Iso.refl _) (by
      change ((U.sheafPullback (Type u) J K).obj
        (J.uliftYoneda.{u}.obj V)).obj.map (𝟙 (op (U.obj X.left)))
          ((representableRingedSliceImageIso (J := J) (K := K) U V).inv.hom.app
            (op (U.obj X.left)) (ULift.up (U.map X.hom))) =
        ((U.sheafAdjunctionContinuous (Type u) J K).unit.app
          (J.uliftYoneda.{u}.obj V)).hom.app (op X.left) (ULift.up X.hom)
      rw [Functor.map_id_apply]
      exact (representableSlice_unit (J := J) (K := K) U V X.left X.hom).symm)).op)
    (by
      intro X Y f
      apply Quiver.Hom.unop_inj
      apply Subtype.ext
      change (𝟙 _) ≫ (U.map f.left).op = (U.map f.left).op ≫ (𝟙 _)
      simp)

private theorem element_identity_heq
    {E : Type u} [SmallCategory E] (B : E ⥤ Type u) (W : E)
    {a b : B.obj W} (h : B.map (𝟙 W) a = b)
    (M : B.Elementsᵒᵖᵒᵖ ⥤ Type u) (x : M.obj (op (op ⟨W, a⟩))) :
    HEq (M.map (CategoryOfElements.homMk ⟨W, a⟩ ⟨W, b⟩ (𝟙 W) h).op.op x) x := by
  have hab : a = b := by simpa only [Functor.map_id_apply] using h
  cases hab
  change HEq (M.map (𝟙 _) x) x
  rw [Functor.map_id_apply]

private theorem representableSlice_chartSquare_heq
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.Subcanonical] [K.Subcanonical]
    (U : C ⥤ D) [U.IsContinuous J K] (V : C)
    (M : (((U.sheafPullback (Type u) J K).obj
      (J.uliftYoneda.{u}.obj V)).obj.Elementsᵒᵖ)ᵒᵖ ⥤ Type u)
    (T : Over V)
    (x : M.obj (op ((representableRingedSliceChart V
      (Iso.refl (J.uliftYoneda.{u}.obj V)) ⋙
        representableSliceElementFunctor (J := J) (K := K) U V).obj T))) :
    HEq (M.map ((representableSlice_chartSquare U V).inv.app T).op x) x := by
  exact element_identity_heq _ _ _ M x

private theorem representableSlice_chartDense
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} [J.Subcanonical]
    (V : C) {A : Sheaf J (Type u)} (e : A ≅ J.uliftYoneda.{u}.obj V) :
    (representableRingedSliceChart V e).IsDenseSubsite (J.over V) (elementTopology A) := by
  have := (representableRingedSliceChart_properties V e).1
  refine { functorPushforward_mem_iff := ?_ }
  intro X S
  rw [projection_topology, ← liftedTopology_eq_restricted]
  change (S.functorPushforward (representableRingedSliceChart V e)).functorPushforward
    (elementProjection A) ∈ J _ ↔ S.functorPushforward (Over.forget V) ∈ J _
  rw [← Sieve.functorPushforward_comp]
  rfl

/-- The unit-induced element functor is continuous and its set inverse image is left exact.
Source: Stacks Tags 03CF and 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism).
Proof: the representable charts identify this functor with `Over.post U`: the
adjunct equation for c_V sends the unit image of a to U(a). Its covering sieves
therefore pull back to covering sieves. Under the same charts its inverse image
is the localized geometric inverse image, which preserves finite limits. -/
theorem representableSliceElementFunctor_continuous
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.Subcanonical] [K.Subcanonical]
    (U : C ⥤ D) [U.IsContinuous J K] (V : C) :
    (representableSliceElementFunctor (J := J) (K := K) U V).IsContinuous
      (elementTopology (J.uliftYoneda.{u}.obj V))
      (elementTopology ((U.sheafPullback (Type u) J K).obj
        (J.uliftYoneda.{u}.obj V))) := by
  let F := representableRingedSliceChart V (Iso.refl (J.uliftYoneda.{u}.obj V))
  let T := representableSliceElementFunctor (J := J) (K := K) U V
  let H := Over.post (X := V) U
  let G := representableRingedSliceChart (U.obj V)
    (representableRingedSliceImageIso (J := J) (K := K) U V)
  have : F.IsEquivalence := (representableRingedSliceChart_properties V _).1
  have : F.IsDenseSubsite (J.over V) (elementTopology (J.uliftYoneda.{u}.obj V)) :=
    representableSlice_chartDense V _
  let e := F.asEquivalence
  have : e.symm.inverse.IsDenseSubsite (J.over V)
      (elementTopology (J.uliftYoneda.{u}.obj V)) :=
    representableSlice_chartDense V _
  have : e.symm.functor.IsDenseSubsite
      (elementTopology (J.uliftYoneda.{u}.obj V)) (J.over V) := inferInstance
  have : e.inverse.IsContinuous (elementTopology (J.uliftYoneda.{u}.obj V)) (J.over V) :=
    Functor.IsDenseSubsite.instIsContinuous
      (J := elementTopology (J.uliftYoneda.{u}.obj V)) (K := J.over V)
      (G := e.symm.functor)
  have : (H ⋙ G).IsContinuous (J.over V)
      (elementTopology ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))) :=
    Functor.isContinuous_comp H G (J.over V) (K.over (U.obj V)) _
  have : (F ⋙ T).IsContinuous (J.over V)
      (elementTopology ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))) :=
    Functor.isContinuous_of_iso (representableSlice_chartSquare U V).symm _ _
  exact Functor.isContinuous_comp'
    ((Functor.associator e.inverse F T).symm ≪≫
      isoWhiskerRight e.counitIso T ≪≫ T.leftUnitor) _ (J.over V) _

/-- Continuity of the specified element functor.
Source: Stacks Tag 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
instance representableSliceElementFunctorContinuous
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.Subcanonical] [K.Subcanonical]
    (U : C ⥤ D) [U.IsContinuous J K] (V : C) :
    (representableSliceElementFunctor (J := J) (K := K) U V).IsContinuous
      (elementTopology (J.uliftYoneda.{u}.obj V))
      (elementTopology ((U.sheafPullback (Type u) J K).obj
        (J.uliftYoneda.{u}.obj V))) :=
  representableSliceElementFunctor_continuous U V

/-- Left exactness of the element-site inverse image.
Source: Stacks Tags 03CF and 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism).
Proof: identify the element sites by the representable charts with C/V and D/uV.
The element functor becomes Over.post U by the adjunct formula for c_V.
The localized set inverse image is left exact by the localized-site theorem;
equivalences preserve and reflect finite limits, giving the claim. -/
theorem representableSliceElementFunctor_leftExact
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.Subcanonical] [K.Subcanonical]
    (U : C ⥤ D) [U.IsContinuous J K] [PreservesFiniteLimits U] (V : C) :
    PreservesFiniteLimits
      ((representableSliceElementFunctor (J := J) (K := K) U V).sheafPullback (Type u)
        (elementTopology (J.uliftYoneda.{u}.obj V))
        (elementTopology ((U.sheafPullback (Type u) J K).obj
          (J.uliftYoneda.{u}.obj V)))) := by
  let F := representableRingedSliceChart V (Iso.refl (J.uliftYoneda.{u}.obj V))
  let T := representableSliceElementFunctor (J := J) (K := K) U V
  let H := Over.post (X := V) U
  let G := representableRingedSliceChart (U.obj V)
    (representableRingedSliceImageIso (J := J) (K := K) U V)
  have : F.IsEquivalence := (representableRingedSliceChart_properties V _).1
  have : G.IsEquivalence := (representableRingedSliceChart_properties (U.obj V) _).1
  let e := F.asEquivalence
  have : RepresentablyFlat H := flat_of_preservesFiniteLimits H
  have : RepresentablyFlat (e.inverse ⋙ H ⋙ G) := inferInstance
  have : RepresentablyFlat T := RepresentablyFlat.of_iso
    ((Functor.associator e.inverse H G) ≪≫
      isoWhiskerLeft e.inverse (representableSlice_chartSquare U V).symm ≪≫
      (Functor.associator e.inverse F T).symm ≪≫
      isoWhiskerRight e.counitIso T ≪≫ T.leftUnitor)
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits T (Type u) _ _

/-- The existing element ring with its commutative-ring coefficients retained.
Source: Stacks Tag 04IF
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
abbrev representableSliceCommRing
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u)) :=
  ((elementProjection A).sheafPushforwardContinuous CommRingCat.{u}
    (elementTopology A) J).obj R

/-- Restriction of the given structural adjunct to the specified element sites.
Source: Stacks Tags 04IF and 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceElementCoefficientMap
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [J.Subcanonical] [K.Subcanonical]
    (U : C ⥤ D) [U.IsContinuous J K]
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (a : R ⟶ (U.sheafPushforwardContinuous CommRingCat.{u} J K).obj S) (V : C) :
    representableSliceCommRing R (J.uliftYoneda.{u}.obj V) ⟶
      ((representableSliceElementFunctor U V).sheafPushforwardContinuous CommRingCat.{u}
        (elementTopology (J.uliftYoneda.{u}.obj V))
        (elementTopology ((U.sheafPullback (Type u) J K).obj
          (J.uliftYoneda.{u}.obj V)))).obj
        (representableSliceCommRing S
          ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))) :=
  ObjectProperty.homMk {
    app X := a.hom.app X.unop.unop.1
    naturality _X _Y b := a.hom.naturality b.unop.unop.1 }

private theorem representableSlice_moduleEquivalence
    {E F : Type u} [SmallCategory E] [SmallCategory F]
    {T : GrothendieckTopology E} {T' : GrothendieckTopology F}
    (e : E ≌ F) [e.functor.IsContinuous T T'] [e.inverse.IsContinuous T' T]
    {Q : Sheaf T RingCat.{u}} {Q' : Sheaf T' RingCat.{u}}
    (phi : Q ⟶ (e.functor.sheafPushforwardContinuous RingCat T T').obj Q')
    (psi : Q' ⟶ (e.inverse.sheafPushforwardContinuous RingCat T' T).obj Q)
    (h₁ : Functor.whiskerRight (NatTrans.op e.counit) Q'.obj =
      psi.hom ≫ e.inverse.op.whiskerLeft phi.hom)
    (h₂ : phi.hom ≫ e.functor.op.whiskerLeft psi.hom ≫
      Functor.whiskerRight (NatTrans.op e.unit) Q.obj = 𝟙 Q.obj) :
    (SheafOfModules.pushforward.{u} phi).IsEquivalence :=
  (SheafOfModules.pushforwardPushforwardEquivalence e phi psi h₁ h₂).isEquivalence_functor

private theorem representableSlice_equivalenceTriangle
    {E F : Type u} [SmallCategory E] [SmallCategory F]
    (e : E ≌ F) (P : Fᵒᵖ ⥤ RingCat.{u}) (X : E) :
    P.map (e.counit.app (e.functor.obj X)).op ≫
      P.map (e.functor.map (e.unit.app X)).op = 𝟙 _ := by
  rw [← Functor.map_comp, ← op_comp]
  exact (congrArg (fun f ↦ P.map f.op) (e.functor_unitIso_comp X)).trans
    (P.map_id (op (e.functor.obj X)))

set_option backward.isDefEq.respectTransparency true in
private theorem representableSlice_modulesChart_equivalence
    {E : Type u} [SmallCategory E] {T : GrothendieckTopology E} [T.Subcanonical]
    (Q : Sheaf T RingCat.{u}) (W : E) {B : Sheaf T (Type u)}
    (c : B ≅ T.uliftYoneda.{u}.obj W) :
    (representableRingedSliceModules Q W c).IsEquivalence := by
  let F := representableRingedSliceChart W c
  have : F.IsEquivalence := (representableRingedSliceChart_properties W c).1
  let e := F.asEquivalence
  have : e.functor.IsContinuous (T.over W) (elementTopology B) :=
    (representableRingedSliceChart_properties W c).2
  have : e.symm.inverse.IsDenseSubsite (T.over W) (elementTopology B) :=
    representableSlice_chartDense W c
  have : e.symm.functor.IsDenseSubsite (elementTopology B) (T.over W) := inferInstance
  have : e.inverse.IsContinuous (elementTopology B) (T.over W) :=
    Functor.IsDenseSubsite.instIsContinuous (J := elementTopology B) (K := T.over W)
      (G := e.symm.functor)
  let A := elementRing Q B
  let S := Q.over W
  let phi := representableRingedSliceCoefficientMap Q W c
  let psi : A ⟶ (e.inverse.sheafPushforwardContinuous RingCat (elementTopology B)
      (T.over W)).obj S :=
    ⟨Functor.whiskerRight (NatTrans.op e.counit) A.obj⟩
  have h₁ : Functor.whiskerRight (NatTrans.op e.counit) A.obj =
      psi.hom ≫ e.inverse.op.whiskerLeft phi.hom := by
    ext X : 2
    exact (Category.comp_id _).symm
  have h₂ : phi.hom ≫ e.functor.op.whiskerLeft psi.hom ≫
      Functor.whiskerRight (NatTrans.op e.unit) S.obj = 𝟙 S.obj := by
    ext X : 2
    change A.obj.map (e.counit.app (e.functor.obj X.unop)).op ≫
      A.obj.map (e.functor.map (e.unit.app X.unop)).op = 𝟙 _
    exact representableSlice_equivalenceTriangle e A.obj X.unop
  change (SheafOfModules.pushforward.{u} phi).IsEquivalence
  exact representableSlice_moduleEquivalence e phi psi h₁ h₂

private theorem representableSlice_setsChart_equivalence
    {E : Type u} [SmallCategory E] {T : GrothendieckTopology E} [T.Subcanonical]
    (W : E) {B : Sheaf T (Type u)} (c : B ≅ T.uliftYoneda.{u}.obj W) :
    (representableRingedSliceSets W c).IsEquivalence := by
  let F := representableRingedSliceChart W c
  have : F.IsEquivalence := (representableRingedSliceChart_properties W c).1
  let e := F.asEquivalence
  have : e.functor.IsContinuous (T.over W) (elementTopology B) :=
    (representableRingedSliceChart_properties W c).2
  have : e.symm.inverse.IsDenseSubsite (T.over W) (elementTopology B) :=
    representableSlice_chartDense W c
  have : e.inverse.IsDenseSubsite (elementTopology B) (T.over W) :=
    inferInstanceAs (e.symm.functor.IsDenseSubsite (elementTopology B) (T.over W))
  exact (e.sheafCongr (T.over W) (elementTopology B) (Type u)).isEquivalence_inverse


section CanonicalComparisons
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  [HasFiniteLimits C] [HasFiniteLimits D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.Subcanonical] [K.Subcanonical]
  (U : C ⥤ D) [U.IsContinuous J K] [PreservesFiniteLimits U]
  {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
  (a : R ⟶ (U.sheafPushforwardContinuous CommRingCat.{u} J K).obj S) (V : C)

/-- The concrete slice inverse image, along the unit-induced element functor.
Source: Stacks Tags 04IF and 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
abbrev representableSliceInverse :=
  (representableSliceElementFunctor (J := J) (K := K) U V).sheafPullback (Type u)
    (elementTopology (J.uliftYoneda.{u}.obj V))
    (elementTopology ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)))

/-- The restricted structural map on rings, with components a_W.
Source: Stacks Tags 04IF and 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
abbrev representableSliceRingMap :
    elementRing ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        (J.uliftYoneda.{u}.obj V) ⟶
      ((representableSliceElementFunctor U V).sheafPushforwardContinuous RingCat _ _).obj
        (elementRing ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
          ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))) :=
  SheafOfModules.ringedSiteModuleMap (representableSliceElementFunctor U V)
    (representableSliceElementCoefficientMap U a V)

/-- The actual module inverse image of the specified slice ringed-site morphism.
Source: Stacks Tags 04IF and 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
abbrev representableSliceModulePullback :
    SheafOfModules.{u} (elementRing ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      (J.uliftYoneda.{u}.obj V)) ⥤
    SheafOfModules.{u} (elementRing ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))) :=
  SheafOfModules.pullback.{u} (F := representableSliceElementFunctor U V)
    (representableSliceRingMap U a V)

/-- The fixed module adjunction for the element-site morphism.
Source: Mathlib's continuous module adjunction.
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceModuleAdjunction : representableSliceModulePullback U a V ⊣
    SheafOfModules.pushforward (representableSliceRingMap U a V) :=
  SheafOfModules.pullbackPushforwardAdjunction (representableSliceRingMap U a V)

/-- The fixed module adjunction on the original sites.
Source: Mathlib's continuous module adjunction.
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceGlobalModuleAdjunction :
    SheafOfModules.pullback.{u} (SheafOfModules.ringedSiteModuleMap U a) ⊣
      SheafOfModules.pushforward (SheafOfModules.ringedSiteModuleMap U a) :=
  SheafOfModules.pullbackPushforwardAdjunction (SheafOfModules.ringedSiteModuleMap U a)

/-- The fixed module adjunction on the localized sites.
Source: Mathlib's continuous module adjunction.
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceLocalizedModuleAdjunction :
    SheafOfModules.pullback.{u} (SheafOfModules.sliceModuleRingMap U
        (SheafOfModules.ringedSiteModuleMap U a) V) ⊣
    SheafOfModules.pushforward (SheafOfModules.sliceModuleRingMap U
        (SheafOfModules.ringedSiteModuleMap U a) V) :=
  SheafOfModules.pullbackPushforwardAdjunction
    (SheafOfModules.sliceModuleRingMap U
        (SheafOfModules.ringedSiteModuleMap U a) V)

/-- The direct-image square of the slice is identity on sections.
Source: Stacks Tags 03CF and 04IF
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceSetPushforwardIso :
    U.sheafPushforwardContinuous (Type u) J K ⋙
        elementSheafPullback (J.uliftYoneda.{u}.obj V) ≅
      elementSheafPullback ((U.sheafPullback (Type u) J K).obj
        (J.uliftYoneda.{u}.obj V)) ⋙
        (representableSliceElementFunctor U V).sheafPushforwardContinuous (Type u) _ _ :=
  NatIso.ofComponents (fun _ ↦ ObjectProperty.isoMk _ (Iso.refl _))

/-- The canonical restriction map of set sheaves is the inverse mate of the identity.
Source: Stacks Tags 03CF and 04IF
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceSetPullbackMap :
    elementSheafPullback (J.uliftYoneda.{u}.obj V) ⋙
        representableSliceInverse (J := J) (K := K) U V ⟶
      U.sheafPullback (Type u) J K ⋙
        elementSheafPullback ((U.sheafPullback (Type u) J K).obj
          (J.uliftYoneda.{u}.obj V)) :=
  ((mateEquiv (U.sheafAdjunctionContinuous (Type u) J K)
    ((representableSliceElementFunctor U V).sheafAdjunctionContinuous (Type u) _ _)).symm
      (TwoSquare.mk _ _ _ _
        (representableSliceSetPushforwardIso (J := J) (K := K) U V).hom)).natTrans

/-- The module direct-image restriction square, identity on sections.
Source: Stacks Tags 04IF and 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceModulePushforwardIso :
    SheafOfModules.pushforward.{u} (SheafOfModules.ringedSiteModuleMap U a) ⋙
        elementModulePullback ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
          (J.uliftYoneda.{u}.obj V) ≅
      elementModulePullback ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
          ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)) ⋙
        SheafOfModules.pushforward (representableSliceRingMap U a V) :=
  NatIso.ofComponents (fun _ ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _))) (by intros; rfl)

/-- The canonical module restriction mate. This is mu inverse, fixed before the square.
Source: Stacks Tags 04IF and 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceModulePullbackMap :
    elementModulePullback ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        (J.uliftYoneda.{u}.obj V) ⋙ representableSliceModulePullback U a V ⟶
      SheafOfModules.pullback.{u} (SheafOfModules.ringedSiteModuleMap U a) ⋙
        elementModulePullback ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
          ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)) :=
  ((mateEquiv (representableSliceGlobalModuleAdjunction U a)
    (representableSliceModuleAdjunction U a V)).symm
      (TwoSquare.mk _ _ _ _ (representableSliceModulePushforwardIso U a V).hom)).natTrans


/-- The underlying structural adjunct on element-site sheaves, restricted sectionwise.
Source: Stacks Tag 04IF
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceUnderlyingCoefficientMap :
    ((sheafCompose (elementTopology (J.uliftYoneda.{u}.obj V)) (forget RingCat)).obj
      (elementRing ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        (J.uliftYoneda.{u}.obj V))) ⟶
      ((representableSliceElementFunctor (J := J) (K := K) U V).sheafPushforwardContinuous (Type
      u) _ _).obj
        ((sheafCompose
          (elementTopology ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)))
          (forget RingCat)).obj
          (elementRing ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
            ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)))) :=
  ObjectProperty.homMk
    (Functor.whiskerRight (representableSliceRingMap U a V).hom (forget RingCat))

/-- The structural map is the transpose of the restricted given ring map.
Source: Stacks Tag 04IF
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceStructuralMap :
    (representableSliceInverse U V).obj
      ((elementSheafPullback (J.uliftYoneda.{u}.obj V)).obj
        ((sheafCompose J (forget CommRingCat)).obj R)) ⟶
    (elementSheafPullback ((U.sheafPullback (Type u) J K).obj
      (J.uliftYoneda.{u}.obj V))).obj ((sheafCompose K (forget CommRingCat)).obj S) :=
  (((representableSliceElementFunctor (J := J) (K := K) U V).sheafAdjunctionContinuous (Type u) _
      _).homEquiv _ _).symm
      (representableSliceUnderlyingCoefficientMap U a V)

private theorem representableSlice_ringed_ext
    {E F : Type u} [SmallCategory E] [SmallCategory F]
    {T : GrothendieckTopology E} {T' : GrothendieckTopology F}
    {Q : Sheaf T RingCat.{u}} {Q' : Sheaf T' RingCat.{u}}
    (s t : RingedToposMorphism Q Q')
    (hi : s.inverse = t.inverse) (hd : s.direct = t.direct)
    (ha : HEq s.adj t.adj) (hr : HEq s.ringMap t.ringMap)
    (hm : s.modules = t.modules) (hu : HEq s.underlying t.underlying) : s = t := by
  rcases s with ⟨si, sd, sa, sle, sr, sz, so, sadd, sm, smod, smadd, su, slin⟩
  rcases t with ⟨ti, td, ta, tle, tr, tz, tone, tadd, tm, tmod, tmadd, tu, tlin⟩
  dsimp only at hi hd ha hr hm hu
  subst ti
  subst td
  cases eq_of_heq ha
  cases eq_of_heq hr
  subst tmod
  cases eq_of_heq hu
  rfl

private theorem representableSlice_continuousRinged_spec
    {E F : Type u} [SmallCategory E] [SmallCategory F]
    {T : GrothendieckTopology E} {T' : GrothendieckTopology F}
    (P : F ⥤ E) [P.IsContinuous T' T]
    (L : Sheaf T' (Type u) ⥤ Sheaf T (Type u))
    (adj : L ⊣ P.sheafPushforwardContinuous (Type u) T' T)
    [PreservesFiniteLimits L]
    (Q : Sheaf T CommRingCat.{u}) (Q' : Sheaf T' CommRingCat.{u})
    (phi : Q' ⟶ (P.sheafPushforwardContinuous CommRingCat T' T).obj Q) :
    let sf := siteContinuousRingedTopos P L adj Q Q' phi
    sf.inverse = L ∧ sf.direct = P.sheafPushforwardContinuous (Type u) T' T ∧
      HEq sf.adj adj ∧
      HEq sf.ringMap ((adj.homEquiv
        ((sheafCompose T' (forget CommRingCat)).obj Q')
        ((sheafCompose T (forget CommRingCat)).obj Q)).symm
          (ObjectProperty.homMk (Functor.whiskerRight phi.hom (forget CommRingCat)))) ∧
      sf.modules = SheafOfModules.pushforward (F := P) (J := T') (K := T)
          (S := (sheafCompose T' (forget₂ CommRingCat RingCat)).obj Q')
          (R := (sheafCompose T (forget₂ CommRingCat RingCat)).obj Q)
        ((sheafCompose T' (forget₂ CommRingCat RingCat)).map phi) ∧
      HEq sf.underlying (Iso.refl
        (SheafOfModules.pushforward (F := P) (J := T') (K := T)
          (S := (sheafCompose T' (forget₂ CommRingCat RingCat)).obj Q')
          (R := (sheafCompose T (forget₂ CommRingCat RingCat)).obj Q)
          ((sheafCompose T' (forget₂ CommRingCat RingCat)).map phi) ⋙
          SheafOfModules.toSheaf _ ⋙ sheafCompose _ (forget AddCommGrpCat))) := by
  exact ⟨rfl, rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl⟩

private theorem representableSlice_continuousRinged_unique
    {E F : Type u} [SmallCategory E] [SmallCategory F]
    {T : GrothendieckTopology E} {T' : GrothendieckTopology F}
    (P : F ⥤ E) [P.IsContinuous T' T]
    (L : Sheaf T' (Type u) ⥤ Sheaf T (Type u))
    (adj : L ⊣ P.sheafPushforwardContinuous (Type u) T' T)
    [PreservesFiniteLimits L]
    (Q : Sheaf T CommRingCat.{u}) (Q' : Sheaf T' CommRingCat.{u})
    (phi : Q' ⟶ (P.sheafPushforwardContinuous CommRingCat T' T).obj Q) :
    ∃! sf : RingedToposMorphism
        ((sheafCompose T (forget₂ CommRingCat RingCat)).obj Q)
        ((sheafCompose T' (forget₂ CommRingCat RingCat)).obj Q'),
    sf.inverse = L ∧ sf.direct = P.sheafPushforwardContinuous (Type u) T' T ∧
      HEq sf.adj adj ∧
      HEq sf.ringMap ((adj.homEquiv
        ((sheafCompose T' (forget CommRingCat)).obj Q')
        ((sheafCompose T (forget CommRingCat)).obj Q)).symm
          (ObjectProperty.homMk (Functor.whiskerRight phi.hom (forget CommRingCat)))) ∧
      sf.modules = SheafOfModules.pushforward (F := P) (J := T') (K := T)
          (S := (sheafCompose T' (forget₂ CommRingCat RingCat)).obj Q')
          (R := (sheafCompose T (forget₂ CommRingCat RingCat)).obj Q)
        ((sheafCompose T' (forget₂ CommRingCat RingCat)).map phi) ∧
      HEq sf.underlying (Iso.refl
        (SheafOfModules.pushforward (F := P) (J := T') (K := T)
          (S := (sheafCompose T' (forget₂ CommRingCat RingCat)).obj Q')
          (R := (sheafCompose T (forget₂ CommRingCat RingCat)).obj Q)
          ((sheafCompose T' (forget₂ CommRingCat RingCat)).map phi) ⋙
          SheafOfModules.toSheaf _ ⋙ sheafCompose _ (forget AddCommGrpCat))) := by
  let sf := siteContinuousRingedTopos P L adj Q Q' phi
  have hs := representableSlice_continuousRinged_spec P L adj Q Q' phi
  apply ExistsUnique.intro sf hs
  intro t ht
  rcases ht with ⟨hi, hd, ha, hr, hm, hu⟩
  exact representableSlice_ringed_ext t sf (hi.trans hs.1.symm)
    (hd.trans hs.2.1.symm) (ha.trans hs.2.2.1.symm)
    (hr.trans hs.2.2.2.1.symm) (hm.trans hs.2.2.2.2.1.symm)
    (hu.trans hs.2.2.2.2.2.symm)

/-- The slice ringed morphism has completely specified geometric and module data.
Source: Stacks Tags 04IF and 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism).
Proof: transpose the sectionwise ring map a through the displayed continuous
adjunction. Naturality of its unit and counit with the terminal and product
projections proves preservation of zero, one, addition and multiplication.
Take module pushforward with the same coefficient map; its underlying set sheaf
is the displayed continuous direct image, so its underlying identification is
identity. Transposition of the scalar-action and addition maps proves module
linearity. All data fields have thus been specified, and proof irrelevance
makes the resulting structure unique. -/
theorem representableSliceRingedMorphism_unique :
    ∃! sf : RingedToposMorphism
      (elementRing ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
        ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)))
      (elementRing ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        (J.uliftYoneda.{u}.obj V)),
      sf.inverse = representableSliceInverse (J := J) (K := K) U V ∧
      sf.direct = (representableSliceElementFunctor (J := J) (K := K) U
      V).sheafPushforwardContinuous
        (Type u) _ _ ∧
      HEq sf.adj
        ((representableSliceElementFunctor (J := J) (K := K) U V).sheafAdjunctionContinuous (Type u)
          (elementTopology (J.uliftYoneda.{u}.obj V))
          (elementTopology ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)))) ∧
      HEq sf.ringMap (representableSliceStructuralMap U a V) ∧
      sf.modules = SheafOfModules.pushforward.{u} (representableSliceRingMap U a V) ∧
      HEq sf.underlying (Iso.refl
        (SheafOfModules.pushforward.{u} (representableSliceRingMap U a V) ⋙
          SheafOfModules.toSheaf _ ⋙ sheafCompose _ (forget AddCommGrpCat))) := by
  have : PreservesFiniteLimits (representableSliceInverse (J := J) (K := K) U V) :=
    representableSliceElementFunctor_leftExact U V
  exact representableSlice_continuousRinged_unique (representableSliceElementFunctor U V)
    (representableSliceInverse (J := J) (K := K) U V)
    ((representableSliceElementFunctor U V).sheafAdjunctionContinuous (Type u) _ _)
    (representableSliceCommRing S
      ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)))
    (representableSliceCommRing R (J.uliftYoneda.{u}.obj V))
    (representableSliceElementCoefficientMap U a V)


/-- The unique ringed morphism with the concrete element-site data specified above.
The uniqueness theorem fixes every data field; only proofs of its laws are postponed.
Source: Stacks Tags 04IF and 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceRingedMorphism : RingedToposMorphism
    (elementRing ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)))
    (elementRing ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      (J.uliftYoneda.{u}.obj V)) :=
  Classical.choose (representableSliceRingedMorphism_unique U a V)

/-- The chart comparison on module direct images, normalized on sections.
Source: Stacks Tag 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism).
Proof: the unit image of an arrow b is sent by c_V to U(b), by the representable
adjunct equation. Thus the two restrictions evaluate the same module at the same
element-site object. The induced map is identity on its sections and scalar
multiplication is restriction along a in both expressions. This defines a natural
isomorphism, uniquely determined by its section maps. -/
theorem representableSliceModuleChartPushforward_unique :
    ∃! beta : SheafOfModules.pushforward.{u} (representableSliceRingMap U a V) ⋙
        representableRingedSliceModules
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) V
          (Iso.refl (J.uliftYoneda.{u}.obj V)) ≅
      representableRingedSliceModules
          ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S) (U.obj V)
          (representableRingedSliceImageIso (J := J) (K := K) U V) ⋙
        SheafOfModules.pushforward (SheafOfModules.sliceModuleRingMap U
        (SheafOfModules.ringedSiteModuleMap U a) V),
      ∀ M T x, HEq ((beta.hom.app M).val.app (op T) x) x := by
  let F := representableRingedSliceChart V (Iso.refl (J.uliftYoneda.{u}.obj V))
  let T := representableSliceElementFunctor (J := J) (K := K) U V
  let H := Over.post (X := V) U
  let G := representableRingedSliceChart (U.obj V)
    (representableRingedSliceImageIso (J := J) (K := K) U V)
  let phi := representableRingedSliceCoefficientMap
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) V
    (Iso.refl (J.uliftYoneda.{u}.obj V))
  let psi := representableSliceRingMap U a V
  let phi' := SheafOfModules.sliceModuleRingMap U
    (SheafOfModules.ringedSiteModuleMap U a) V
  let psi' := representableRingedSliceCoefficientMap
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S) (U.obj V)
    (representableRingedSliceImageIso (J := J) (K := K) U V)
  have : (F ⋙ T).IsContinuous (J.over V)
      (elementTopology ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))) :=
    Functor.isContinuous_comp F T (J.over V)
      (elementTopology (J.uliftYoneda.{u}.obj V))
      (elementTopology ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)))
  have : (H ⋙ G).IsContinuous (J.over V)
      (elementTopology ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))) :=
    Functor.isContinuous_comp H G (J.over V) (K.over (U.obj V))
      (elementTopology ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)))
  let rho : (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V) ⟶
      ((F ⋙ T).sheafPushforwardContinuous RingCat (J.over V)
        (elementTopology ((U.sheafPullback (Type u) J K).obj
          (J.uliftYoneda.{u}.obj V)))).obj
          (elementRing ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
            ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))) :=
    phi ≫ (F.sheafPushforwardContinuous RingCat (J.over V)
    (elementTopology (J.uliftYoneda.{u}.obj V))).map psi
  let rho' : (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V) ⟶
      ((H ⋙ G).sheafPushforwardContinuous RingCat (J.over V)
        (elementTopology ((U.sheafPullback (Type u) J K).obj
          (J.uliftYoneda.{u}.obj V)))).obj
          (elementRing ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
            ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))) :=
    phi' ≫ (H.sheafPushforwardContinuous RingCat (J.over V)
      (K.over (U.obj V))).map psi'
  have hr : rho ≫ (Functor.sheafPushforwardContinuousNatTrans
      (representableSlice_chartSquare U V).inv RingCat _ _).app
        (elementRing ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
          ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))) = rho' := by
    ext X x
    change S.obj.map (𝟙 (op (U.obj X.unop.left)))
      (a.hom.app (op X.unop.left) x) = a.hom.app (op X.unop.left) x
    rw [Functor.map_id]
    rfl
  let beta := SheafOfModules.pushforwardComp phi psi ≪≫
    SheafOfModules.pushforwardNatIso (F := H ⋙ G) (G := F ⋙ T) rho
      (representableSlice_chartSquare U V).symm ≪≫
      SheafOfModules.pushforwardCongr hr ≪≫
        (SheafOfModules.pushforwardComp phi' psi').symm
  have hb : ∀ M T x, HEq ((beta.hom.app M).val.app (op T) x) x := by
    intro M X x
    change HEq (M.val.map ((representableSlice_chartSquare U V).inv.app X).op x) x
    exact representableSlice_chartSquare_heq U V
      (M.val.presheaf ⋙ forget AddCommGrpCat) X x
  refine ⟨beta, hb, ?_⟩
  intro gamma hg
  apply Iso.ext
  ext M T x
  exact eq_of_heq ((hg M T.unop x).trans (hb M T.unop x).symm)

/-- The sectionwise identity chart comparison, fixed before taking its mate.
Source: Stacks Tag 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceModuleChartPushforwardIso :
    SheafOfModules.pushforward.{u} (representableSliceRingMap U a V) ⋙
        representableRingedSliceModules
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) V
          (Iso.refl (J.uliftYoneda.{u}.obj V)) ≅
      representableRingedSliceModules
          ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S) (U.obj V)
          (representableRingedSliceImageIso (J := J) (K := K) U V) ⋙
        SheafOfModules.pushforward (SheafOfModules.sliceModuleRingMap U
        (SheafOfModules.ringedSiteModuleMap U a) V) :=
  Classical.choose (representableSliceModuleChartPushforward_unique U a V)

/-- The canonical chart inverse mate on modules, in the direction lambda.
Source: Stacks Tag 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceModuleChartPullbackMap :
    representableRingedSliceModules
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) V
      (Iso.refl (J.uliftYoneda.{u}.obj V)) ⋙
        SheafOfModules.pullback.{u} (SheafOfModules.sliceModuleRingMap U
        (SheafOfModules.ringedSiteModuleMap U a) V) ⟶
    representableSliceModulePullback U a V ⋙ representableRingedSliceModules
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S) (U.obj V)
      (representableRingedSliceImageIso (J := J) (K := K) U V) :=
  ((mateEquiv
    (representableSliceModuleAdjunction U a V)
    (representableSliceLocalizedModuleAdjunction U a V)).symm
      (TwoSquare.mk _ _ _ _ (representableSliceModuleChartPushforwardIso U a V).hom)).natTrans


/-- The set chart direct-image comparison, fixed on every section.
Source: Stacks Tags 03CF and 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism).
Proof: c_V sends the unit image of b to U(b), so the two functors evaluate a
sheaf at the same element. Transport along this equality gives the sectionwise
identity. The same equality for triangles proves naturality; the identity on
sections uniquely determines the isomorphism. -/
theorem representableSliceSetChartPushforward_unique :
    ∃! beta :
      (representableSliceElementFunctor (J := J) (K := K) U V).sheafPushforwardContinuous (Type
      u) _ _ ⋙
        representableRingedSliceSets V (Iso.refl (J.uliftYoneda.{u}.obj V)) ≅
      representableRingedSliceSets (U.obj V)
          (representableRingedSliceImageIso (J := J) (K := K) U V) ⋙
        (Over.post (X := V) U).sheafPushforwardContinuous (Type u) _ _,
      ∀ M T x, HEq ((beta.hom.app M).hom.app (op T) x) x := by
  let beta :
      (representableSliceElementFunctor (J := J) (K := K) U V).sheafPushforwardContinuous
        (Type u) _ _ ⋙
          representableRingedSliceSets V (Iso.refl (J.uliftYoneda.{u}.obj V)) ≅
      representableRingedSliceSets (U.obj V)
          (representableRingedSliceImageIso (J := J) (K := K) U V) ⋙
        (Over.post (X := V) U).sheafPushforwardContinuous (Type u) _ _ :=
    NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
      (isoWhiskerRight (NatIso.op (representableSlice_chartSquare U V).symm) M.obj))
      (by
        intro M N f
        ext T x
        exact (f.hom.naturality_apply
          ((representableSlice_chartSquare U V).inv.app T.unop).op x).symm)
  have hb : ∀ M T x, HEq ((beta.hom.app M).hom.app (op T) x) x := by
    intro M T x
    exact representableSlice_chartSquare_heq U V M.obj T x
  refine ⟨beta, hb, ?_⟩
  intro gamma hg
  apply Iso.ext
  ext M T x
  exact eq_of_heq ((hg M T.unop x).trans (hb M T.unop x).symm)

/-- The chart direct-image identification has sectionwise identity components.
Source: Stacks Tag 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceSetChartPushforwardIso :
    (representableSliceElementFunctor (J := J) (K := K) U V).sheafPushforwardContinuous (Type
      u) _ _ ⋙
        representableRingedSliceSets V (Iso.refl (J.uliftYoneda.{u}.obj V)) ≅
      representableRingedSliceSets (U.obj V)
          (representableRingedSliceImageIso (J := J) (K := K) U V) ⋙
        (Over.post (X := V) U).sheafPushforwardContinuous (Type u) _ _ :=
  Classical.choose (representableSliceSetChartPushforward_unique (J := J) (K := K) U V)

/-- The canonical set chart inverse mate, in the direction alpha.
Source: Stacks Tags 03CF and 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceSetChartPullbackMap :
    representableRingedSliceSets V (Iso.refl (J.uliftYoneda.{u}.obj V)) ⋙
      (Over.post U).sheafPullback (Type u) (J.over V) (K.over (U.obj V)) ⟶
    representableSliceInverse U V ⋙ representableRingedSliceSets (U.obj V)
      (representableRingedSliceImageIso (J := J) (K := K) U V) :=
  ((mateEquiv
    ((representableSliceElementFunctor (J := J) (K := K) U V).sheafAdjunctionContinuous (Type u)
      _ _)
    ((Over.post (X := V) U).sheafAdjunctionContinuous (Type u) _ _)).symm
      (TwoSquare.mk _ _ _ _
        (representableSliceSetChartPushforwardIso (J := J) (K := K) U V).hom)).natTrans

private def representableSlice_right :
    Over ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)) ⥤
      Over (J.uliftYoneda.{u}.obj V) :=
  Over.post (U.sheafPushforwardContinuous (Type u) J K) ⋙
    Over.pullback ((U.sheafAdjunctionContinuous (Type u) J K).unit.app
      (J.uliftYoneda.{u}.obj V))

private def representableSlice_fibreFunctor
    {E : Type u} [SmallCategory E] {T : GrothendieckTopology E}
    (B : Sheaf T (Type u)) : Over B ⥤ Sheaf (elementTopology B) (Type u) where
  obj X := ⟨(elementFibrePresheafFunctor B).obj X, by
    obtain ⟨_, _, ⟨e, ⟨i⟩⟩, _⟩ := element_site_descent B
    exact (Presheaf.isSheaf_of_iso_iff (i.app X)).mp (e.inverse.obj X).property⟩
  map f := ⟨(elementFibrePresheafFunctor B).map f⟩

private def representableSlice_rightFibreEquiv
    (X : Over ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)))
    (W : Cᵒᵖ) (b : (J.uliftYoneda.{u}.obj V).obj.obj W) :
    ((elementFibrePresheafFunctor (J.uliftYoneda.{u}.obj V)).obj
      ((representableSlice_right U V).obj X)).obj (elementObj _ W b) ≃
    ((elementFibrePresheafFunctor
      ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))).obj X).obj
      (elementObj _ (U.op.obj W)
        (((U.sheafAdjunctionContinuous (Type u) J K).unit.app
          (J.uliftYoneda.{u}.obj V)).hom.app W b)) where
  toFun x := ⟨(pullback.fst
      ((U.sheafPushforwardContinuous (Type u) J K).map X.hom)
      ((U.sheafAdjunctionContinuous (Type u) J K).unit.app
        (J.uliftYoneda.{u}.obj V))).hom.app W x.val, by
    have hp := congrArg (fun f ↦ f.hom.app W x.val)
      (pullback.condition (f := (U.sheafPushforwardContinuous (Type u) J K).map X.hom)
        (g := (U.sheafAdjunctionContinuous (Type u) J K).unit.app
          (J.uliftYoneda.{u}.obj V)))
    exact hp.trans (congrArg _ x.property)⟩
  invFun x := ⟨(sectionsPullbackEquiv J
      ((U.sheafPushforwardContinuous (Type u) J K).map X.hom)
      ((U.sheafAdjunctionContinuous (Type u) J K).unit.app
        (J.uliftYoneda.{u}.obj V)) W.unop).symm ⟨(x.val, b), x.property⟩,
    sectionsPullbackEquiv_inv_snd J _ _ W.unop _⟩
  left_inv x := by
    apply Subtype.ext
    apply (sectionsPullbackEquiv J _ _ W.unop).injective
    apply Subtype.ext
    apply Prod.ext
    · exact sectionsPullbackEquiv_inv_fst J _ _ W.unop _
    · exact (sectionsPullbackEquiv_inv_snd J _ _ W.unop _).trans x.property.symm
  right_inv x := by
    apply Subtype.ext
    exact sectionsPullbackEquiv_inv_fst J _ _ W.unop _

private def representableSlice_rightFibreIso :
    representableSlice_right U V ⋙ representableSlice_fibreFunctor (J.uliftYoneda.{u}.obj V) ≅
      representableSlice_fibreFunctor
        ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)) ⋙
        (representableSliceElementFunctor U V).sheafPushforwardContinuous (Type u) _ _ :=
  NatIso.ofComponents (fun X ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun T ↦
      (representableSlice_rightFibreEquiv U V X T.unop.unop.1 T.unop.unop.2).toIso)
      (by
        intro T T' f
        apply ConcreteCategory.hom_ext
        intro x
        apply Subtype.ext
        exact (pullback.fst
          ((U.sheafPushforwardContinuous (Type u) J K).map X.hom)
          ((U.sheafAdjunctionContinuous (Type u) J K).unit.app
            (J.uliftYoneda.{u}.obj V))).hom.naturality_apply f.unop.unop.1 x.val))) (by
    intro X Y f
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext T
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    change (pullback.fst ((U.sheafPushforwardContinuous (Type u) J K).map Y.hom)
      ((U.sheafAdjunctionContinuous (Type u) J K).unit.app
        (J.uliftYoneda.{u}.obj V))).hom.app T.unop.unop.1
        (((representableSlice_right U V).map f).left.hom.app T.unop.unop.1 x.val) =
      f.left.hom.app (U.op.obj T.unop.unop.1)
        ((pullback.fst ((U.sheafPushforwardContinuous (Type u) J K).map X.hom)
          ((U.sheafAdjunctionContinuous (Type u) J K).unit.app
            (J.uliftYoneda.{u}.obj V))).hom.app T.unop.unop.1 x.val)
    have he : ((representableSlice_right U V).map f).left ≫
        pullback.fst ((U.sheafPushforwardContinuous (Type u) J K).map Y.hom)
          ((U.sheafAdjunctionContinuous (Type u) J K).unit.app
            (J.uliftYoneda.{u}.obj V)) =
        pullback.fst ((U.sheafPushforwardContinuous (Type u) J K).map X.hom)
          ((U.sheafAdjunctionContinuous (Type u) J K).unit.app
            (J.uliftYoneda.{u}.obj V)) ≫
          (U.sheafPushforwardContinuous (Type u) J K).map f.left := by
      exact pullback.lift_fst _ _ _
    exact congrArg (fun g ↦ g.hom.app T.unop.unop.1 x.val) he)

private def representableSlice_fibreIso
    {E : Type u} [SmallCategory E] {T : GrothendieckTopology E}
    {B : Sheaf T (Type u)} {Q : Sheaf T RingCat.{u}}
    (slices : RingedSheafSliceAdjunctionData Q B) :
    slices.fibreEquivalence.inverse ≅ representableSlice_fibreFunctor B :=
  NatIso.ofComponents (fun X ↦ ObjectProperty.isoMk _ (slices.fibre_iso.app X))
    (by intro X Y f; apply Sheaf.hom_ext; exact slices.fibre_iso.hom.naturality f)

private def representableSlice_rightIso
    (sourceSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (J.uliftYoneda.{u}.obj V))
    (targetSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))) :
    representableSlice_right U V ⋙ sourceSlices.fibreEquivalence.inverse ≅
      targetSlices.fibreEquivalence.inverse ⋙
        (representableSliceElementFunctor U V).sheafPushforwardContinuous (Type u) _ _ :=
  isoWhiskerLeft _ (representableSlice_fibreIso sourceSlices) ≪≫
    representableSlice_rightFibreIso U V ≪≫
      isoWhiskerRight (representableSlice_fibreIso targetSlices).symm _

private def representableSlice_theta
    (sourceSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (J.uliftYoneda.{u}.obj V))
    (targetSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))) :
    sourceSlices.fibreEquivalence.inverse ⋙ representableSliceInverse U V ⟶
      Over.post (U.sheafPullback (Type u) J K) ⋙ targetSlices.fibreEquivalence.inverse :=
  ((mateEquiv (Over.postAdjunctionLeft (X := J.uliftYoneda.{u}.obj V)
    (U.sheafAdjunctionContinuous (Type u) J K))
    ((representableSliceElementFunctor U V).sheafAdjunctionContinuous (Type u) _ _)).symm
      (TwoSquare.mk _ _ _ _
        (representableSlice_rightIso U V sourceSlices targetSlices).hom)).natTrans

private theorem representableSlice_rightIso_val
    (sourceSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (J.uliftYoneda.{u}.obj V))
    (targetSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)))
    (X : Over ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)))
    (W : Cᵒᵖ) (b : (J.uliftYoneda.{u}.obj V).obj.obj W)
    (x : (sourceSlices.fibreEquivalence.inverse.obj
      ((representableSlice_right U V).obj X)).obj.obj (elementObj _ W b)) :
    ((targetSlices.fibre_iso.hom.app X).app (elementObj _ (U.op.obj W)
        (((U.sheafAdjunctionContinuous (Type u) J K).unit.app
          (J.uliftYoneda.{u}.obj V)).hom.app W b))
      (((representableSlice_rightIso U V sourceSlices targetSlices).hom.app X).hom.app
        (elementObj _ W b) x)).val =
      (pullback.fst ((U.sheafPushforwardContinuous (Type u) J K).map X.hom)
        ((U.sheafAdjunctionContinuous (Type u) J K).unit.app
          (J.uliftYoneda.{u}.obj V))).hom.app W
        (((sourceSlices.fibre_iso.hom.app ((representableSlice_right U V).obj X)).app
          (elementObj _ W b) x).val) := by
  let y := representableSlice_rightFibreEquiv U V X W b
    ((sourceSlices.fibre_iso.hom.app ((representableSlice_right U V).obj X)).app
      (elementObj _ W b) x)
  exact congrArg (fun f ↦ (f.app (elementObj _ (U.op.obj W)
    (((U.sheafAdjunctionContinuous (Type u) J K).unit.app
      (J.uliftYoneda.{u}.obj V)).hom.app W b)) y).val)
    (targetSlices.fibre_iso.inv_hom_id_app X)

private theorem representableSlice_sliceUnit_fst
    (X : Over (J.uliftYoneda.{u}.obj V)) :
    ((Over.postAdjunctionLeft (X := J.uliftYoneda.{u}.obj V)
      (U.sheafAdjunctionContinuous (Type u) J K)).unit.app X).left ≫
        pullback.fst _ _ =
      (U.sheafAdjunctionContinuous (Type u) J K).unit.app X.left := by
  dsimp [Over.postAdjunctionLeft, Adjunction.ofNatIsoLeft, Over.pullback]
  simp [Adjunction.comp_unit_app, Over.mapPullbackAdj_unit_app,
    Over.postAdjunctionRight_unit_app]

private theorem representableSlice_theta_isIso
    (sourceSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (J.uliftYoneda.{u}.obj V))
    (targetSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))) :
    IsIso (representableSlice_theta U V sourceSlices targetSlices) := by
  exact equivalentMate_isIso
    (Over.postAdjunctionLeft (X := J.uliftYoneda.{u}.obj V)
      (U.sheafAdjunctionContinuous (Type u) J K))
    ((representableSliceElementFunctor U V).sheafAdjunctionContinuous (Type u) _ _)
    sourceSlices.fibreEquivalence.symm targetSlices.fibreEquivalence.symm
    (representableSlice_rightIso U V sourceSlices targetSlices)

private theorem representableSlice_theta_unit
    (sourceSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (J.uliftYoneda.{u}.obj V))
    (targetSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)))
    (X : Over (J.uliftYoneda.{u}.obj V)) (W : Cᵒᵖ)
    (b : (J.uliftYoneda.{u}.obj V).obj.obj W)
    (x : (sourceSlices.fibreEquivalence.inverse.obj X).obj.obj (elementObj _ W b)) :
    (((targetSlices.fibre_iso.hom.app
      ((Over.post (U.sheafPullback (Type u) J K)).obj X)).app
      (elementObj _ (U.op.obj W)
        (((U.sheafAdjunctionContinuous (Type u) J K).unit.app
          (J.uliftYoneda.{u}.obj V)).hom.app W b)))
      (((((representableSliceElementFunctor U V).sheafAdjunctionContinuous
        (Type u) _ _).homEquiv _ _) (representableSlice_theta U V
          sourceSlices targetSlices |>.app X)).hom.app (elementObj _ W b) x)).val =
      ((U.sheafAdjunctionContinuous (Type u) J K).unit.app X.left).hom.app W
        (((sourceSlices.fibre_iso.hom.app X).app (elementObj _ W b) x).val) := by
  let adj := Over.postAdjunctionLeft (X := J.uliftYoneda.{u}.obj V)
    (U.sheafAdjunctionContinuous (Type u) J K)
  have hu := unit_mateEquiv_symm adj
    ((representableSliceElementFunctor U V).sheafAdjunctionContinuous (Type u) _ _)
    (TwoSquare.mk _ _ _ _ (representableSlice_rightIso U V sourceSlices targetSlices).hom) X
  have he : ((representableSliceElementFunctor U V).sheafAdjunctionContinuous
      (Type u) _ _).homEquiv _ _
        ((representableSlice_theta U V sourceSlices targetSlices).app X) =
      sourceSlices.fibreEquivalence.inverse.map (adj.unit.app X) ≫
        (representableSlice_rightIso U V sourceSlices targetSlices).hom.app _ := by
    rw [Adjunction.homEquiv_unit]
    exact hu.symm
  rw [he]
  refine (representableSlice_rightIso_val U V sourceSlices targetSlices
    ((Over.post (U.sheafPullback (Type u) J K)).obj X) W b
      ((sourceSlices.fibreEquivalence.inverse.map (adj.unit.app X)).hom.app
        (elementObj _ W b) x)).trans ?_
  have hn := sourceSlices.fibre_iso.hom.naturality (adj.unit.app X)
  have hs := congrArg (fun f ↦ (f.app (elementObj _ W b) x).val) hn
  change ((sourceSlices.fibre_iso.hom.app _).app _
    ((sourceSlices.fibreEquivalence.inverse.map (adj.unit.app X)).hom.app _ x)).val =
      (adj.unit.app X).left.hom.app W
        (((sourceSlices.fibre_iso.hom.app X).app (elementObj _ W b) x).val) at hs
  exact (congrArg ((pullback.fst
      ((U.sheafPushforwardContinuous (Type u) J K).map
        ((Over.post (U.sheafPullback (Type u) J K)).obj X).hom)
      ((U.sheafAdjunctionContinuous (Type u) J K).unit.app
        (J.uliftYoneda.{u}.obj V))).hom.app W) hs).trans
    (congrArg (fun f ↦ f.hom.app W
      (((sourceSlices.fibre_iso.hom.app X).app (elementObj _ W b) x).val))
        (representableSlice_sliceUnit_fst (J := J) (K := K) U V X))


/-- The slice inverse image formula, normalized through the fibre equivalences.
Source: Stacks Tags 03CF and 04IF
(blueprint: lem-tw-representable-slice-localized-ringed-morphism).
Proof: over an arrow b the slice right adjoint has fibre consisting of sections k
whose structure image is U(b). The global sheaf adjunction restricts to these
fibres: its unit sends x to eta_H(x), and naturality at the structure map proves
the fibre equation. This gives the Hom adjunction with inverse image Over.post L.
Its comparison with the concrete element-site adjunction is the unique
unit-preserving comparison of left adjoints. The displayed equation describes
that unit on the underlying value of every fibre, hence determines the comparison.
On G times h_V naturality of eta with both projections gives eta_G and eta_hV;
transposition gives exactly the finite-product comparison. -/
theorem representableSliceFibreComparison_unique
    (sourceSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (J.uliftYoneda.{u}.obj V))
    (targetSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))) :
    ∃! theta : sourceSlices.fibreEquivalence.inverse ⋙
        representableSliceInverse (J := J) (K := K) U V ≅
      Over.post (U.sheafPullback (Type u) J K) ⋙ targetSlices.fibreEquivalence.inverse,
      ∀ X W b x,
        (((targetSlices.fibre_iso.hom.app
          ((Over.post (U.sheafPullback (Type u) J K)).obj X)).app
          (elementObj _ (U.op.obj W)
            (((U.sheafAdjunctionContinuous (Type u) J K).unit.app
              (J.uliftYoneda.{u}.obj V)).hom.app W b)))
          (((((representableSliceElementFunctor U V).sheafAdjunctionContinuous
            (Type u) _ _).homEquiv _ _) (theta.hom.app X)).hom.app
              (elementObj (J.uliftYoneda.{u}.obj V) W b) x)).val =
          ((U.sheafAdjunctionContinuous (Type u) J K).unit.app X.left).hom.app W
            (((sourceSlices.fibre_iso.hom.app X).app
              (elementObj (J.uliftYoneda.{u}.obj V) W b) x).val) := by
  have hi := representableSlice_theta_isIso U V sourceSlices targetSlices
  refine ⟨asIso (representableSlice_theta U V sourceSlices targetSlices), ?_, ?_⟩
  · exact representableSlice_theta_unit U V sourceSlices targetSlices
  · intro gamma hg
    apply Iso.ext
    apply NatTrans.ext
    funext X
    apply (((representableSliceElementFunctor U V).sheafAdjunctionContinuous
      (Type u) _ _).homEquiv _ _).injective
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    apply ConcreteCategory.hom_ext
    intro x
    apply (ConcreteCategory.bijective_of_isIso
      ((targetSlices.fibre_iso.app
        ((Over.post (U.sheafPullback (Type u) J K)).obj X)).hom.app
          (elementObj _ (U.op.obj W.unop.unop.1)
            (((U.sheafAdjunctionContinuous (Type u) J K).unit.app
              (J.uliftYoneda.{u}.obj V)).hom.app W.unop.unop.1 W.unop.unop.2)))).1
    apply Subtype.ext
    exact (hg X W.unop.unop.1 W.unop.unop.2 x).trans
      (representableSlice_theta_unit U V sourceSlices targetSlices
        X W.unop.unop.1 W.unop.unop.2 x).symm

/-- The named fibre comparison is fixed by the global unit on each fibre.
Source: Stacks Tags 03CF and 04IF
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceFibreComparison
    (sourceSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (J.uliftYoneda.{u}.obj V))
    (targetSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))) :
    sourceSlices.fibreEquivalence.inverse ⋙ representableSliceInverse U V ≅
      Over.post (U.sheafPullback (Type u) J K) ⋙ targetSlices.fibreEquivalence.inverse :=
  Classical.choose (representableSliceFibreComparison_unique U V sourceSlices targetSlices)


/-- The product slice restriction object, using the actual sheaf product.
Source: Stacks Tags 03CF and 04IF
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceProduct
    {E : Type u} [SmallCategory E] {T : GrothendieckTopology E}
    (A G : Sheaf T (Type u)) : Over A :=
  Over.mk (CartesianMonoidalCategory.snd G A)

/-- The projection from the product fibre to G, at the presheaf level.
Source: Stacks Tags 03CF and 04IF
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceProductFibreIso
    {E : Type u} [SmallCategory E] {T : GrothendieckTopology E}
    (A G : Sheaf T (Type u)) :
    (elementFibrePresheafFunctor A).obj (representableSliceProduct A G) ≅
      ((elementSheafPullback A).obj G).obj :=
  NatIso.ofComponents (fun X ↦ {
    hom := TypeCat.ofHom (fun x ↦ x.val.1)
    inv := TypeCat.ofHom (fun g ↦ ⟨(g, X.unop.unop.2), rfl⟩)
    hom_inv_id := by ext x; apply Subtype.ext; exact Prod.ext rfl x.property.symm
    inv_hom_id := by rfl }) (by intros; rfl)

/-- Finite-product preservation in the slice, written with its two projections.
Source: Stacks Tags 03CF and 04IF
(blueprint: lem-tw-representable-slice-localized-ringed-morphism).
Proof: finite-limit preservation makes the product comparison invertible.
Its second projection is L of the second projection, so it is a map over LA;
the inverse satisfies the over condition by cancelling the comparison. Thus
it is the asserted slice isomorphism. -/
theorem representableSliceProductComparison_unique
    (G : Sheaf J (Type u)) :
    ∃! p :
      (Over.post (U.sheafPullback (Type u) J K)).obj
        (representableSliceProduct (J.uliftYoneda.{u}.obj V) G) ≅
      representableSliceProduct
        ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))
        ((U.sheafPullback (Type u) J K).obj G),
      p.hom.left = CartesianMonoidalCategory.prodComparison
        (U.sheafPullback (Type u) J K) G (J.uliftYoneda.{u}.obj V) := by
  have : PreservesFiniteLimits (U.sheafPullback (Type u) J K) :=
    by
      have : RepresentablyFlat U := flat_of_preservesFiniteLimits U
      exact Functor.sheafPullbackConstruction.preservesFiniteLimits U (Type u) J K
  let L := U.sheafPullback (Type u) J K
  let h := CartesianMonoidalCategory.prodComparison L G (J.uliftYoneda.{u}.obj V)
  have : IsIso h := by dsimp [h, L]; infer_instance
  let p : (Over.post L).obj
      (representableSliceProduct (J.uliftYoneda.{u}.obj V) G) ≅
      representableSliceProduct (L.obj (J.uliftYoneda.{u}.obj V)) (L.obj G) :=
    Over.isoMk (asIso h) (by
      exact CartesianMonoidalCategory.prodComparison_snd L G (J.uliftYoneda.{u}.obj V))
  refine ⟨p, rfl, ?_⟩
  intro q hq
  apply Iso.ext
  apply Over.OverMorphism.ext
  exact hq

/-- The canonical finite-product comparison in the sheaf slice.
Source: Stacks Tags 03CF and 04IF
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceProductComparison (G : Sheaf J (Type u)) :
    (Over.post (U.sheafPullback (Type u) J K)).obj
      (representableSliceProduct (J.uliftYoneda.{u}.obj V) G) ≅
    representableSliceProduct
      ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))
      ((U.sheafPullback (Type u) J K).obj G) :=
  Classical.choose (representableSliceProductComparison_unique (J := J) (K := K) U V G)


/-- The fibre identification of the product restriction, with the recorded fibre_iso.
Source: Stacks Tags 03CF and 04IF
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceRestrictionFibreIso
    {E : Type u} [SmallCategory E] {T : GrothendieckTopology E}
    {B : Sheaf T (Type u)} {Q : Sheaf T RingCat.{u}}
    (slices : RingedSheafSliceAdjunctionData Q B) (G : Sheaf T (Type u)) :
    slices.fibreEquivalence.inverse.obj (representableSliceProduct B G) ≅
      (elementSheafPullback B).obj G :=
  ObjectProperty.isoMk _ (slices.fibre_iso.app (representableSliceProduct B G) ≪≫
    representableSliceProductFibreIso B G)

/-- The module localization adjunction transported along its canonical pullback equation.
Source: Stacks Tags 04IE and 04IF
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceLocalizationAdjunction
    {E : Type u} [SmallCategory E] {T : GrothendieckTopology E}
    {B : Sheaf T (Type u)} {Q : Sheaf T RingCat.{u}}
    (slices : RingedSheafSliceAdjunctionData Q B) :
    elementModulePullback Q B ⊣ slices.localization.modules :=
  slices.localization_modules.ofNatIsoLeft (eqToIso slices.pullback_eq)

/-- The canonical right-adjoint localization square obtained from sectionwise identity.
Source: Stacks Tags 04IF and 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceModuleLocalizationSquare
    (sourceSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (J.uliftYoneda.{u}.obj V))
    (targetSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))) :
    TwoSquare targetSlices.localization.modules
      (SheafOfModules.pushforward (representableSliceRingMap U a V))
      (SheafOfModules.pushforward (SheafOfModules.ringedSiteModuleMap U a))
      sourceSlices.localization.modules :=
  (mateEquiv (representableSliceLocalizationAdjunction targetSlices)
    (representableSliceLocalizationAdjunction sourceSlices))
      (TwoSquare.mk _ _ _ _ (representableSliceModulePushforwardIso U a V).hom)

set_option linter.unusedVariables false in
/-- The module restriction comparison computed through the localization adjunctions.
First recover the fixed sectionwise identity from its vertical mate, then take
its horizontal inverse mate. This is the canonical mu inverse.
Source: Stacks Tags 04IF and 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism). -/
def representableSliceModuleRestrictionMate
    (sourceSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (J.uliftYoneda.{u}.obj V))
    (targetSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))) :
    elementModulePullback ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        (J.uliftYoneda.{u}.obj V) ⋙ representableSliceModulePullback U a V ⟶
      SheafOfModules.pullback.{u} (SheafOfModules.ringedSiteModuleMap U a) ⋙
        elementModulePullback ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
          ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)) :=
  representableSliceModulePullbackMap U a V


private theorem representableSlice_inverseMatePasting
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {L₃ : E ⥤ F} {R₃ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (b₁ : TwoSquare R₁ H₁ G₁ R₂) (b₂ : TwoSquare R₂ H₂ G₂ R₃) :
    TwoSquare.hComp ((mateEquiv a₁ a₂).symm b₁) ((mateEquiv a₂ a₃).symm b₂) =
      (mateEquiv a₁ a₃).symm (TwoSquare.vComp b₁ b₂) := by
  apply (mateEquiv a₁ a₃).injective
  rw [mateEquiv_vcomp, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

private theorem representableSlice_setPullback_unit (G : Sheaf J (Type u)) :
    (((representableSliceElementFunctor (J := J) (K := K) U V).sheafAdjunctionContinuous (Type u)
    (elementTopology (J.uliftYoneda.{u}.obj V))
    (elementTopology ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)))).homEquiv
      _ _) ((representableSliceSetPullbackMap U V).app G) =
      (elementSheafPullback (J.uliftYoneda.{u}.obj V)).map
        ((U.sheafAdjunctionContinuous (Type u) J K).unit.app G) := by
  rw [Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm (U.sheafAdjunctionContinuous (Type u) J K)
    ((representableSliceElementFunctor (J := J) (K := K) U V).sheafAdjunctionContinuous (Type u)
    (elementTopology (J.uliftYoneda.{u}.obj V))
    (elementTopology ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))))
    (TwoSquare.mk _ _ _ _ (representableSliceSetPushforwardIso U V).hom) G).symm

private theorem representableSlice_productProjection
    (targetSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)))
    (G : Sheaf J (Type u))
    (W : Dᵒᵖ)
    (b : ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)).obj.obj W)
    (x : (targetSlices.fibreEquivalence.inverse.obj
      ((Over.post (U.sheafPullback (Type u) J K)).obj
        (representableSliceProduct (J.uliftYoneda.{u}.obj V) G))).obj.obj
          (elementObj _ W b)) :
    ((targetSlices.fibreEquivalence.inverse.map
        (representableSliceProductComparison U V G).hom ≫
      (representableSliceRestrictionFibreIso targetSlices
        ((U.sheafPullback (Type u) J K).obj G)).hom).hom.app (elementObj _ W b) x) =
      ((U.sheafPullback (Type u) J K).map
        (CartesianMonoidalCategory.fst G (J.uliftYoneda.{u}.obj V))).hom.app W
        (((targetSlices.fibre_iso.hom.app
          ((Over.post (U.sheafPullback (Type u) J K)).obj
            (representableSliceProduct (J.uliftYoneda.{u}.obj V) G))).app
              (elementObj _ W b) x).val) := by
  have hn := targetSlices.fibre_iso.hom.naturality
    (representableSliceProductComparison U V G).hom
  have hs := congrArg (fun f ↦ (f.app (elementObj _ W b) x).val.1) hn
  change _ = (((representableSliceProductComparison U V G).hom.left).hom.app W
    (((targetSlices.fibre_iso.hom.app _).app (elementObj _ W b) x).val)).1 at hs
  change _ = _
  refine hs.trans ?_
  have hp := (Classical.choose_spec
    (representableSliceProductComparison_unique (J := J) (K := K) U V G)).1
  have he := CartesianMonoidalCategory.prodComparison_fst
    (U.sheafPullback (Type u) J K) G (J.uliftYoneda.{u}.obj V)
  rw [← hp] at he
  exact congrArg (fun f ↦ f.hom.app W
    (((targetSlices.fibre_iso.hom.app _).app (elementObj _ W b) x).val)) he

private theorem representableSlice_productNormalization
    (sourceSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (J.uliftYoneda.{u}.obj V))
    (targetSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)))
    (G : Sheaf J (Type u)) :
    (representableSliceInverse (J := J) (K := K) U V).map
        (representableSliceRestrictionFibreIso sourceSlices G).hom ≫
      (representableSliceSetPullbackMap (J := J) (K := K) U V).app G =
    (representableSliceFibreComparison U V sourceSlices targetSlices).hom.app
        (representableSliceProduct (J.uliftYoneda.{u}.obj V) G) ≫
      targetSlices.fibreEquivalence.inverse.map
        (representableSliceProductComparison (J := J) (K := K) U V G).hom ≫
      (representableSliceRestrictionFibreIso targetSlices
        ((U.sheafPullback (Type u) J K).obj G)).hom := by
  let adj :=
    (representableSliceElementFunctor (J := J) (K := K) U V).sheafAdjunctionContinuous
      (Type u)
    (elementTopology (J.uliftYoneda.{u}.obj V))
    (elementTopology ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)))
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, representableSlice_setPullback_unit,
    Adjunction.homEquiv_naturality_right]
  ext W x
  have htheta := (Classical.choose_spec
    (representableSliceFibreComparison_unique U V sourceSlices targetSlices)).1
      (representableSliceProduct (J.uliftYoneda.{u}.obj V) G)
      W.unop.unop.1 W.unop.unop.2 x
  have hp := representableSlice_productProjection U V targetSlices G
    (U.op.obj W.unop.unop.1)
    (((U.sheafAdjunctionContinuous (Type u) J K).unit.app
      (J.uliftYoneda.{u}.obj V)).hom.app W.unop.unop.1 W.unop.unop.2)
    (((adj.homEquiv _ _)
      ((representableSliceFibreComparison U V sourceSlices targetSlices).hom.app
        (representableSliceProduct (J.uliftYoneda.{u}.obj V) G))).hom.app W x)
  refine Eq.trans ?_ hp.symm
  have hv := congrArg (fun y ↦ ((U.sheafPullback (Type u) J K).map
      (CartesianMonoidalCategory.fst G (J.uliftYoneda.{u}.obj V))).hom.app
        (U.op.obj W.unop.unop.1) y) htheta
  have hn := congrArg (fun f ↦ f.hom.app W.unop.unop.1
    (((sourceSlices.fibre_iso.hom.app
      (representableSliceProduct (J.uliftYoneda.{u}.obj V) G)).app W x).val))
    ((U.sheafAdjunctionContinuous (Type u) J K).unit.naturality
      (CartesianMonoidalCategory.fst G (J.uliftYoneda.{u}.obj V)))
  exact hn.trans hv.symm
private theorem representableSlice_structural
    : representableSliceStructuralMap U a V =
      (representableSliceSetPullbackMap (J := J) (K := K) U V).app
          ((sheafCompose J (forget CommRingCat)).obj R) ≫
        (elementSheafPullback
          ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))).map
          (((U.sheafAdjunctionContinuous (Type u) J K).homEquiv
            ((sheafCompose J (forget CommRingCat)).obj R)
            ((sheafCompose K (forget CommRingCat)).obj S)).symm
            (ObjectProperty.homMk (Functor.whiskerRight a.hom (forget CommRingCat)))) := by
  let adj :=
    (representableSliceElementFunctor (J := J) (K := K) U V).sheafAdjunctionContinuous
      (Type u)
    (elementTopology (J.uliftYoneda.{u}.obj V))
    (elementTopology ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)))
  let g := (((U.sheafAdjunctionContinuous (Type u) J K).homEquiv
    ((sheafCompose J (forget CommRingCat)).obj R)
    ((sheafCompose K (forget CommRingCat)).obj S)).symm
      (ObjectProperty.homMk (Functor.whiskerRight a.hom (forget CommRingCat))))
  apply (adj.homEquiv _ _).injective
  rw [representableSliceStructuralMap, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right]
  change representableSliceUnderlyingCoefficientMap U a V =
    (adj.homEquiv
      ((elementSheafPullback (J.uliftYoneda.{u}.obj V)).obj
        ((sheafCompose J (forget CommRingCat)).obj R)) _)
      ((representableSliceSetPullbackMap U V).app _) ≫ _
  rw [representableSlice_setPullback_unit]
  ext W x
  change a.hom.app W.unop.unop.1 x =
    g.hom.app (U.op.obj W.unop.unop.1)
      (((U.sheafAdjunctionContinuous (Type u) J K).unit.app
        ((sheafCompose J (forget CommRingCat)).obj R)).hom.app W.unop.unop.1 x)
  have hg : (U.sheafAdjunctionContinuous (Type u) J K).homEquiv _ _ g =
      ObjectProperty.homMk (Functor.whiskerRight a.hom (forget CommRingCat)) :=
    Equiv.apply_symm_apply _ _
  exact (congrArg (fun f ↦ f.hom.app W.unop.unop.1 x) hg).symm

private theorem representableSlice_setPasting (G : Sheaf J (Type u)) :
    (representableSliceSetChartPullbackMap (J := J) (K := K) U V).app
        ((elementSheafPullback (J.uliftYoneda.{u}.obj V)).obj G) ≫
      (representableRingedSliceSets (U.obj V)
        (representableRingedSliceImageIso (J := J) (K := K) U V)).map
          ((representableSliceSetPullbackMap (J := J) (K := K) U V).app G) ≫
      (representableRingedSliceRestrictionIso (U.obj V)
        (representableRingedSliceImageIso (J := J) (K := K) U V)).hom.app
          ((U.sheafPullback (Type u) J K).obj G) =
    ((Over.post (X := V) U).sheafPullback (Type u)
      (J.over V) (K.over (U.obj V))).map
        ((representableRingedSliceRestrictionIso V
          (Iso.refl (J.uliftYoneda.{u}.obj V))).hom.app G) ≫
      (sliceSetPullbackMap (K := J) (J := K) U V).app G := by
  let a₀ := U.sheafAdjunctionContinuous (Type u) J K
  let a₁ :=
    (representableSliceElementFunctor (J := J) (K := K) U V).sheafAdjunctionContinuous
      (Type u)
    (elementTopology (J.uliftYoneda.{u}.obj V))
    (elementTopology ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V)))
  let a₂ := (Over.post (X := V) U).sheafAdjunctionContinuous (Type u)
    (J.over V) (K.over (U.obj V))
  let b₀ := TwoSquare.mk _ _ _ _ (representableSliceSetPushforwardIso (J := J) (K := K) U V).hom
  let b₁ := TwoSquare.mk _ _ _ _
    (representableSliceSetChartPushforwardIso (J := J) (K := K) U V).hom
  have hb : TwoSquare.vComp b₀ b₁ =
      TwoSquare.mk _ _ _ _ (sliceSetPushforwardIso (K := J) (J := K) U V).hom := by
    ext M T x
    exact eq_of_heq ((Classical.choose_spec
      (representableSliceSetChartPushforward_unique (J := J) (K := K) U V)).1
        ((elementSheafPullback ((U.sheafPullback (Type u) J K).obj
          (J.uliftYoneda.{u}.obj V))).obj M) T.unop x)
  have hp : TwoSquare.hComp ((mateEquiv a₀ a₁).symm b₀)
      ((mateEquiv a₁ a₂).symm b₁) =
      (mateEquiv a₀ a₂).symm (TwoSquare.vComp b₀ b₁) :=
    representableSlice_inverseMatePasting a₀ a₁ a₂ b₀ b₁
  rw [hb] at hp
  have hc := congrArg (fun b ↦ b.natTrans.app G) hp
  change (representableSliceSetChartPullbackMap (J := J) (K := K) U V).app _ ≫
    (representableRingedSliceSets (U.obj V) (representableRingedSliceImageIso U V)).map
      ((representableSliceSetPullbackMap (J := J) (K := K) U V).app G) =
    (sliceSetPullbackMap (K := J) (J := K) U V).app G at hc
  have hC : (representableRingedSliceRestrictionIso V
      (Iso.refl (J.uliftYoneda.{u}.obj V))).hom.app G = 𝟙 _ := by
    ext T x
    rfl
  have hD : (representableRingedSliceRestrictionIso (U.obj V)
      (representableRingedSliceImageIso (J := J) (K := K) U V)).hom.app
        ((U.sheafPullback (Type u) J K).obj G) = 𝟙 _ := by
    ext T x
    rfl
  rw [hC, hD]
  change _ ≫ _ ≫ 𝟙 ((K.overPullback (Type u) (U.obj V)).obj
    ((U.sheafPullback (Type u) J K).obj G)) =
      ((Over.post (X := V) U).sheafPullback (Type u)
        (J.over V) (K.over (U.obj V))).map
          (𝟙 ((J.overPullback (Type u) V).obj G)) ≫ _
  rw [Category.comp_id, Functor.map_id, Category.id_comp]
  exact hc
private theorem representableSlice_mateNaturality
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (a' : L' ⊣ R')
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (b : TwoSquare R H G R') (b' : TwoSquare R H' G' R')
    (c : G ⟶ G') (d : H ⟶ H')
    (hb : b.natTrans ≫ whiskerRight d R' = whiskerLeft R c ≫ b'.natTrans) :
    ((mateEquiv a a').symm b).natTrans ≫ whiskerLeft L d =
      whiskerRight c L' ≫ ((mateEquiv a a').symm b').natTrans := by
  apply NatTrans.ext
  funext X
  apply (a'.homEquiv _ _).injective
  change (a'.homEquiv _ _)
    ((((mateEquiv a a').symm b).natTrans.app X) ≫ d.app (L.obj X)) =
      (a'.homEquiv _ _) (L'.map (c.app X) ≫
        (((mateEquiv a a').symm b').natTrans.app X))
  rw [a'.homEquiv_naturality_right, a'.homEquiv_naturality_left]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have h₁ := (unit_mateEquiv_symm a a' b X).symm
  change a'.unit.app (G.obj X) ≫
    R'.map (((mateEquiv a a').symm b).natTrans.app X) =
      G.map (a.unit.app X) ≫ b.natTrans.app (L.obj X) at h₁
  have h₂ := (unit_mateEquiv_symm a a' b' X).symm
  change a'.unit.app (G'.obj X) ≫
    R'.map (((mateEquiv a a').symm b').natTrans.app X) =
      G'.map (a.unit.app X) ≫ b'.natTrans.app (L.obj X) at h₂
  rw [h₁, h₂]
  have he := congrArg (fun t ↦ t.app (L.obj X)) hb
  change b.natTrans.app (L.obj X) ≫ R'.map (d.app (L.obj X)) =
    c.app (R.obj (L.obj X)) ≫ b'.natTrans.app (L.obj X) at he
  rw [Category.assoc, he, ← Category.assoc]
  exact (congrArg (fun k ↦ k ≫ b'.natTrans.app (L.obj X))
    (c.naturality (a.unit.app X))).trans (Category.assoc _ _ _)
private theorem representableSlice_fullMatePasting
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {L₃ : E ⥤ F} {R₃ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (b₁ : TwoSquare R₁ H₁ G₁ R₂) (b₂ : TwoSquare R₂ H₂ G₂ R₃)
    {G : A ⥤ E} {H : B ⥤ F} (b : TwoSquare R₁ H G R₃)
    (c : G₁ ⋙ G₂ ⟶ G) (d : H₁ ⋙ H₂ ⟶ H)
    (hb : (TwoSquare.vComp b₁ b₂).natTrans ≫ whiskerRight d R₃ =
      whiskerLeft R₁ c ≫ b.natTrans) :
    (TwoSquare.hComp ((mateEquiv a₁ a₂).symm b₁)
      ((mateEquiv a₂ a₃).symm b₂)).natTrans ≫ whiskerLeft L₁ d =
      whiskerRight c L₃ ≫ ((mateEquiv a₁ a₃).symm b).natTrans := by
  rw [representableSlice_inverseMatePasting]
  exact representableSlice_mateNaturality a₁ a₃ _ b c d hb

private theorem representableSlice_fullMatePasting_app
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {L₃ : E ⥤ F} {R₃ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (b₁ : TwoSquare R₁ H₁ G₁ R₂) (b₂ : TwoSquare R₂ H₂ G₂ R₃)
    {G : A ⥤ E} {H : B ⥤ F} (b : TwoSquare R₁ H G R₃)
    (c : G₁ ⋙ G₂ ⟶ G) (d : H₁ ⋙ H₂ ⟶ H)
    (hb : (TwoSquare.vComp b₁ b₂).natTrans ≫ whiskerRight d R₃ =
      whiskerLeft R₁ c ≫ b.natTrans) (X : A) :
    (((mateEquiv a₂ a₃).symm b₂).natTrans.app (G₁.obj X)) ≫
      H₂.map (((mateEquiv a₁ a₂).symm b₁).natTrans.app X) ≫
        d.app (L₁.obj X) =
      L₃.map (c.app X) ≫ (((mateEquiv a₁ a₃).symm b).natTrans.app X) := by
  have h := congrArg (fun t ↦ t.app X)
    (representableSlice_fullMatePasting a₁ a₂ a₃ b₁ b₂ b c d hb)
  simpa only [TwoSquare.hComp_app, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, Category.comp_id, Category.id_comp, Category.assoc] using h

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem representableSlice_mateIsoOfPasting
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {L₃ : E ⥤ F} {R₃ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (b₁ : TwoSquare R₁ H₁ G₁ R₂) (b₂ : TwoSquare R₂ H₂ G₂ R₃)
    {G : A ⥤ E} {H : B ⥤ F} (b : TwoSquare R₁ H G R₃)
    (c : G₁ ⋙ G₂ ⟶ G) (d : H₁ ⋙ H₂ ⟶ H)
    (hb : (TwoSquare.vComp b₁ b₂).natTrans ≫ whiskerRight d R₃ =
      whiskerLeft R₁ c ≫ b.natTrans) [hReflect : H₂.ReflectsIsomorphisms]
    [hC : IsIso c] [hD : IsIso d]
    [h₂ : IsIso (((mateEquiv a₂ a₃).symm b₂).natTrans)]
    [h₃ : IsIso (((mateEquiv a₁ a₃).symm b).natTrans)] :
    IsIso (((mateEquiv a₁ a₂).symm b₁).natTrans) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  have h := representableSlice_fullMatePasting_app a₁ a₂ a₃ b₁ b₂ b c d hb X
  have hi : IsIso
      ((((mateEquiv a₂ a₃).symm b₂).natTrans.app (G₁.obj X)) ≫
        H₂.map (((mateEquiv a₁ a₂).symm b₁).natTrans.app X) ≫ d.app (L₁.obj X)) := by
    rw [h]
    infer_instance
  have := IsIso.of_isIso_comp_left
    (((mateEquiv a₂ a₃).symm b₂).natTrans.app (G₁.obj X))
    (H₂.map (((mateEquiv a₁ a₂).symm b₁).natTrans.app X) ≫ d.app (L₁.obj X))
  have := IsIso.of_isIso_comp_right
    (H₂.map (((mateEquiv a₁ a₂).symm b₁).natTrans.app X)) (d.app (L₁.obj X))
  exact isIso_of_reflects_iso _ H₂

set_option linter.defProp false in
private def representableSlice_modulePasting :=
  let a₀ := representableSliceGlobalModuleAdjunction U a
  let a₁ := representableSliceModuleAdjunction U a V
  let a₂ := representableSliceLocalizedModuleAdjunction U a V
  let b₀ := TwoSquare.mk _ _ _ _ (representableSliceModulePushforwardIso U a V).hom
  let b₁ := TwoSquare.mk _ _ _ _ (representableSliceModuleChartPushforwardIso U a V).hom
  let b₂ := TwoSquare.mk _ _ _ _ (SheafOfModules.sliceModulePushforwardIso U
      (SheafOfModules.ringedSiteModuleMap U a) V).hom
  let c := (representableRingedSliceModuleRestrictionIso
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) V
      (Iso.refl (J.uliftYoneda.{u}.obj V))).hom
  let d := (representableRingedSliceModuleRestrictionIso
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S) (U.obj V)
      (representableRingedSliceImageIso (J := J) (K := K) U V)).hom
  representableSlice_fullMatePasting_app a₀ a₁ a₂ b₀ b₁ b₂ c d (by
    apply NatTrans.ext
    funext N
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro T
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact eq_of_heq ((Classical.choose_spec
      (representableSliceModuleChartPushforward_unique U a V)).1
        ((elementModulePullback ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
          ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))).obj N) T.unop x))

private theorem representableSlice_moduleIsIso
    [hChart : IsIso (representableSliceModuleChartPullbackMap U a V)]
    [hLocal : IsIso (SheafOfModules.sliceModulePullbackMap U
      (SheafOfModules.ringedSiteModuleMap U a) V)]
    [hReflect : (representableRingedSliceModules
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S) (U.obj V)
      (representableRingedSliceImageIso (J := J) (K := K) U V)).ReflectsIsomorphisms] :
    IsIso (representableSliceModulePullbackMap U a V) := by
  let a₀ := representableSliceGlobalModuleAdjunction U a
  let a₁ := representableSliceModuleAdjunction U a V
  let a₂ := representableSliceLocalizedModuleAdjunction U a V
  let b₀ := TwoSquare.mk _ _ _ _ (representableSliceModulePushforwardIso U a V).hom
  let b₁ := TwoSquare.mk _ _ _ _ (representableSliceModuleChartPushforwardIso U a V).hom
  let b₂ := TwoSquare.mk _ _ _ _ (SheafOfModules.sliceModulePushforwardIso U
      (SheafOfModules.ringedSiteModuleMap U a) V).hom
  let c := (representableRingedSliceModuleRestrictionIso
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) V
      (Iso.refl (J.uliftYoneda.{u}.obj V))).hom
  let d := (representableRingedSliceModuleRestrictionIso
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S) (U.obj V)
      (representableRingedSliceImageIso (J := J) (K := K) U V)).hom
  have hAlpha : IsIso (((mateEquiv a₁ a₂).symm b₁).natTrans) := by
    unfold representableSliceModuleChartPullbackMap at hChart
    exact hChart
  have hSigma : IsIso (((mateEquiv a₀ a₂).symm b₂).natTrans) := by
    unfold SheafOfModules.sliceModulePullbackMap at hLocal
    simpa only [a₀, a₂, b₂, representableSliceGlobalModuleAdjunction,
      representableSliceLocalizedModuleAdjunction] using hLocal
  have result := representableSlice_mateIsoOfPasting a₀ a₁ a₂ b₀ b₁ b₂ c d
    (h₂ := hAlpha) (h₃ := hSigma) (hReflect := hReflect)
    (hC := Iso.isIso_hom _) (hD := Iso.isIso_hom _) (by
    apply NatTrans.ext
    funext N
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro T
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact eq_of_heq ((Classical.choose_spec
      (representableSliceModuleChartPushforward_unique U a V)).1
        ((elementModulePullback ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
          ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))).obj N) T.unop x))
  simpa only [representableSliceModulePullbackMap] using result

private theorem representableSlice_reflectIsoOfPasting
    {E F : Type*} [Category E] [Category F] (T : E ⥤ F) [T.ReflectsIsomorphisms]
    {X Y : E} {A B : F} (f : X ⟶ Y) (g : A ⟶ T.obj X) (h : T.obj Y ⟶ B)
    [IsIso g] [IsIso h] [IsIso (g ≫ T.map f ≫ h)] : IsIso f := by
  have := IsIso.of_isIso_comp_left g (T.map f ≫ h)
  have := IsIso.of_isIso_comp_right (T.map f) h
  exact isIso_of_reflects_iso f T

attribute [local irreducible] representableSliceModuleChartPullbackMap
  representableSliceSetChartPullbackMap
  representableSliceSetPullbackMap representableSliceStructuralMap
  representableSliceModulePullbackMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Representable localization identifies the concrete slice ringed morphism with
localized sites and modules, with the canonical product and restriction normalizations.

Source: Stacks Tags 03CF and 04D3; Modules on Sites Tags 04J0, 04IF and 04J7
(blueprint: lem-tw-representable-slice-localized-ringed-morphism).

Proof:
1. The charts send an arrow b to its represented element, and c_V identifies the
   target chart. The adjunct formula c_V eta = beta sends this element to U(b).
   Coverings agree under the charts, giving equivalences also for restricted rings
   and modules, since their coefficients at W are literally R(W) and S(W).
2. The specified element functor is the unit-induced map (W,b) to (UW,eta(b)).
   Its coefficient map is a_W. Its continuous adjunction and the unique ringed
   structure above define the slice morphism, with no free geometric or ring data.
   Transposing on each fibre gives the named theta: (H,phi) maps to (LH,Lphi).
3. For G times h_V, the fibre projection is the displayed product fibre map.
   Naturality of the global unit with both projections shows that theta on this
   object followed by the finite-product comparison is precisely the named set
   restriction mate. This proves the product normalization and its invertibility.
4. The set chart square is sectionwise identity, so its inverse mate is the
   canonical inverse-image chart comparison. Pasting its direct-image square with
   the element restriction square is the original localized direct-image square.
   Taking mates proves the displayed set restriction equality.
5. Apply that normalization to the underlying ring R. The element coefficient
   map is restriction of a, hence its transpose is restriction of c after the
   named product comparison. This proves the structural-map equation, including
   all ring operations, identifying the ringed morphisms.
6. The module chart square and module restriction square are the specified
   sectionwise identities with the same scalar action. The localization square
   is their right mate under sourceSlices.localization_modules and
   targetSlices.localization_modules; transposing it back gives the same identity.
   Its horizontal inverse mate is the named module restriction map. Uniqueness of
   mates therefore identifies it with the usual restriction comparison with f*.
   Taking inverse mates of the pasted module squares proves the last equality.
   The chart equivalences and module adjunctions imply that both module mates
   are invertible. No flatness or invertibility of c is needed. -/
theorem representable_slice_localized_ringed_morphism
    [PreservesFiniteLimits (U.sheafPullback (Type u) J K)]
    (sourceSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (J.uliftYoneda.{u}.obj V))
    (targetSlices : RingedSheafSliceAdjunctionData
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))) :
    (representableRingedSliceModules
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) V
      (Iso.refl (J.uliftYoneda.{u}.obj V))).IsEquivalence ∧
    (representableRingedSliceModules
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S) (U.obj V)
      (representableRingedSliceImageIso (J := J) (K := K) U V)).IsEquivalence ∧
    IsIso (representableSliceSetPullbackMap (J := J) (K := K) U V) ∧
    IsIso (representableSliceSetChartPullbackMap (J := J) (K := K) U V) ∧
    IsIso (representableSliceModuleRestrictionMate U a V sourceSlices targetSlices) ∧
    IsIso (representableSliceModuleChartPullbackMap U a V) ∧
    (∀ G : Sheaf J (Type u),
      (representableSliceInverse (J := J) (K := K) U V).map
          (representableSliceRestrictionFibreIso sourceSlices G).hom ≫
        (representableSliceSetPullbackMap (J := J) (K := K) U V).app G =
      (representableSliceFibreComparison U V sourceSlices targetSlices).hom.app
          (representableSliceProduct (J.uliftYoneda.{u}.obj V) G) ≫
        targetSlices.fibreEquivalence.inverse.map
          (representableSliceProductComparison (J := J) (K := K) U V G).hom ≫
        (representableSliceRestrictionFibreIso targetSlices
          ((U.sheafPullback (Type u) J K).obj G)).hom) ∧
    (representableSliceStructuralMap U a V =
      (representableSliceSetPullbackMap (J := J) (K := K) U V).app
          ((sheafCompose J (forget CommRingCat)).obj R) ≫
        (elementSheafPullback
          ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))).map
          (((U.sheafAdjunctionContinuous (Type u) J K).homEquiv
            ((sheafCompose J (forget CommRingCat)).obj R)
            ((sheafCompose K (forget CommRingCat)).obj S)).symm
            (ObjectProperty.homMk (Functor.whiskerRight a.hom (forget CommRingCat))))) ∧
    (∀ G : Sheaf J (Type u),
      (representableSliceSetChartPullbackMap (J := J) (K := K) U V).app
          ((elementSheafPullback (J.uliftYoneda.{u}.obj V)).obj G) ≫
        (representableRingedSliceSets (U.obj V)
          (representableRingedSliceImageIso (J := J) (K := K) U V)).map
            ((representableSliceSetPullbackMap (J := J) (K := K) U V).app G) ≫
        (representableRingedSliceRestrictionIso (U.obj V)
          (representableRingedSliceImageIso (J := J) (K := K) U V)).hom.app
            ((U.sheafPullback (Type u) J K).obj G) =
      ((Over.post (X := V) U).sheafPullback (Type u) _ _).map
          ((representableRingedSliceRestrictionIso V
            (Iso.refl (J.uliftYoneda.{u}.obj V))).hom.app G) ≫
        (sliceSetPullbackMap (K := J) (J := K) U V).app G) ∧
    (∀ M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
      (representableSliceModuleChartPullbackMap U a V).app
          ((elementModulePullback ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
            (J.uliftYoneda.{u}.obj V)).obj M) ≫
        (representableRingedSliceModules
          ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S) (U.obj V)
          (representableRingedSliceImageIso (J := J) (K := K) U V)).map
            ((representableSliceModuleRestrictionMate U a V sourceSlices targetSlices).app M) ≫
        (representableRingedSliceModuleRestrictionIso
          ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S) (U.obj V)
          (representableRingedSliceImageIso (J := J) (K := K) U V)).hom.app
            ((SheafOfModules.pullback.{u} (F := U) (J := J) (K := K)
              (S := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
              (R := (sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
              (SheafOfModules.ringedSiteModuleMap U a)).obj M) =
      (SheafOfModules.pullback.{u} (F := Over.post (X := V) U)
        (J := J.over V) (K := K.over (U.obj V))
        (S := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)
        (R := ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S).over (U.obj V))
        (SheafOfModules.sliceModuleRingMap U
        (SheafOfModules.ringedSiteModuleMap U a) V)).map
            ((representableRingedSliceModuleRestrictionIso
              ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) V
              (Iso.refl (J.uliftYoneda.{u}.obj V))).hom.app M) ≫
        (SheafOfModules.sliceModulePullbackMap U
          (SheafOfModules.ringedSiteModuleMap U a) V).app M) := by
  have hMC := representableSlice_modulesChart_equivalence
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) V
    (Iso.refl (J.uliftYoneda.{u}.obj V))
  have hMD := representableSlice_modulesChart_equivalence
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S) (U.obj V)
    (representableRingedSliceImageIso (J := J) (K := K) U V)
  have hSC := representableSlice_setsChart_equivalence V
    (Iso.refl (J.uliftYoneda.{u}.obj V))
  have hSD := representableSlice_setsChart_equivalence (U.obj V)
    (representableRingedSliceImageIso (J := J) (K := K) U V)
  have hAlpha : IsIso (representableSliceSetChartPullbackMap (J := J) (K := K) U V) := by
    unfold representableSliceSetChartPullbackMap
    exact equivalentMate_isIso
      ((representableSliceElementFunctor (J := J) (K := K) U V).sheafAdjunctionContinuous (Type u)
    (elementTopology (J.uliftYoneda.{u}.obj V))
    (elementTopology ((U.sheafPullback (Type u) J K).obj (J.uliftYoneda.{u}.obj V))))
      ((Over.post (X := V) U).sheafAdjunctionContinuous (Type u)
    (J.over V) (K.over (U.obj V)))
      (representableRingedSliceSets V (Iso.refl (J.uliftYoneda.{u}.obj V))).asEquivalence
      (representableRingedSliceSets (U.obj V)
        (representableRingedSliceImageIso (J := J) (K := K) U V)).asEquivalence
      (representableSliceSetChartPushforwardIso U V)
  have hLambda : IsIso (representableSliceModuleChartPullbackMap U a V) := by
    unfold representableSliceModuleChartPullbackMap
    exact equivalentMate_isIso
      (representableSliceModuleAdjunction U a V)
      (representableSliceLocalizedModuleAdjunction U a V)
      (representableRingedSliceModules
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) V
        (Iso.refl (J.uliftYoneda.{u}.obj V))).asEquivalence
      (representableRingedSliceModules
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S) (U.obj V)
        (representableRingedSliceImageIso (J := J) (K := K) U V)).asEquivalence
      (representableSliceModuleChartPushforwardIso U a V)
  have hQ : IsIso (representableSliceSetPullbackMap (J := J) (K := K) U V) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro G
    let F := representableRingedSliceSets (U.obj V)
      (representableRingedSliceImageIso (J := J) (K := K) U V)
    have := sliceSetPullbackMap_isIso (K := J) (J := K) U V
    have h := representableSlice_setPasting (J := J) (K := K) U V G
    have hi : IsIso ((representableSliceSetChartPullbackMap (J := J) (K := K) U V).app _ ≫
        F.map ((representableSliceSetPullbackMap (J := J) (K := K) U V).app G) ≫
        (representableRingedSliceRestrictionIso (U.obj V)
          (representableRingedSliceImageIso (J := J) (K := K) U V)).hom.app _) := by
      rw [h]
      infer_instance
    exact representableSlice_reflectIsoOfPasting F
      ((representableSliceSetPullbackMap (J := J) (K := K) U V).app G)
      ((representableSliceSetChartPullbackMap (J := J) (K := K) U V).app _)
      ((representableRingedSliceRestrictionIso (U.obj V)
        (representableRingedSliceImageIso (J := J) (K := K) U V)).hom.app _)
  have hMu : IsIso (representableSliceModulePullbackMap U a V) := by
    have := SheafOfModules.sliceModulePullbackMap_isIso U a V
    exact representableSlice_moduleIsIso U a V
  refine ⟨hMC, hMD, hQ, hAlpha, ?_, hLambda, ?_, representableSlice_structural U a V,
    representableSlice_setPasting (J := J) (K := K) U V, ?_⟩
  · simpa only [representableSliceModuleRestrictionMate] using hMu
  · exact representableSlice_productNormalization U V sourceSlices targetSlices
  · intro M
    simp only [representableSliceModuleRestrictionMate]
    simpa only [representableSliceModuleChartPullbackMap, representableSliceModulePullbackMap,
      SheafOfModules.sliceModulePullbackMap, representableSliceGlobalModuleAdjunction,
      representableSliceLocalizedModuleAdjunction] using representableSlice_modulePasting U a V M

end CanonicalComparisons
end CategoryTheory
end
