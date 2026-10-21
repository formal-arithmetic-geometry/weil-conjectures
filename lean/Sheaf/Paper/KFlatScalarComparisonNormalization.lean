/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Mates
import all Sheaf.Paper.KFlatRingedToposPullback
import all Sheaf.CategoryTheory.FlatRestrictionOrdinaryComparisons

/-! # Normalization of scalar pullback on K-flat representatives

Source: blueprint main-20261015, det-prop-scalar-six-pullback (1); Stacks Project,
Tags 03EL, 0G7E, 06YY, 07A6 and 0D6D
(blueprint: lem-sfb-kflat-scalar-comparison-normalization).

## Main statements

- `kflat_scalar_comparison_normalization`: balanced comparison and specified derived mate.
- `θ_composition`, `θ_identity`: geometric composition and identity normalization.

The ordinary comparison is specified on generalized pure tensors, including its
scalar-extension units. The derived comparison is the inverse mate of the action
identification, rather than an unspecified isomorphism of functors. Its representative
formula uses the counits of the existing universal derived-change-of-rings models.
-/

@[expose] public section
set_option autoImplicit false
universe u w u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace SheafOfModules.ScalarPullback

/-- The module category already used by the scalar-change model.
Source: Stacks 03D2 (blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
abbrev Modules {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (A : Sheaf J CommRingCat.{u}) :=
  ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A)

/-- Forget a module to its underlying sheaf of sets.
Source: Stacks 03D2 (blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
noncomputable abbrev underlying {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (A : Sheaf J CommRingCat.{u}) : Modules A ⥤ Sheaf J (Type u) :=
  toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u} ⋙ uliftFunctor.{u, u})

/-- Restriction of scalars along the given sheaf ring map.
Source: Stacks 03D2 (blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
noncomputable abbrev restriction {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    Modules B ⥤ Modules A :=
  restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)

section InverseImageAliases

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- The existing algebraic inverse-image presentation in the small-site universe.
Source: Stacks 03D2
(blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
abbrev InverseImage (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u}) :=
  AlgebraicInverseImageOfUniverses.{u, u, u, u, u, u} L A B

variable {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
  {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}

/-- The existing module projection, with its sheaf-composition instances elaborated once.
Source: Stacks 03D2
(blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
abbrev inverseModules (I : InverseImage L A B) : Modules A ⥤ Modules B := I.modules

/-- The existing ring identification of the algebraic inverse-image presentation.
Source: Stacks 03D2
(blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
abbrev inverseRing (I : InverseImage L A B) :
    L.obj ((sheafCompose J
      (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).obj A) ≅
      (sheafCompose K (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).obj B :=
  I.ringUnderlying

/-- The existing underlying-module identification of the inverse-image presentation.
Source: Stacks 03D2
(blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
abbrev inverseUnderlying (I : InverseImage L A B) :
    inverseModules I ⋙ underlying B ≅ underlying A ⋙ L :=
  I.moduleUnderlying

end InverseImageAliases

/-- The image of a balanced pure tensor in the model's ordinary scalar extension.
The equality transport only identifies the model's object with the existing sheafification.
Source: Stacks 03EL (blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
noncomputable def pure {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {A B : Sheaf J CommRingCat.{u}} {φ : A ⟶ B}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
    (m : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ) (M : Modules A) (U : Cᵒᵖ)
    (b : B.obj.obj U) (x : M.val.obj U) : (m.E.obj M).val.obj U :=
  (eqToHom (m.obj_eq M).symm).val.app U
    ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
      (b ⊗ₜ[A.obj.obj U, (φ.hom.app U).hom] x))

/-- The inverse scalar-adjunction mate of a restriction/action square.
Source: Stacks 07A7 (blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
def mate {AY : Type u₁} {BY : Type u₂} {AX : Type u₃} {BX : Type u₄}
    [Category.{v₁} AY] [Category.{v₂} BY] [Category.{v₃} AX] [Category.{v₄} BX]
    {TY : AY ⥤ BY} {rY : BY ⥤ AY} {TX : AX ⥤ BX} {rX : BX ⥤ AX}
    (dY : TY ⊣ rY) (dX : TX ⊣ rX) {IA : AY ⥤ AX} {IB : BY ⥤ BX}
    (a : rY ⋙ IA ⟶ IB ⋙ rX) : IA ⋙ TX ⟶ TY ⋙ IB :=
  ((mateEquiv dY dX).symm (TwoSquare.mk _ _ _ _ a)).natTrans

/-- The normalized coefficient adjunction, expressed with the model's cochain counit.
This is the unit clause of the existing derived coefficient adjunction, transported
from homotopy localization to cochain localization by quotientCompQhIso.
Source: Stacks 07A6 (blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
def AdjunctionNormalized {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {A B : Sheaf J CommRingCat.{u}} {φ : A ⟶ B}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
    [PreservesFiniteLimits (restriction φ)] [PreservesFiniteColimits (restriction φ)]
    (m : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ)
    (a : m.E ⊣ restriction φ) (d : m.T ⊣ (restriction φ).mapDerivedCategory) : Prop :=
  (∀ (M : Modules A) (U : Cᵒᵖ) (x : M.val.obj U),
    (a.unit.app M).val.app U x = pure m M U 1 x) ∧
  ∀ (P : CochainComplex (Modules A) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients.{u, u, u} (J := J) (R := A) P →
    (∀ n : ℤ, IsFlatOnSite.{u, u, u, u} (J := J) (R := A) (P.X n)) →
    d.unit.app (DerivedCategory.Q.obj P) ≫
        (restriction φ).mapDerivedCategory.map (m.ε.app P) ≫
        (restriction φ).mapDerivedCategoryFactors.hom.app
          ((m.E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def unliftInverseImage
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (I : InverseImage L A B) : AlgebraicInverseImage L A B := by
  let eR := SheafOfModules.sheafUliftIso J CommRingCat.{u} (CategoryTheory.forget CommRingCat.{u})
  let eS := SheafOfModules.sheafUliftIso K CommRingCat.{u} (CategoryTheory.forget CommRingCat.{u})
  let eM := Functor.isoWhiskerLeft (toSheaf ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj A)) <|
    SheafOfModules.sheafUliftIso J AddCommGrpCat.{u} (CategoryTheory.forget AddCommGrpCat.{u})
  let eN := Functor.isoWhiskerLeft (toSheaf ((sheafCompose K
    (forget₂ CommRingCat.{u} RingCat.{u})).obj B)) <|
    SheafOfModules.sheafUliftIso K AddCommGrpCat.{u} (CategoryTheory.forget AddCommGrpCat.{u})
  let er := L.mapIso (eR.app A).symm ≪≫ I.ringUnderlying ≪≫ eS.app B
  let em := Functor.isoWhiskerLeft I.modules eN.symm ≪≫ I.moduleUnderlying ≪≫
    Functor.isoWhiskerRight eM L
  refine
    { ringUnderlying := er
      modules := I.modules
      moduleUnderlying := em
      ringAdd := ?_
      ringMul := ?_
      ringZero := ?_
      ringOne := ?_
      moduleAdd := ?_
      moduleZero := ?_
      moduleSMul := ?_ }
  · intro T a b t h V x
    have hr := I.ringAdd T (a ≫ (eR.app A).inv) (b ≫ (eR.app A).inv)
      (t ≫ (eR.app A).inv) h V x
    simpa [er, eR, eS, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a b t h V x
    have hr := I.ringMul T (a ≫ (eR.app A).inv) (b ≫ (eR.app A).inv)
      (t ≫ (eR.app A).inv) h V x
    simpa [er, eR, eS, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I.ringZero T (a ≫ (eR.app A).inv) h V x
    simpa [er, eR, eS, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro T a h V x
    have hr := I.ringOne T (a ≫ (eR.app A).inv) h V x
    simpa [er, eR, eS, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a b t h V x
    have hr := I.moduleAdd M T (a ≫ (eM.app M).inv) (b ≫ (eM.app M).inv)
      (t ≫ (eM.app M).inv) h V x
    simpa [em, eM, eN, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a h V x
    have hr := I.moduleZero M T (a ≫ (eM.app M).inv) h V x
    simpa [em, eM, eN, SheafOfModules.sheafUliftIso, uliftTrivial, Functor.map_comp] using hr
  · intro M T a b t h V x
    have hr := I.moduleSMul M T (a ≫ (eR.app A).inv) (b ≫ (eM.app M).inv)
      (t ≫ (eM.app M).inv) h V x
    simpa [er, em, eR, eS, eM, eN, SheafOfModules.sheafUliftIso, uliftTrivial,
      Functor.map_comp] using hr

section Action

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {AY BY : Sheaf J CommRingCat.{u}} {AX BX : Sheaf K CommRingCat.{u}}
  {φY : AY ⟶ BY} {φX : AX ⟶ BX}
  {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
  (IA : InverseImage L AY AX)
  (IB : InverseImage L BY BX)
  (ring_compat : L.map ((sheafCompose J
      (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φY) ≫
      (inverseRing IB).hom = (inverseRing IA).hom ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φX)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 800000 in
-- Compare the two scalar-restriction presentations and their underlying graph operations.
include ring_compat in
/-- The unique restriction/action identification fixed by the underlying inverse images.
Source: Stacks 03D2, blueprint det-prop-scalar-six-pullback (1)
(blueprint: lem-sfb-kflat-scalar-comparison-normalization).
Proof: transport addition and scalar multiplication using the generalized graph equations
of IA and IB. Ring compatibility makes the two restricted actions equal. Their underlying
sheaf isomorphism therefore lifts uniquely to a module isomorphism, naturally in H;
faithfulness of the underlying-sheaf functor gives uniqueness. -/
theorem action_existsUnique (leftExact : PreservesFiniteLimits L) :
    ∃! a : restriction φY ⋙ (inverseModules IA) ≅ (inverseModules IB) ⋙ restriction φX,
      ∀ (H : Modules BY) (U : Dᵒᵖ)
        (x : ((inverseModules IA).obj ((restriction φY).obj H)).val.obj U),
        (a.hom.app H).val.app U x =
          (((inverseUnderlying IB).inv.app H).hom.app U
            (((inverseUnderlying IA).hom.app ((restriction φY).obj H)).hom.app U
              (ULift.up x))).down := by
  classical
  let := leftExact
  let A := unliftInverseImage IA
  let B := unliftInverseImage IB
  let UY : Modules BY ⥤ Sheaf J (Type u) :=
    toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj BY) ⋙
      sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})
  let UX : Modules AX ⥤ Sheaf K (Type u) :=
    toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj AX) ⋙
      sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})
  let eJ := SheafOfModules.sheafUliftIso J CommRingCat.{u} (CategoryTheory.forget CommRingCat.{u})
  let eK := SheafOfModules.sheafUliftIso K CommRingCat.{u} (CategoryTheory.forget CommRingCat.{u})
  have hc : A.ringUnderlying.hom ≫
      (sheafCompose K (CategoryTheory.forget CommRingCat.{u})).map φX =
      L.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map φY) ≫
        eqToHom (congrArg (fun F ↦ F.obj
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj BY))
            (rfl : L = L)) ≫ B.ringUnderlying.hom := by
    have h := congrArg (fun q ↦ L.map (eJ.inv.app AY) ≫ q ≫ eK.hom.app BX)
      ring_compat
    change (L.map (eJ.inv.app AY) ≫ IA.ringUnderlying.hom ≫ eK.hom.app AX) ≫
      (sheafCompose K (CategoryTheory.forget CommRingCat.{u})).map φX =
        L.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map φY) ≫
          𝟙 _ ≫ (L.map (eJ.inv.app BY) ≫ IB.ringUnderlying.hom ≫ eK.hom.app BX)
    simp only [Category.id_comp, Category.assoc]
    rw [← eK.hom.naturality φX]
    rw [← L.map_comp_assoc, eJ.inv.naturality φY, L.map_comp_assoc]
    exact h.symm
  have hex (M : Modules BY) :=
    CategoryTheory.FlatRingedDiagramInput.inverse_change_hom A B φY φX rfl hc M
  let f (M : Modules BY) := (hex M).choose
  have hf (M : Modules BY) : UX.map (f M) =
      A.moduleUnderlying.hom.app ((restriction φY).obj M) ≫ B.moduleUnderlying.inv.app M := by
    exact (hex M).choose_spec
  have hi (M : Modules BY) : IsIso (f M) := by
    have : IsIso (UX.map (f M)) := by rw [hf]; infer_instance
    exact isIso_of_reflects_iso (f M) UX
  let β : restriction φY ⋙ inverseModules IA ⟶ inverseModules IB ⋙ restriction φX :=
    { app := f
      naturality := by
        intro M N g
        apply UX.map_injective
        change UX.map (A.modules.map ((restriction φY).map g) ≫ f N) =
          UX.map (f M ≫ (restriction φX).map (B.modules.map g))
        rw [Functor.map_comp, Functor.map_comp, hf, hf]
        have hA := A.moduleUnderlying.hom.naturality ((restriction φY).map g)
        have hB := B.moduleUnderlying.inv.naturality g
        change UX.map (A.modules.map ((restriction φY).map g)) ≫
          A.moduleUnderlying.hom.app ((restriction φY).obj N) =
            A.moduleUnderlying.hom.app ((restriction φY).obj M) ≫ L.map (UY.map g) at hA
        change L.map (UY.map g) ≫ B.moduleUnderlying.inv.app N =
          B.moduleUnderlying.inv.app M ≫
            UX.map ((restriction φX).map (B.modules.map g)) at hB
        rw [← Category.assoc, hA, Category.assoc, hB, Category.assoc] }
  let a : restriction φY ⋙ inverseModules IA ≅ inverseModules IB ⋙ restriction φX :=
    NatIso.ofComponents (fun M ↦ asIso (f M)) (fun g ↦ β.naturality g)
  have ha (M : Modules BY) (V : Dᵒᵖ)
      (x : ((inverseModules IA).obj ((restriction φY).obj M)).val.obj V) :
      (a.hom.app M).val.app V x =
        (((inverseUnderlying IB).inv.app M).hom.app V
          (((inverseUnderlying IA).hom.app ((restriction φY).obj M)).hom.app V
            (ULift.up x))).down := by
    have hraw := hf M
    dsimp only [A, B, unliftInverseImage, Iso.trans_hom, Iso.trans_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app] at hraw
    let e := SheafOfModules.sheafUliftIso J AddCommGrpCat.{u}
      (CategoryTheory.forget AddCommGrpCat.{u})
    let N := (toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj BY)).obj M
    simp only [Category.assoc] at hraw
    change UX.map (f M) = _ ≫ IA.moduleUnderlying.hom.app ((restriction φY).obj M) ≫
      L.map (e.hom.app N) ≫ L.map (e.inv.app N) ≫ IB.moduleUnderlying.inv.app M ≫ _ at hraw
    rw [← L.map_comp_assoc, Iso.hom_inv_id_app] at hraw
    erw [L.map_id, Category.id_comp] at hraw
    have h := congrArg (fun q ↦ q.hom.app V x) hraw
    dsimp [a, UX, B, unliftInverseImage, toSheaf, PresheafOfModules.toPresheaf,
      inverseModules, inverseUnderlying, sheafCompose,
      SheafOfModules.sheafUliftIso, uliftTrivial] at h ⊢
    exact h
  refine ⟨a, ha, ?_⟩
  intro a' ha'
  apply Iso.ext
  ext M V x
  exact (ha' M V x).trans (ha M V x).symm

/-- The canonical ordinary action identification, chosen from its unique underlying map.
Source: Stacks 03D2, blueprint det-prop-scalar-six-pullback (1)
(blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
@[irreducible]
noncomputable def a_h (leftExact : PreservesFiniteLimits L) :
    restriction φY ⋙ (inverseModules IA) ≅ (inverseModules IB) ⋙ restriction φX :=
  Classical.choose (action_existsUnique IA IB ring_compat leftExact).exists

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{w} (Modules AY)] [HasDerivedCategory.{w} (Modules BY)]
  [HasDerivedCategory.{w} (Modules AX)] [HasDerivedCategory.{w} (Modules BX)]
  [(inverseModules IA).Additive] [(inverseModules IB).Additive]
  [PreservesFiniteLimits (inverseModules IA)] [PreservesFiniteColimits (inverseModules IA)]
  [PreservesFiniteLimits (inverseModules IB)] [PreservesFiniteColimits (inverseModules IB)]
  [PreservesFiniteLimits (restriction φY)] [PreservesFiniteColimits (restriction φY)]
  [PreservesFiniteLimits (restriction φX)] [PreservesFiniteColimits (restriction φX)]

/-- Exact localization of the canonical ordinary action identification.
Source: Stacks 06YY, blueprint det-prop-scalar-six-pullback (1)
(blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
@[irreducible]
noncomputable def aD_h (leftExact : PreservesFiniteLimits L) :
    (restriction φY).mapDerivedCategory ⋙ (inverseModules IA).mapDerivedCategory ≅
      (inverseModules IB).mapDerivedCategory ⋙ (restriction φX).mapDerivedCategory := by
  letI := comp_preservesFiniteLimits (restriction φY) (inverseModules IA)
  letI := comp_preservesFiniteColimits (restriction φY) (inverseModules IA)
  letI := comp_preservesFiniteLimits (inverseModules IB) (restriction φX)
  letI := comp_preservesFiniteColimits (inverseModules IB) (restriction φX)
  exact (Functor.mapDerivedCategoryCompIso (restriction φY) (inverseModules IA)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (a_h IA IB ring_compat leftExact) ≪≫
      Functor.mapDerivedCategoryCompIso (inverseModules IB) (restriction φX)

/-- The specified geometric scalar comparison, as the inverse mate of the canonical action.
Source: blueprint det-prop-scalar-six-pullback (1), Stacks 07A7
(blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
@[irreducible]
noncomputable def θ_h (leftExact : PreservesFiniteLimits L)
    {TY : DerivedCategory (Modules AY) ⥤ DerivedCategory (Modules BY)}
    {TX : DerivedCategory (Modules AX) ⥤ DerivedCategory (Modules BX)}
    (dY : TY ⊣ (restriction φY).mapDerivedCategory)
    (dX : TX ⊣ (restriction φX).mapDerivedCategory) :
    (inverseModules IA).mapDerivedCategory ⋙ TX ⟶ TY ⋙ (inverseModules IB).mapDerivedCategory :=
  mate dY dX (aD_h IA IB ring_compat leftExact).hom

end Action

/-- The balanced comparison, its ordinary unit normalization, and its equality with the
specified scalar-adjunction mate on every flat-term K-flat representative. The last
isomorphism assertion concerns the entire unbounded derived category.

The two algebraic inverse images use the same geometric inverse image. The ring equation
says exactly that φX is the inverse image of φY under the displayed ring identifications.
The action isomorphism is fixed on underlying sheaves by moduleUnderlying. The derived
action is fixed by exact localization, not chosen freely. The pure-tensor equation is the
balanced-coequalizer characterization, tested on all generalized pairings before and
after inverse image; it is not a sectionwise-evaluation assumption about inverse image.
All exactness structures below are conclusions, not flatness assumptions on φY or φX.

Source: blueprint main-20261015 det-prop-scalar-six-pullback (1); Stacks 03EL, 04JC,
0G7E, 06YY, 07A6 and 06YS
(blueprint: lem-sfb-kflat-scalar-comparison-normalization).

Proof:
1. Geometric inverse image is additive and exact with transported actions
(lem-trf-geometric-inverse-image-exact). Exact localization gives its representative
comparisons (lem-weil-pbc-exact-functor-derived-factorization). Restricting the transported
action is the same as transporting the restricted action, giving a and then aD.
2. Apply the algebraic inverse-image tensor comparison (03EL) to the new ring as a module
and P in each degree. Inverse image preserves the two balancing arrows and their
coequalizer. The generalized pure-tensor formula gives B-linearity and the displayed
comparison χ, naturally in P. At coefficient 1 it gives the ordinary unit equation.
This uses lem-weil-pbc-geometric-module-construction and
lem-weil-pbc-algebraic-inverse-image-tensor-comparison.
3. Inverse image preserves flat-term K-flat complexes
(lem-weil-pbc-ringed-pullback-preserves-kflat). Thus both universal change-of-rings
counits are invertible on these representatives (lem-pur-derived-change-of-rings).
4. The normalized coefficient adjunction (lem-pur-sheaf-ring-derived-coefficient-adjunction)
identifies the derived units with the ordinary units on the representatives. The ordinary
unit equation says that Q(χ inverse), under the counits and exact localization comparisons,
has transpose aD after the Y-unit. Injectivity of the adjunction Hom bijection identifies
it with mate dY dX aD.hom. This is precisely the displayed representative equality.
5. Resolve any unbounded object by a flat-term K-flat complex (lem-pc-kflat-resolution).
The representative equality makes the mate invertible there. Naturality along the
localized resolution, which is an isomorphism, proves invertibility at every object.
6. The companion geometric composition and identity statements use the underlying-sheaf
identifications and exact localization. The transported action squares paste, and
lem-weil-pbc-mate-pasting gives their specified mates. No flatness or boundedness is used. -/
theorem kflat_scalar_comparison_normalization
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {AY BY : Sheaf J CommRingCat.{u}} {AX BX : Sheaf K CommRingCat.{u}}
    (φY : AY ⟶ BY) (φX : AX ⟶ BX)
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (R : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ R) [PreservesFiniteLimits L]
    (IA : InverseImage L AY AX)
    (IB : InverseImage L BY BX)
    (ring_compat : L.map ((sheafCompose J
        (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φY) ≫
        (inverseRing IB).hom = (inverseRing IA).hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φX)
    [HasDerivedCategory.{w} (Modules AY)] [HasDerivedCategory.{w} (Modules BY)]
    [HasDerivedCategory.{w} (Modules AX)] [HasDerivedCategory.{w} (Modules BX)]
    (mY : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φY)
    (mX : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φX) :
    ∃ (_ : (inverseModules IA).Additive) (_ : (inverseModules IB).Additive)
      (_ : PreservesFiniteLimits (inverseModules IA))
      (_ : PreservesFiniteColimits (inverseModules IA))
      (_ : PreservesFiniteLimits (inverseModules IB))
      (_ : PreservesFiniteColimits (inverseModules IB))
      (_ : PreservesFiniteLimits (restriction φY))
      (_ : PreservesFiniteColimits (restriction φY))
      (_ : PreservesFiniteLimits (restriction φX))
      (_ : PreservesFiniteColimits (restriction φX)),
    ∃ (aY : mY.E ⊣ restriction φY) (aX : mX.E ⊣ restriction φX)
      (dY : mY.T ⊣ (restriction φY).mapDerivedCategory)
      (dX : mX.T ⊣ (restriction φX).mapDerivedCategory)
      (χ : mY.E ⋙ (inverseModules IB) ≅ (inverseModules IA) ⋙ mX.E),
    AdjunctionNormalized mY aY dY ∧ AdjunctionNormalized mX aX dX ∧
    (∀ (H : Modules BY) (U : Dᵒᵖ)
      (x : ((inverseModules IA).obj ((restriction φY).obj H)).val.obj U),
      ((a_h IA IB ring_compat inferInstance).hom.app H).val.app U x =
        (((inverseUnderlying IB).inv.app H).hom.app U
          (((inverseUnderlying IA).hom.app ((restriction φY).obj H)).hom.app U
            (ULift.up x))).down) ∧
    (∀ (H : CochainComplex (Modules BY) ℤ),
      (aD_h IA IB ring_compat inferInstance).hom.app (DerivedCategory.Q.obj H) =
        (inverseModules IA).mapDerivedCategory.map
          ((restriction φY).mapDerivedCategoryFactors.hom.app H) ≫
          (inverseModules IA).mapDerivedCategoryFactors.hom.app
            (((restriction φY).mapHomologicalComplex (.up ℤ)).obj H) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (a_h IA IB ring_compat inferInstance) (.up ℤ)).hom.app H) ≫
          (restriction φX).mapDerivedCategoryFactors.inv.app
            (((inverseModules IB).mapHomologicalComplex (.up ℤ)).obj H) ≫
          (restriction φX).mapDerivedCategory.map
            ((inverseModules IB).mapDerivedCategoryFactors.inv.app H)) ∧
    (∀ (M : Modules AY) (Z : Sheaf J (Type u))
      (b : Z ⟶ (sheafCompose J
        (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).obj BY)
      (x : Z ⟶ (underlying AY).obj M)
      (z : Z ⟶ (underlying BY).obj (mY.E.obj M)),
      (∀ (U : Cᵒᵖ) (t : Z.obj.obj U),
        @id ((mY.E.obj M).val.obj U) (z.hom.app U t).down =
          pure mY M U (@id (BY.obj.obj U) (b.hom.app U t).down)
            (@id (M.val.obj U) (x.hom.app U t).down)) →
      ∀ (U : Dᵒᵖ) (t : (L.obj Z).obj.obj U),
        (χ.hom.app M).val.app U
          (((inverseUnderlying IB).inv.app (mY.E.obj M)).hom.app U ((L.map z).hom.app U t)).down =
        pure mX ((inverseModules IA).obj M) U
          (@id (BX.obj.obj U) ((L.map b ≫ (inverseRing IB).hom).hom.app U t).down)
          (((inverseUnderlying IA).inv.app M).hom.app U ((L.map x).hom.app U t)).down) ∧
    (∀ M : Modules AY,
      (inverseModules IA).map (aY.unit.app M) ≫
        (a_h IA IB ring_compat inferInstance).hom.app (mY.E.obj M) ≫
          (restriction φX).map (χ.hom.app M) = aX.unit.app ((inverseModules IA).obj M)) ∧
    (∀ (P : CochainComplex (Modules AY) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients.{u, u, u} (J := J) (R := AY) P →
      (∀ n : ℤ, IsFlatOnSite.{u, u, u, u} (J := J) (R := AY) (P.X n)) →
      IsIso (mX.ε.app (((inverseModules IA).mapHomologicalComplex (.up ℤ)).obj P)) ∧
      (θ_h IA IB ring_compat inferInstance dY dX).app (DerivedCategory.Q.obj P) ≫
          (inverseModules IB).mapDerivedCategory.map (mY.ε.app P) ≫
          (inverseModules IB).mapDerivedCategoryFactors.hom.app
            ((mY.E.mapHomologicalComplex (.up ℤ)).obj P) =
        mX.T.map ((inverseModules IA).mapDerivedCategoryFactors.hom.app P) ≫
          mX.ε.app (((inverseModules IA).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex χ (.up ℤ)).inv.app P)) ∧
    IsIso (θ_h IA IB ring_compat inferInstance dY dX) := by
  sorry

/-- Exact localization of a module composition identification.
This is the standard exact-functor comparison, with composite exactness derived internally.
Source: Stacks 06YY and 0D6D
(blueprint: lem-sfb-kflat-scalar-comparison-normalization). -/
@[irreducible]
noncomputable def compositionDerived
    {A B C : Type u₁} [Category.{v₁} A] [Category.{v₁} B] [Category.{v₁} C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (c : F ⋙ G ≅ H) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory := by
  letI := comp_preservesFiniteLimits F G
  letI := comp_preservesFiniteColimits F G
  exact (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
    Functor.mapDerivedCategoryNatIso c

section Composition

variable {CZ CY CX : Type u}
  [Category.{u} CZ] [Category.{u} CY] [Category.{u} CX]
  {JZ : GrothendieckTopology CZ} {JY : GrothendieckTopology CY}
  {JX : GrothendieckTopology CX}
  [HasSheafify JZ AddCommGrpCat.{u}] [JZ.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify JY AddCommGrpCat.{u}] [JY.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify JX AddCommGrpCat.{u}] [JX.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {AZ BZ : Sheaf JZ CommRingCat.{u}} {AY BY : Sheaf JY CommRingCat.{u}}
  {AX BX : Sheaf JX CommRingCat.{u}}
  {φZ : AZ ⟶ BZ} {φY : AY ⟶ BY} {φX : AX ⟶ BX}
  (Lg : Sheaf JZ (Type u) ⥤ Sheaf JY (Type u))
  (Rg : Sheaf JY (Type u) ⥤ Sheaf JZ (Type u)) (adjg : Lg ⊣ Rg)
  (Lf : Sheaf JY (Type u) ⥤ Sheaf JX (Type u))
  (Rf : Sheaf JX (Type u) ⥤ Sheaf JY (Type u)) (adjf : Lf ⊣ Rf)
  (Lh : Sheaf JZ (Type u) ⥤ Sheaf JX (Type u))
  (adjh : Lh ⊣ Rf ⋙ Rg)
  [PreservesFiniteLimits Lg] [PreservesFiniteLimits Lf] [PreservesFiniteLimits Lh]
  (IgA : InverseImage Lg AZ AY)
  (IgB : InverseImage Lg BZ BY)
  (IfA : InverseImage Lf AY AX)
  (IfB : InverseImage Lf BY BX)
  (IhA : InverseImage Lh AZ AX)
  (IhB : InverseImage Lh BZ BX)
  (hg : Lg.map ((sheafCompose JZ
      (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φZ) ≫
      (inverseRing IgB).hom = (inverseRing IgA).hom ≫
        (sheafCompose JY (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φY)
  (hf : Lf.map ((sheafCompose JY
      (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φY) ≫
      (inverseRing IfB).hom = (inverseRing IfA).hom ≫
        (sheafCompose JX (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φX)
  (hh : Lh.map ((sheafCompose JZ
      (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φZ) ≫
      (inverseRing IhB).hom = (inverseRing IhA).hom ≫
        (sheafCompose JX (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φX)
  [HasDerivedCategory.{w} (Modules AZ)] [HasDerivedCategory.{w} (Modules BZ)]
  [HasDerivedCategory.{w} (Modules AY)] [HasDerivedCategory.{w} (Modules BY)]
  [HasDerivedCategory.{w} (Modules AX)] [HasDerivedCategory.{w} (Modules BX)]
  [(inverseModules IgA).Additive]
  [PreservesFiniteLimits (inverseModules IgA)] [PreservesFiniteColimits (inverseModules IgA)]
  [(inverseModules IgB).Additive]
  [PreservesFiniteLimits (inverseModules IgB)] [PreservesFiniteColimits (inverseModules IgB)]
  [(inverseModules IfA).Additive]
  [PreservesFiniteLimits (inverseModules IfA)] [PreservesFiniteColimits (inverseModules IfA)]
  [(inverseModules IfB).Additive]
  [PreservesFiniteLimits (inverseModules IfB)] [PreservesFiniteColimits (inverseModules IfB)]
  [(inverseModules IhA).Additive]
  [PreservesFiniteLimits (inverseModules IhA)] [PreservesFiniteColimits (inverseModules IhA)]
  [(inverseModules IhB).Additive]
  [PreservesFiniteLimits (inverseModules IhB)] [PreservesFiniteColimits (inverseModules IhB)]
  [PreservesFiniteLimits (restriction φZ)] [PreservesFiniteColimits (restriction φZ)]
  [PreservesFiniteLimits (restriction φY)] [PreservesFiniteColimits (restriction φY)]
  [PreservesFiniteLimits (restriction φX)] [PreservesFiniteColimits (restriction φX)]

/-- Geometric composition of the specified scalar comparisons.
The composite topos morphism has right adjoint Rf ⋙ Rg. Its chosen inverse image
Lh is canonically identified with Lg ⋙ Lf by leftAdjointUniq for adjg.comp adjf
and adjh. Arbitrary algebraic presentations of that inverse image are compared
by cA and cB, using this specified underlying-sheaf composition identification.
Their equations fix the canonical module composition isomorphisms on underlying sheaves.
The displayed ring equations
fix the ring composition maps. The derived maps are the existing exact localization
of these same module identifications, not freely supplied comparison maps.
Source: blueprint det-prop-scalar-six-pullback (1), Stacks 0D6D
(blueprint: lem-sfb-kflat-scalar-comparison-normalization).
Proof: the underlying equations uniquely determine cA and cB, because both sides are
inverse images of the same sheaf with the same transported operations. The ring
composition equations show that the canonical action a_h is the paste of a_g and a_f
under cA and cB. Exact localization preserves that paste. Apply clause (1) of
lem-weil-pbc-mate-pasting to the shared scalar adjunctions to get the stated equation.
No flatness of a ring map or boundedness of a complex is used. -/
theorem θ_composition
    (ringA : ((adjg.comp adjf).leftAdjointUniq adjh).hom.app
        ((sheafCompose JZ
          (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).obj AZ) ≫
        (inverseRing IhA).hom = Lf.map (inverseRing IgA).hom ≫ (inverseRing IfA).hom)
    (ringB : ((adjg.comp adjf).leftAdjointUniq adjh).hom.app
        ((sheafCompose JZ
          (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).obj BZ) ≫
        (inverseRing IhB).hom = Lf.map (inverseRing IgB).hom ≫ (inverseRing IfB).hom)
    (mZ : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φZ)
    (mY : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φY)
    (mX : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φX)
    (dZ : mZ.T ⊣ (restriction φZ).mapDerivedCategory)
    (dY : mY.T ⊣ (restriction φY).mapDerivedCategory)
    (dX : mX.T ⊣ (restriction φX).mapDerivedCategory) :
    ∃ (cA : (inverseModules IgA) ⋙ (inverseModules IfA) ≅ (inverseModules IhA))
      (cB : (inverseModules IgB) ⋙ (inverseModules IfB) ≅ (inverseModules IhB)),
    (∀ (M : Modules AZ) (U : CXᵒᵖ)
      (x : ((inverseModules IfA).obj ((inverseModules IgA).obj M)).val.obj U),
      (cA.hom.app M).val.app U x =
        (((inverseUnderlying IhA).inv.app M).hom.app U
          ((((adjg.comp adjf).leftAdjointUniq adjh).hom.app ((underlying AZ).obj M)).hom.app U
            ((Lf.map ((inverseUnderlying IgA).hom.app M)).hom.app U
              (((inverseUnderlying IfA).hom.app ((inverseModules IgA).obj M)).hom.app U
                (ULift.up x))))).down) ∧
    (∀ (M : Modules BZ) (U : CXᵒᵖ)
      (x : ((inverseModules IfB).obj ((inverseModules IgB).obj M)).val.obj U),
      (cB.hom.app M).val.app U x =
        (((inverseUnderlying IhB).inv.app M).hom.app U
          ((((adjg.comp adjf).leftAdjointUniq adjh).hom.app ((underlying BZ).obj M)).hom.app U
            ((Lf.map ((inverseUnderlying IgB).hom.app M)).hom.app U
              (((inverseUnderlying IfB).hom.app ((inverseModules IgB).obj M)).hom.app U
                (ULift.up x))))).down) ∧
    Functor.whiskerRight
        (compositionDerived (inverseModules IgA) (inverseModules IfA)
          (inverseModules IhA) cA).hom mX.T ≫
      θ_h IhA IhB hh inferInstance dZ dX ≫
      Functor.whiskerLeft mZ.T
        (compositionDerived (inverseModules IgB) (inverseModules IfB) (inverseModules IhB) cB).inv =
      (Functor.associator (inverseModules IgA).mapDerivedCategory
        (inverseModules IfA).mapDerivedCategory mX.T).hom ≫
      Functor.whiskerLeft (inverseModules IgA).mapDerivedCategory
        (θ_h IfA IfB hf inferInstance dY dX) ≫
      (Functor.associator (inverseModules IgA).mapDerivedCategory mY.T
        (inverseModules IfB).mapDerivedCategory).inv ≫
      Functor.whiskerRight (θ_h IgA IgB hg inferInstance dZ dY)
        (inverseModules IfB).mapDerivedCategory ≫
      (Functor.associator mZ.T (inverseModules IgB).mapDerivedCategory
        (inverseModules IfB).mapDerivedCategory).hom := by
  sorry

end Composition

section Identity

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {A B : Sheaf J CommRingCat.{u}} {φ : A ⟶ B}
  (IA : InverseImage (𝟭 (Sheaf J (Type u))) A A)
  (IB : InverseImage (𝟭 (Sheaf J (Type u))) B B)
  (h : (𝟭 (Sheaf J (Type u))).map ((sheafCompose J
      (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φ) ≫
      (inverseRing IB).hom = (inverseRing IA).hom ≫
        (sheafCompose J (CategoryTheory.forget CommRingCat.{u} ⋙ uliftFunctor.{u, u})).map φ)
  [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
  [(inverseModules IA).Additive] [(inverseModules IB).Additive]
  [PreservesFiniteLimits (inverseModules IA)] [PreservesFiniteColimits (inverseModules IA)]
  [PreservesFiniteLimits (inverseModules IB)] [PreservesFiniteColimits (inverseModules IB)]
  [PreservesFiniteLimits (restriction φ)] [PreservesFiniteColimits (restriction φ)]

/-- Identity normalization with canonical underlying ring and module identifications.
The geometric inverse image is the identity functor of the sheaf topos, with its
identity adjunction. The module identifications iA and iB are fixed on underlying
sheaves; their displayed exact localizations identify θ_h with the identity of T.
Source: blueprint det-prop-scalar-six-pullback (1), Stacks 0D6D
(blueprint: lem-sfb-kflat-scalar-comparison-normalization).
Proof: the identity underlying maps lift uniquely to iA and iB under the ring equations.
The action a_h becomes the identity of scalar restriction under these identifications.
Localizing preserves this equation, and clause (4) of lem-weil-pbc-mate-pasting identifies
its inverse mate with the identity of scalar extension. The unitors give exactly the
stated equation. -/
theorem θ_identity
    (ringA : (inverseRing IA).hom = 𝟙 _)
    (ringB : (inverseRing IB).hom = 𝟙 _)
    (m : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} φ)
    (d : m.T ⊣ (restriction φ).mapDerivedCategory) :
    ∃ (iA : (inverseModules IA) ≅ 𝟭 (Modules A)) (iB : (inverseModules IB) ≅ 𝟭 (Modules B)),
    (∀ (M : Modules A) (U : Cᵒᵖ) (x : ((inverseModules IA).obj M).val.obj U),
      (iA.hom.app M).val.app U x =
        (((inverseUnderlying IA).hom.app M).hom.app U (ULift.up x)).down) ∧
    (∀ (M : Modules B) (U : Cᵒᵖ) (x : ((inverseModules IB).obj M).val.obj U),
      (iB.hom.app M).val.app U x =
        (((inverseUnderlying IB).hom.app M).hom.app U (ULift.up x)).down) ∧
    Functor.whiskerRight
        (Functor.mapDerivedCategoryNatIso iA ≪≫
          Functor.mapDerivedCategoryIdIso (Modules A)).inv m.T ≫
      θ_h IA IB h inferInstance d d ≫
      Functor.whiskerLeft m.T
        (Functor.mapDerivedCategoryNatIso iB ≪≫
          Functor.mapDerivedCategoryIdIso (Modules B)).hom =
      (Functor.leftUnitor m.T).hom ≫ (Functor.rightUnitor m.T).inv := by
  sorry

end Identity

end SheafOfModules.ScalarPullback
