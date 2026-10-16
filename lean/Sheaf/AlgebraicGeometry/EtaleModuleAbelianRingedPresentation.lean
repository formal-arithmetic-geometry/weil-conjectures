/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import Sheaf.CategoryTheory.RingedToposMorphism

import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Sites.Equivalence
import Sheaf.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import all Sheaf.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.BaseChange.DerivedForget
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Ringed presentations of coefficient forgetting and étale direct image

Source: Stacks Project, Tags 093I, 0D6J, and 0D6E.
(blueprint: lem-kun-etale-module-abelian-ringed-presentation)
-/

@[expose] public section

universe u

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : D ⥤ C) [F.IsContinuous K J]
  (L : Sheaf K (Type u) ⥤ Sheaf J (Type u))
  (adj : L ⊣ F.sheafPushforwardContinuous (Type u) K J)

private def directPair {X Y : Sheaf J (Type u)} {T : Sheaf K (Type u)}
    (x : T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj X)
    (y : T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj Y) :
    T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj (X ⊗ Y) :=
  ⟨{ app U := ↾(fun t ↦ (x.hom.app U t, y.hom.app U t))
     naturality := by
       intro U V f
       ext t
       change (x.hom.app V (T.obj.map f t), y.hom.app V (T.obj.map f t)) =
         (X.obj.map (F.op.map f) (x.hom.app U t),
           Y.obj.map (F.op.map f) (y.hom.app U t))
       exact Prod.ext (CategoryTheory.congr_fun (x.hom.naturality f) t)
         (CategoryTheory.congr_fun (y.hom.naturality f) t) }⟩

private theorem transpose_pair {X Y : Sheaf J (Type u)} {T : Sheaf K (Type u)}
    (x : T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj X)
    (y : T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj Y) :
    (adj.homEquiv T (X ⊗ Y)).symm (directPair F x y) =
      CartesianMonoidalCategory.lift ((adj.homEquiv T X).symm x)
        ((adj.homEquiv T Y).symm y) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [CartesianMonoidalCategory.lift_fst, ← adj.homEquiv_naturality_right_symm]
    rfl
  · rw [CartesianMonoidalCategory.lift_snd, ← adj.homEquiv_naturality_right_symm]
    rfl

private theorem transpose_binary
    {X Y Z : Sheaf J (Type u)} {T : Sheaf K (Type u)} (op : X ⊗ Y ⟶ Z)
    (x : T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj X)
    (y : T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj Y)
    (z : T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj Z)
    (hz : ∀ U t, z.hom.app U t = op.hom.app (F.op.obj U)
      (x.hom.app U t, y.hom.app U t)) :
    ∀ U t, ((adj.homEquiv T Z).symm z).hom.app U t =
      op.hom.app U (((adj.homEquiv T X).symm x).hom.app U t,
        ((adj.homEquiv T Y).symm y).hom.app U t) := by
  have he : z = directPair F x y ≫
      (F.sheafPushforwardContinuous (Type u) K J).map op := by
    ext U t
    exact hz U t
  rw [he, adj.homEquiv_naturality_right_symm, transpose_pair F L adj]
  intro U t
  rfl

private theorem transpose_constant
    {X : Sheaf J (Type u)} {T : Sheaf K (Type u)}
    (op : 𝟙_ (Sheaf J (Type u)) ⟶ X)
    (z : T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj X)
    (hz : ∀ U t, z.hom.app U t = op.hom.app (F.op.obj U) PUnit.unit) :
    ∀ U t, ((adj.homEquiv T X).symm z).hom.app U t = op.hom.app U PUnit.unit := by
  let w : T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj (𝟙_ _) :=
    ⟨{ app U := ↾(fun _ ↦ PUnit.unit) }⟩
  have he : z = w ≫ (F.sheafPushforwardContinuous (Type u) K J).map op := by
    ext U t
    exact hz U t
  rw [he, adj.homEquiv_naturality_right_symm]
  intro U t
  change op.hom.app U _ = _
  congr 1

open SheafOfModules.GeometricConstruction in
private noncomputable def continuousRingedTopos
    [PreservesFiniteLimits L]
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} K J).obj R) :
    RingedToposMorphism (base R) (base S) := by
  let φR : base S ⟶ (F.sheafPushforwardContinuous RingCat.{u} K J).obj (base R) :=
    (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).map φ
  let φs : rset S ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj (rset R) :=
    (sheafCompose K (forget CommRingCat.{u})).map φ
  let g := (adj.homEquiv (rset S) (rset R)).symm φs
  let P := SheafOfModules.pushforward.{u} (F := F) φR
  refine {
    inverse := L
    direct := F.sheafPushforwardContinuous (Type u) K J
    adj := adj
    leftExact := inferInstance
    ringMap := g
    ring_zero := ?_
    ring_one := ?_
    ring_add := ?_
    ring_mul := ?_
    modules := P
    additive := ?_
    underlying := Iso.refl _
    module_linear := ?_
  }
  · intro T z hz U t
    change T ⟶ rset S at z
    change ((L.map z) ≫ g).hom.app U t = (0 : R.obj.obj U)
    dsimp only [g]
    rw [← adj.homEquiv_naturality_left_symm]
    let zeroR : 𝟙_ (Sheaf J (Type u)) ⟶ rset R :=
      ⟨{ app U := ↾(fun _ ↦ (0 : R.obj.obj U))
         naturality := by intro U V f; ext t; exact (R.obj.map f).hom.map_zero.symm }⟩
    apply transpose_constant F L adj zeroR (z ≫ φs) _ U t
    intro V x
    change (φ.hom.app V).hom (z.hom.app V x) = 0
    have h : (show S.obj.obj V from z.hom.app V x) = 0 := hz V x
    exact (congrArg (φ.hom.app V).hom h).trans (φ.hom.app V).hom.map_zero
  · intro T z hz U t
    change T ⟶ rset S at z
    change ((L.map z) ≫ g).hom.app U t = (1 : R.obj.obj U)
    dsimp only [g]
    rw [← adj.homEquiv_naturality_left_symm]
    apply transpose_constant F L adj (ringOne R) (z ≫ φs) _ U t
    intro V x
    change (φ.hom.app V).hom (z.hom.app V x) = 1
    have h : (show S.obj.obj V from z.hom.app V x) = 1 := hz V x
    exact (congrArg (φ.hom.app V).hom h).trans (φ.hom.app V).hom.map_one
  · intro T x y z hz U t
    change T ⟶ rset S at x y z
    change ((L.map z) ≫ g).hom.app U t =
      @Add.add (R.obj.obj U) inferInstance
        (((L.map x) ≫ g).hom.app U t) (((L.map y) ≫ g).hom.app U t)
    dsimp only [g]
    rw [← adj.homEquiv_naturality_left_symm,
      ← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_left_symm]
    apply transpose_binary F L adj (ringAdd R) (x ≫ φs) (y ≫ φs) (z ≫ φs) _ U t
    intro V x'
    change (φ.hom.app V).hom (z.hom.app V x') =
      (φ.hom.app V).hom (x.hom.app V x') + (φ.hom.app V).hom (y.hom.app V x')
    have h : (show S.obj.obj V from z.hom.app V x') =
        (show S.obj.obj V from x.hom.app V x') + (show S.obj.obj V from y.hom.app V x') :=
      hz V x'
    exact (congrArg (φ.hom.app V).hom h).trans ((φ.hom.app V).hom.map_add _ _)
  · intro T x y z hz U t
    change T ⟶ rset S at x y z
    change ((L.map z) ≫ g).hom.app U t =
      @Mul.mul (R.obj.obj U) inferInstance
        (((L.map x) ≫ g).hom.app U t) (((L.map y) ≫ g).hom.app U t)
    dsimp only [g]
    rw [← adj.homEquiv_naturality_left_symm,
      ← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_left_symm]
    apply transpose_binary F L adj (ringMul R) (x ≫ φs) (y ≫ φs) (z ≫ φs) _ U t
    intro V x'
    change (φ.hom.app V).hom (z.hom.app V x') =
      (φ.hom.app V).hom (x.hom.app V x') * (φ.hom.app V).hom (y.hom.app V x')
    have h : (show S.obj.obj V from z.hom.app V x') =
        (show S.obj.obj V from x.hom.app V x') * (show S.obj.obj V from y.hom.app V x') :=
      hz V x'
    exact (congrArg (φ.hom.app V).hom h).trans ((φ.hom.app V).hom.map_mul _ _)
  · exact ⟨by intro M N a b; ext U x; rfl⟩
  · intro M T a x y z hz U t
    change T ⟶ rset S at a
    change T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj ((mset R).obj M)
      at x y z
    let ax : T ⟶ (F.sheafPushforwardContinuous (Type u) K J).obj ((mset R).obj M) :=
      CartesianMonoidalCategory.lift a x ≫ action S (P.obj M)
    have hAdd := transpose_binary F L adj (addition R M) ax y z
      (fun V x' ↦ hz V x') U t
    have hSmul := transpose_binary F L adj (action R M) (a ≫ φs) x ax
      (fun V x' ↦ rfl) U t
    change ((adj.homEquiv T _).symm z).hom.app U t = _
    rw [hAdd, hSmul]
    rw [adj.homEquiv_naturality_left_symm]
    rfl

end

private noncomputable def restrictionRingedTopos
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (c : S ⟶ R) : RingedToposMorphism R S where
  inverse := 𝟭 _
  direct := 𝟭 _
  adj := Adjunction.id
  leftExact := inferInstance
  ringMap := (sheafCompose J (forget RingCat.{u})).map c
  ring_zero := by
    intro T z hz U t
    change (c.hom.app U).hom (z.hom.app U t) = 0
    rw [hz U t]
    exact (c.hom.app U).hom.map_zero
  ring_one := by
    intro T z hz U t
    change (c.hom.app U).hom (z.hom.app U t) = 1
    rw [hz U t]
    exact (c.hom.app U).hom.map_one
  ring_add := by
    intro T x y z hz U t
    change (c.hom.app U).hom (z.hom.app U t) =
      (c.hom.app U).hom (x.hom.app U t) + (c.hom.app U).hom (y.hom.app U t)
    rw [hz U t]
    exact (c.hom.app U).hom.map_add _ _
  ring_mul := by
    intro T x y z hz U t
    change (c.hom.app U).hom (z.hom.app U t) =
      (c.hom.app U).hom (x.hom.app U t) * (c.hom.app U).hom (y.hom.app U t)
    rw [hz U t]
    exact (c.hom.app U).hom.map_mul _ _
  modules := SheafOfModules.restrictScalars c
  additive := inferInstance
  underlying := Iso.refl _
  module_linear := by
    intro M T a x y z hz U t
    exact hz U t
end CategoryTheory

namespace AlgebraicGeometry.Etale

open CategoryTheory.Functor

private noncomputable def smallEtaleModuleLift (X : Scheme.{u})
    (R : Sheaf X.smallEtaleTopology RingCat.{u + 1}) :
    let e := AsSmall.equiv.{u, u + 1, u + 1} (C := X.Etale)
    let T := e.inverse.inducedTopology X.smallEtaleTopology
    SheafOfModules.{u + 1} R ≌
      SheafOfModules.{u + 1}
        ((e.sheafCongr X.smallEtaleTopology T RingCat.{u + 1}).functor.obj R) := by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := X.Etale)
  let T := e.inverse.inducedTopology X.smallEtaleTopology
  let R' := (e.sheafCongr X.smallEtaleTopology T RingCat.{u + 1}).functor.obj R
  let φ : R' ⟶ (e.inverse.sheafPushforwardContinuous RingCat.{u + 1}
      T X.smallEtaleTopology).obj R := 𝟙 _
  let ψ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{u + 1}
      X.smallEtaleTopology T).obj R' := 𝟙 _
  have : e.symm.functor.IsContinuous T X.smallEtaleTopology := by
    change e.inverse.IsContinuous T X.smallEtaleTopology
    infer_instance
  have : e.symm.inverse.IsContinuous X.smallEtaleTopology T := by
    change e.functor.IsContinuous X.smallEtaleTopology T
    infer_instance
  exact SheafOfModules.pushforwardPushforwardEquivalence e.symm φ ψ
    (by
      ext U x
      change (R.obj.map (𝟙 _)).hom x = x
      rw [R.obj.map_id]
      rfl)
    (by
      ext U x
      change (R.obj.map (𝟙 _)).hom x = x
      rw [R.obj.map_id]
      rfl)


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem integerToSheafEquivalence (X : Scheme.{u}) :
    let e := AsSmall.equiv.{u, u + 1, u + 1} (C := X.Etale)
    let T := e.inverse.inducedTopology X.smallEtaleTopology
    let Z := (constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} ℤ))
    let Z' := (e.sheafCongr X.smallEtaleTopology T CommRingCat.{u + 1}).functor.obj Z
    (SheafOfModules.toSheaf.{u + 1}
      ((sheafCompose T (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj Z')).IsEquivalence := by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := X.Etale)
  let T := e.inverse.inducedTopology X.smallEtaleTopology
  let Z := (constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1} ℤ))
  let Zr := (sheafCompose X.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj Z
  let Z' := (e.sheafCongr X.smallEtaleTopology T CommRingCat.{u + 1}).functor.obj Z
  let Zr' := (sheafCompose T (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj Z'
  obtain ⟨E, ⟨ε⟩⟩ := moduleSheaf_constantRing_equivalence (ULift.{u + 1} ℤ) X
  have : (E.functor ⋙ SheafOfModules.toSheaf.{u + 1} Zr).IsEquivalence :=
    Functor.isEquivalence_of_iso ε.symm
  have : (SheafOfModules.toSheaf.{u + 1} Zr).IsEquivalence :=
    Functor.isEquivalence_of_comp_left E.functor _
  let E' := smallEtaleModuleLift X Zr
  let ea := e.sheafCongr X.smallEtaleTopology T AddCommGrpCat.{u + 1}
  let ε' : E'.functor ⋙ SheafOfModules.toSheaf.{u + 1} Zr' ≅
      SheafOfModules.toSheaf.{u + 1} Zr ⋙ ea.functor := Iso.refl _
  have : (E'.functor ⋙ SheafOfModules.toSheaf.{u + 1} Zr').IsEquivalence :=
    Functor.isEquivalence_of_iso ε'.symm
  exact Functor.isEquivalence_of_comp_left E'.functor _

/-- The two underived functors have simultaneous presentations by module direct images.

Source: Stacks Project, Tag 093I (constant rings and modules), and the coefficient
restriction and geometric morphisms in the proof of Tag 0D6J(3), using Tag 0D6E.
(blueprint: lem-kun-etale-module-abelian-ringed-presentation).

Proof: Replace the small étale categories of A and B by AsSmall, lifting homs to
Type (u+1), and use the topologies transported along the inverse equivalences.
Precomposition gives equivalences of sheaf categories. Transport the constant
Lambda and constant ULift integers ring sheaves. The constant-ring module equivalence
identifies Lambda-module-valued sheaves with modules over the first ring. For the
integers, first identify abelian groups with ULift-integer modules sectionwise,
then apply the constant-ring equivalence. Thus the forgetful functors from modules
over the constant integer sheaves to abelian sheaves are equivalences. Use their
inverses to define the two abelian encodings.
The identity geometric morphism with ring map Z to Lambda gives r: its module
direct image is restriction of scalars. The geometric morphism induced by v,
with the constant-integer structural map, gives p. The structural ring maps
respect zero, one, addition and multiplication, since inverse image preserves
finite limits and these operations are maps of sheaves. The module-linearity
condition follows in the same way from the addition and action graphs. Under
the equivalences, r.modules is coefficient forgetting and p.modules is abelian
direct image. After applying the fully faithful forgetful functor for the
integer ring, their sectionwise descriptions give the two natural isomorphisms;
fully faithfulness lifts these to module-valued functors. The site equivalence units and
counits give the conjugated set
adjunctions and preserve finite limits. No complexes or resolutions are used.
The zero ring, empty schemes and identity morphisms are included.
-/
theorem etaleModuleAbelianRingedPresentation
    (Λ : Type (u + 1)) [CommRing Λ] {A B : Scheme.{u}} (v : A ⟶ B) :
    ∃ (C D : Type (u + 1)) (_ : SmallCategory C) (_ : SmallCategory D)
      (T : GrothendieckTopology C) (S : GrothendieckTopology D)
      (R Z : Sheaf T CommRingCat.{u + 1}) (W : Sheaf S CommRingCat.{u + 1})
      (eM : Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ) ≌
        SheafOfModules.{u + 1}
          ((sheafCompose T (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
      (eA : Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1} ≌
        SheafOfModules.{u + 1}
          ((sheafCompose T (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj Z))
      (eB : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1} ≌
        SheafOfModules.{u + 1}
          ((sheafCompose S (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj W))
      (r : RingedToposMorphism
        ((sheafCompose T (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
        ((sheafCompose T (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj Z))
      (p : RingedToposMorphism
        ((sheafCompose T (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj Z)
        ((sheafCompose S (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj W)),
      Nonempty (eM.functor ⋙ r.modules ≅ moduleAbelianForget Λ A ⋙ eA.functor) ∧
      Nonempty (eA.functor ⋙ p.modules ≅ (v)_*[AddCommGrpCat.{u + 1}] ⋙ eB.functor) := by
  let ea := AsSmall.equiv.{u, u + 1, u + 1} (C := A.Etale)
  let eb := AsSmall.equiv.{u, u + 1, u + 1} (C := B.Etale)
  let T := ea.inverse.inducedTopology A.smallEtaleTopology
  let S := eb.inverse.inducedTopology B.smallEtaleTopology
  let b := MorphismProperty.Over.pullback @Etale ⊤ v
  let F := eb.inverse ⋙ b ⋙ ea.functor
  have : b.IsContinuous B.smallEtaleTopology A.smallEtaleTopology :=
    AlgebraicGeometry.Etale.isContinuous_overPullback v
  have : (b ⋙ ea.functor).IsContinuous B.smallEtaleTopology T :=
    Functor.isContinuous_comp b ea.functor B.smallEtaleTopology A.smallEtaleTopology T
  have : F.IsContinuous S T :=
    Functor.isContinuous_comp eb.inverse (b ⋙ ea.functor) S B.smallEtaleTopology T
  let Ea := ea.sheafCongr A.smallEtaleTopology T (Type (u + 1))
  let Eb := eb.sheafCongr B.smallEtaleTopology S (Type (u + 1))
  let L := Eb.inverse ⋙ Scheme.etaleSetPullback v ⋙ Ea.functor
  have : PreservesFiniteLimits (Scheme.etaleSetPullback v) := by
    unfold Scheme.etaleSetPullback Functor.sheafPullbackConstruction.sheafPullback
    let : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
      AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} (Type (u + 1))
    infer_instance
  have : PreservesFiniteLimits L := by dsimp [L]; infer_instance
  let adj0 := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
    (Type (u + 1)) B.smallEtaleTopology A.smallEtaleTopology
  let adj : L ⊣ F.sheafPushforwardContinuous (Type (u + 1)) S T :=
    ((Eb.symm.toAdjunction.comp adj0).comp Ea.toAdjunction).ofNatIsoRight (Iso.refl _)
  let Za := (constantSheaf A.smallEtaleTopology CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1} ℤ))
  let Zb := (constantSheaf B.smallEtaleTopology CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1} ℤ))
  let γ : Zb ⟶ (b.sheafPushforwardContinuous CommRingCat.{u + 1}
      B.smallEtaleTopology A.smallEtaleTopology).obj Za :=
    ((sheafificationAdjunction B.smallEtaleTopology CommRingCat.{u + 1}).homEquiv _ _).symm
      (Functor.whiskerLeft b.op (toSheafify A.smallEtaleTopology
        ((Functor.const A.Etaleᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} ℤ)))))
  let Z := (ea.sheafCongr A.smallEtaleTopology T CommRingCat.{u + 1}).functor.obj Za
  let W := (eb.sheafCongr B.smallEtaleTopology S CommRingCat.{u + 1}).functor.obj Zb
  let φ : W ⟶ (F.sheafPushforwardContinuous CommRingCat.{u + 1} S T).obj Z :=
    (eb.sheafCongr B.smallEtaleTopology S CommRingCat.{u + 1}).functor.map γ
  let p := CategoryTheory.continuousRingedTopos F L adj Z W φ
  let Ra := (constantSheaf A.smallEtaleTopology CommRingCat.{u + 1}).obj
    (CommRingCat.of Λ)
  let R := (ea.sheafCongr A.smallEtaleTopology T CommRingCat.{u + 1}).functor.obj Ra
  let c₀ : Za ⟶ Ra := (constantSheaf A.smallEtaleTopology CommRingCat.{u + 1}).map
    (CommRingCat.ofHom ((Int.castRingHom Λ).comp ULift.ringEquiv.toRingHom))
  let cr := (sheafCompose T (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    ((ea.sheafCongr A.smallEtaleTopology T CommRingCat.{u + 1}).functor.map c₀)
  let r := CategoryTheory.restrictionRingedTopos cr
  let Zr := (sheafCompose T (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj Z
  let Wr := (sheafCompose S (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj W
  let Rr := (sheafCompose T (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  have : (SheafOfModules.toSheaf.{u + 1} Zr).IsEquivalence := integerToSheafEquivalence A
  have : (SheafOfModules.toSheaf.{u + 1} Wr).IsEquivalence := integerToSheafEquivalence B
  let Eaa := ea.sheafCongr A.smallEtaleTopology T AddCommGrpCat.{u + 1}
  let Ebb := eb.sheafCongr B.smallEtaleTopology S AddCommGrpCat.{u + 1}
  let eA := Eaa.trans (SheafOfModules.toSheaf.{u + 1} Zr).asEquivalence.symm
  let eB := Ebb.trans (SheafOfModules.toSheaf.{u + 1} Wr).asEquivalence.symm
  obtain ⟨EM, ⟨εM⟩⟩ := moduleSheaf_constantRing_equivalence Λ A
  let eM := EM.trans (smallEtaleModuleLift A _)
  let εA : eA.functor ⋙ SheafOfModules.toSheaf.{u + 1} Zr ≅ Eaa.functor :=
    isoWhiskerLeft Eaa.functor (SheafOfModules.toSheaf.{u + 1} Zr).asEquivalence.counitIso
  let εB : eB.functor ⋙ SheafOfModules.toSheaf.{u + 1} Wr ≅ Ebb.functor :=
    isoWhiskerLeft Ebb.functor (SheafOfModules.toSheaf.{u + 1} Wr).asEquivalence.counitIso
  let εR : eM.functor ⋙ SheafOfModules.toSheaf.{u + 1} Rr ≅
      moduleAbelianForget Λ A ⋙ Eaa.functor := isoWhiskerRight εM Eaa.functor
  let α : eM.functor ⋙ r.modules ≅ moduleAbelianForget Λ A ⋙ eA.functor :=
    ((Functor.whiskeringRight _ _ _).obj (SheafOfModules.toSheaf.{u + 1} Zr)).preimageIso
      (εR ≪≫ isoWhiskerLeft (moduleAbelianForget Λ A) εA.symm)
  let Fab := F.sheafPushforwardContinuous AddCommGrpCat.{u + 1} S T
  let δ : Eaa.functor ⋙ Fab ≅ (v)_*[AddCommGrpCat.{u + 1}] ⋙ Ebb.functor := Iso.refl _
  let β : eA.functor ⋙ p.modules ≅ (v)_*[AddCommGrpCat.{u + 1}] ⋙ eB.functor :=
    ((Functor.whiskeringRight _ _ _).obj (SheafOfModules.toSheaf.{u + 1} Wr)).preimageIso
      (isoWhiskerRight εA Fab ≪≫ δ ≪≫
        isoWhiskerLeft ((v)_*[AddCommGrpCat.{u + 1}]) εB.symm)
  exact ⟨_, _, inferInstance, inferInstance, T, S, R, Z, W, eM, eA, eB, r, p,
    ⟨α⟩, ⟨β⟩⟩
end AlgebraicGeometry.Etale
