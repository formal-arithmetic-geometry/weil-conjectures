/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityTatePowers
public import WeilConjectures.WeilSheaf.TateTwistCohomology
public import WeilConjectures.WeilSheaf.FrobeniusTwist
public import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.CoefficientLinear

/-!
# The Tate encoding: the Weil Tate sheaves in the condensed model

The Weil Tate sheaf `ℚ̄_ℓ(d)` of the old model is the constant Weil twist of `ℚ̄_ℓ` by `χ_ℓ(σ)^d`
(`AlgebraicGeometry.WeilSheaf.tateTwistSheafNatObjIso`); in the condensed model, the Tate twist
`ℚ̄_ℓ,X(d)` (`AlgebraicGeometry.ProEtale.tateTwist`), pulled back to the geometric fibre, is
trivialized with the Weil law `q^d` (`AlgebraicGeometry.ProEtale.CondensedRing.purity_tateTwistNatTrivialization'_weil_lowerStar`).
Given the comparison of the constant Weil sheaf `ℚ̄_ℓ` with the pulled-back unit in the condensed
model (a parameter `ψ`), these combine to the comparison
`E(ℚ̄_ℓ(d)) ≅ p^* ℚ̄_ℓ,X(d)` of Weil objects in the condensed model
(`AlgebraicGeometry.ProEtaleWeilSheaf.purity_tateTwistSheafCondensedIso`): the twist by
`χ_ℓ(σ)^d = q^{-d}` on the one side matches the Weil law `q^d` of the trivialization on the
other. The scalars are compared after multiplication by the integer `q^d`, which is invertible
in the `ℚ̄_ℓ`-linear category of condensed `ℚ̄_ℓ,X̄`-modules.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace CategoryTheory

/-- If `s ≫ N • 𝟙 = 𝟙`, then `F s ≫ N • x = x` for an additive functor `F`. -/
lemma Functor.purity_map_comp_zsmul_eq_self_of_comp_zsmul_id {C : Type*} [Category C] [Preadditive C]
    {D : Type*} [Category D] [Preadditive D] (F : C ⥤ D) [F.Additive] {M : C} {Y : D}
    (s : M ⟶ M) (N : ℤ) (hs : s ≫ N • 𝟙 M = 𝟙 M) (x : F.obj M ⟶ Y) :
    F.map s ≫ N • x = x := by
  rw [← Category.id_comp x, ← Preadditive.zsmul_comp, ← F.map_id, ← F.map_zsmul,
    ← F.map_comp_assoc, hs]

end CategoryTheory

namespace AlgebraicGeometry

open ProEtale

/-! ### A compatible system of roots of unity in `k̄₀` -/

section Roots

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- A compatible system of primitive `lⁿ`-th roots of unity in the algebraic closure of `k₀`. -/
noncomputable def purity_tateRootsSystem : ℕ → AlgebraicClosure k₀ :=
  haveI := WeilSheaf.neZero_natCast_algebraicClosure k₀ l
  (IsSepClosed.exists_isPrimitiveRoot_pow_eq (AlgebraicClosure k₀) l).choose

lemma purity_tateRootsSystem_spec :
    (∀ n, IsPrimitiveRoot (purity_tateRootsSystem k₀ l n) (l ^ n)) ∧
      ∀ n, purity_tateRootsSystem k₀ l (n + 1) ^ l = purity_tateRootsSystem k₀ l n :=
  haveI := WeilSheaf.neZero_natCast_algebraicClosure k₀ l
  (IsSepClosed.exists_isPrimitiveRoot_pow_eq (AlgebraicClosure k₀) l).choose_spec

end Roots

/-! ### Scalars -/

section Scalar

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- `q ≠ 0` in `ℚ̄_ℓ`. -/
lemma purity_natCard_ne_zero_padicAlgCl : (Nat.card k₀ : PadicAlgCl l) ≠ 0 := by
  intro h
  have := (WeilSheaf.cyclotomicUnit k₀ l).ne_zero
  rw [WeilSheaf.cyclotomicUnit_eq, h, inv_zero] at this
  exact this rfl

/-- The scalar `χ_ℓ(σ)^d = q^{-d}` followed by the integer `q^d` is the identity. -/
lemma AdicSheaf.purity_smul_cyclotomicUnit_pow_comp_zsmul {Z : Scheme.{u}} (M : AdicSheaf l Z) (d : ℕ) :
    AdicSheaf.smul (ULift.up ((WeilSheaf.cyclotomicUnit k₀ l ^ d : (PadicAlgCl l)ˣ) :
        PadicAlgCl l)) M ≫ ((Nat.card k₀ : ℤ) ^ d) • 𝟙 M = 𝟙 M := by
  have hN : ((Nat.card k₀ : ℤ) ^ d) • 𝟙 M =
      AdicSheaf.smul (ULift.up ((Nat.card k₀ : PadicAlgCl l) ^ d)) M := by
    refine Mod.hom_ext _ _ ?_
    rw [Mod.zsmul_hom, Mod.id_hom', AdicSheaf.smul_hom,
      ← Int.cast_smul_eq_zsmul (R := ULift.{u + 1} (PadicAlgCl l)), ← ULift.up_intCast]
    congr 2
    simp
  rw [hN, AdicSheaf.smul_smul, ← AdicSheaf.smul_one M]
  congr 1
  refine ULift.ext _ _ ?_
  change (Nat.card k₀ : PadicAlgCl l) ^ d *
    ((WeilSheaf.cyclotomicUnit k₀ l ^ d : (PadicAlgCl l)ˣ) : PadicAlgCl l) = 1
  rw [Units.val_pow_eq_pow_val, WeilSheaf.cyclotomicUnit_eq, ← mul_pow,
    mul_inv_cancel₀ purity_natCard_ne_zero_padicAlgCl, one_pow]

end Scalar

namespace ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The structure morphism of a Weil sheaf transported to the condensed model. -/
lemma purity_toCondensed_obj_obj_str (K : ProEtaleWeilSheaf k₀ l X) :
    ((toCondensed k₀ l X).obj K).obj.str =
      (condensedFrobeniusComparison k₀ l X).hom.app K.carrier ≫
        (adicSheafEquivCondensedMod l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.map
          K.obj.str :=
  rfl

/-- The structure morphism of a constant twist in the condensed model: the structure morphism
followed by the scalar. -/
lemma purity_toCondensed_obj_obj_str_constantTwist (b : (PadicAlgCl l)ˣ) (K : ProEtaleWeilSheaf k₀ l X) :
    ((toCondensed k₀ l X).obj ((constantTwist k₀ l X b).obj K)).obj.str =
      ((toCondensed k₀ l X).obj K).obj.str ≫
        (adicSheafEquivCondensedMod l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.map
          (AdicSheaf.smul (ULift.up (b : PadicAlgCl l)) K.carrier) := by
  rw [purity_toCondensed_obj_obj_str, purity_toCondensed_obj_obj_str, IsoAlgebra.twist_obj_obj_str,
    frobeniusPullbackSmulIso_hom_app, AdicSheaf.smul_comp, Functor.map_comp, Category.assoc]
  try rfl

/-- The structure morphism of a pulled-back Weil object in the condensed model. -/
lemma purity_geometricFiberWeilLowerStar_obj_obj_str
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X)) :
    ((CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀))).obj M).obj.str =
      (CondensedRing.geometricFiberProjLowerStarFrobeniusIso (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀))).hom.app M :=
  rfl

/-- **The Tate encoding, compatibility of the Weil structures.** -/
lemma purity_tateTwistSheafCondensedIso_aux (d : ℕ)
    (ψ : (toCondensed k₀ l X).obj (adicConstant k₀ l X) ≅
      (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀))).obj (𝟙_ _)) :
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*⟦Profinite.padicAlgClRingObj l⟧.map
          (ψ.hom.hom.f ≫ (CondensedRing.purity_tateTwistNatTrivialization' (X ↘ Spec (CommRingCat.of k₀))
            (purity_tateRootsSystem_spec k₀ l).1 (purity_tateRootsSystem_spec k₀ l).2 d).inv) ≫
        (CondensedRing.geometricFiberProjLowerStarFrobeniusIso (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀))).hom.app (tateTwistNat X l d) =
      ((toCondensed k₀ l X).obj ((constantTwist k₀ l X (WeilSheaf.cyclotomicUnit k₀ l ^ d)).obj
          (adicConstant k₀ l X))).obj.str ≫
        (ψ.hom.hom.f ≫ (CondensedRing.purity_tateTwistNatTrivialization' (X ↘ Spec (CommRingCat.of k₀))
          (purity_tateRootsSystem_spec k₀ l).1 (purity_tateRootsSystem_spec k₀ l).2 d).inv) := by
  letI := CondensedRing.modLinear (Profinite.padicAlgClRingObj l)
    (Profinite.PadicAlgCl.constRingHom l) (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  have hN0 : ((((Nat.card k₀ : ℤ) ^ d : ℤ)) : PadicAlgCl l) ≠ 0 := by
    push_cast
    exact pow_ne_zero _ purity_natCard_ne_zero_padicAlgCl
  have hψ : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*⟦Profinite.padicAlgClRingObj l⟧.map
      ψ.hom.hom.f ≫ (CondensedRing.geometricFiberProjLowerStarFrobeniusIso
        (Profinite.padicAlgClRingObj l) (X ↘ Spec (CommRingCat.of k₀))).hom.app (𝟙_ _) =
      ((toCondensed k₀ l X).obj (adicConstant k₀ l X)).obj.str ≫ ψ.hom.hom.f := ψ.hom.hom.h
  have hlaw := CondensedRing.purity_tateTwistNatTrivialization'_weil_lowerStar
    (X ↘ Spec (CommRingCat.of k₀)) (purity_tateRootsSystem_spec k₀ l).1 (purity_tateRootsSystem_spec k₀ l).2 d
  have key : ((Nat.card k₀ : ℤ) ^ d) •
      (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*⟦Profinite.padicAlgClRingObj l⟧.map
          (ψ.hom.hom.f ≫ (CondensedRing.purity_tateTwistNatTrivialization' (X ↘ Spec (CommRingCat.of k₀))
            (purity_tateRootsSystem_spec k₀ l).1 (purity_tateRootsSystem_spec k₀ l).2 d).inv) ≫
        (CondensedRing.geometricFiberProjLowerStarFrobeniusIso (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀))).hom.app (tateTwistNat X l d)) =
      ((Nat.card k₀ : ℤ) ^ d) •
      (((toCondensed k₀ l X).obj ((constantTwist k₀ l X (WeilSheaf.cyclotomicUnit k₀ l ^ d)).obj
          (adicConstant k₀ l X))).obj.str ≫
        (ψ.hom.hom.f ≫ (CondensedRing.purity_tateTwistNatTrivialization' (X ↘ Spec (CommRingCat.of k₀))
          (purity_tateRootsSystem_spec k₀ l).1 (purity_tateRootsSystem_spec k₀ l).2 d).inv)) := by
    rw [Functor.map_comp, Category.assoc, ← Preadditive.comp_zsmul, hlaw, reassoc_of% hψ,
      purity_toCondensed_obj_obj_str_constantTwist, Category.assoc, ← Preadditive.comp_zsmul,
      ← Preadditive.comp_zsmul, Functor.purity_map_comp_zsmul_eq_self_of_comp_zsmul_id _ _ _
        (AdicSheaf.purity_smul_cyclotomicUnit_pow_comp_zsmul _ d)]
  have key' := congrArg (fun x ↦ ((((Nat.card k₀ : ℤ) ^ d : ℤ)) : PadicAlgCl l)⁻¹ • x) key
  simp only [← Int.cast_smul_eq_zsmul (R := PadicAlgCl l), inv_smul_smul₀ hN0] at key'
  exact key'

/-- **The Tate encoding**: given the comparison `ψ : E(ℚ̄_ℓ) ≅ p^* ℚ̄_ℓ,X` of the constant Weil
sheaf with the pulled-back unit in the condensed model, the Weil Tate sheaf `ℚ̄_ℓ(d)` of the old
model corresponds to the pulled-back condensed Tate twist `p^* ℚ̄_ℓ,X(d)` with its canonical
Weil structure. -/
noncomputable def purity_tateTwistSheafCondensedIso (d : ℕ)
    (ψ : (toCondensed k₀ l X).obj (adicConstant k₀ l X) ≅
      (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀))).obj (𝟙_ _)) :
    (toCondensed k₀ l X).obj (WeilSheaf.tateTwistSheaf k₀ l X d).obj ≅
      (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
        (X ↘ Spec (CommRingCat.of k₀))).obj (ProEtale.tateTwist X l d) :=
  (toCondensed k₀ l X).mapIso (WeilSheaf.tateTwistSheafNatObjIso k₀ l X d) ≪≫
    IsoAlgebra.isoMk ((IsoAlgebra.forget _).mapIso ψ ≪≫
      (CondensedRing.purity_tateTwistNatTrivialization' (X ↘ Spec (CommRingCat.of k₀))
        (purity_tateRootsSystem_spec k₀ l).1 (purity_tateRootsSystem_spec k₀ l).2 d).symm) (by
      rw [Iso.trans_hom, Functor.mapIso_hom, IsoAlgebra.forget_map, Iso.symm_hom]
      exact purity_tateTwistSheafCondensedIso_aux d ψ)

end ProEtaleWeilSheaf

end AlgebraicGeometry
