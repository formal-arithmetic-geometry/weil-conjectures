/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Two.TwoTermTensorCoordinates
import all WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement

/-! # Evaluation of the two surviving tensor coordinates

For a complex `Q` concentrated in degrees `-1` and `0` with both terms identified with the unit,
the total tensor `A ⊗ Q` in degree `n` is `A^(n+1) ⊕ A^n`. We compute the two coordinates of
this decomposition on pure tensors of local sections.

## References

* Stacks Project, Tags 03EK, 0A8X.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace WeilConjectures.IntegralHom

variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})

attribute [local instance 2000] abSheafify abLocallyBijective

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [local irreducible] homComplexFunctor

local instance twoTermTensorCoordinateSectionsLocal1 :
    MonoidalCategory (Modules.{t, u} Y R) :=
  SheafOfModules.monoidalCategory R

local instance twoTermTensorCoordinateSectionsLocal2 : HasBinaryBiproducts (Modules.{t, u} Y R) :=
  HasBinaryBiproducts.of_hasBinaryProducts

local instance twoTermTensorCoordinateSectionsLocal3 :
    HasColimitsOfSize.{0, 0} (Modules.{t, u} Y R) :=
  countableColimits Y R

local instance twoTermTensorCoordinateSectionsLocal4 :
    (ordinaryTensor Y R).PreservesZeroMorphisms :=
  ordinaryTensorZero Y R

local instance twoTermTensorCoordinateSectionsLocal5 (M : Modules.{t, u} Y R) :
    ((ordinaryTensor Y R).obj M).PreservesZeroMorphisms := ordinaryTensorObjZero Y R M

local instance twoTermTensorCoordinateSectionsLocal6 (K L : CochainComplex (Modules.{t, u} Y R) ℤ) :
    CochainComplex.HasMapBifunctor K L (ordinaryTensor Y R) := fun _j ↦
  @HasColimitsOfShape.has_colimit _ _ _ _
    ((countableColimits.{t, u} Y R).has_colimits_of_shape _) _

namespace TwoTermCoordinates

/-- A section of the unit module, viewed as a section of the structure sheaf. -/
def unitSection (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ) :
    (𝟙_ (Modules.{t, u} Y R)).val.obj U → R.obj.obj U := fun a ↦ a

/-- The right unitor sends the pure tensor `x ⊗ a` to `a • x`. -/
theorem unitor_pair (M : Modules.{t, u} Y R)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : M.val.obj U) (a : (𝟙_ (Modules.{t, u} Y R)).val.obj U) :
    (ρ_ M).hom.val.app U (pair Y R M (𝟙_ _) U x a) = unitSection Y R U a • x := by
  exact RingedDerivedNative.pureTensor_rightUnitor.{t+1,t,u}
    (AlgebraicGeometry.Scheme.ProEt.topology Y) R M U a x

attribute [local irreducible] SheafOfModules.monoidalCategory

/-- The zero morphism of modules vanishes on every local section. -/
theorem zero_apply (M N : Modules.{t, u} Y R)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ) (x : M.val.obj U) :
    (0 : M ⟶ N).val.app U x = 0 := rfl

/-- Tensoring with an isomorphism `e : N ≅ 𝟙` followed by the right unitor sends `x ⊗ z`
to `e(z) • x`. -/
theorem contract_pair (M N : Modules.{t, u} Y R)
    (e : N ≅ (𝟙_ (Modules.{t, u} Y R)))
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : M.val.obj U) (z : N.val.obj U) :
    ((((ordinaryTensor Y R).obj M).map e.hom ≫ (ρ_ M).hom).val.app U)
      (pair Y R M N U x z) = (unitSection Y R U (e.hom.val.app U z)) • x := by
  have hm := CategoryTheory.CochainPullback.moduleTmul_map (𝟙 M) e.hom U x z
  rw [MonoidalCategory.id_tensorHom] at hm
  simp only [SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] at hm
  change (((ordinaryTensor Y R).obj M).map e.hom).val.app U
      (pair Y R M N U x z) = pair Y R M (𝟙_ _) U x (e.hom.val.app U z) at hm
  exact (congrArg (fun w ↦ (ρ_ M).hom.val.app U w) hm).trans
    (unitor_pair Y R M U x (e.hom.val.app U z))

variable (A Q : CochainComplex (Modules.{t, u} Y R) ℤ)
  (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
  (eNeg : Q.X (-1) ≅ (𝟙_ (Modules.{t, u} Y R)))
  (eZero : Q.X 0 ≅ (𝟙_ (Modules.{t, u} Y R)))

/-- The first (degree `-1`) coordinate of the two-term tensor decomposition, restricted to
the summand `A^a ⊗ Q^b`: it is contraction with `eNeg` if `b = -1` and zero otherwise. -/
theorem neg_coordinate (a b n : ℤ) (hab : a + b = n) :
    CochainComplex.ιMapBifunctor A Q (ordinaryTensor Y R) a b n hab ≫
      (twoTermTensorIso Y R A Q hzero eNeg eZero n).hom ≫ biprod.fst =
    if hb : b = -1 then
      eqToHom (congrArg₂ (fun i k ↦ ((ordinaryTensor Y R).obj (A.X i)).obj (Q.X k))
        (show a = n + 1 by omega) hb) ≫
      ((ordinaryTensor Y R).obj (A.X (n + 1))).map eNeg.hom ≫
        (ρ_ (A.X (n + 1))).hom
    else 0 := by
  classical
  by_cases hb : b = -1
  · subst b
    obtain rfl : a = n + 1 := by omega
    rw [twoTermTensorIso_ι_neg_hom_assoc]
    simp
  · by_cases hb' : b = 0
    · subst b
      obtain rfl : a = n := by omega
      rw [twoTermTensorIso_ι_zero_hom_assoc]
      simp [hb]
    · exact (((ordinaryTensor Y R).obj (A.X a)).map_isZero
        (hzero b hb hb')).eq_of_src _ _

/-- The second (degree `0`) coordinate of the two-term tensor decomposition, restricted to
the summand `A^a ⊗ Q^b`: it is contraction with `eZero` if `b = 0` and zero otherwise. -/
theorem zero_coordinate (a b n : ℤ) (hab : a + b = n) :
    CochainComplex.ιMapBifunctor A Q (ordinaryTensor Y R) a b n hab ≫
      (twoTermTensorIso Y R A Q hzero eNeg eZero n).hom ≫ biprod.snd =
    if hb : b = 0 then
      eqToHom (congrArg₂ (fun i k ↦ ((ordinaryTensor Y R).obj (A.X i)).obj (Q.X k))
        (show a = n by omega) hb) ≫
      ((ordinaryTensor Y R).obj (A.X n)).map eZero.hom ≫ (ρ_ (A.X n)).hom
    else 0 := by
  classical
  by_cases hb : b = 0
  · subst b
    obtain rfl : a = n := by omega
    rw [twoTermTensorIso_ι_zero_hom_assoc]
    simp
  · by_cases hb' : b = -1
    · subst b
      obtain rfl : a = n + 1 := by omega
      rw [twoTermTensorIso_ι_neg_hom_assoc]
      simp [hb]
    · exact (((ordinaryTensor Y R).obj (A.X a)).map_isZero
        (hzero b hb' hb)).eq_of_src _ _

/-- The pure tensor `x ⊗ z` of local sections, as a section of the total tensor in degree
`n = a + b`. -/
noncomputable def generator (a b n : ℤ) (hab : a + b = n)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : (A.X a).val.obj U) (z : (Q.X b).val.obj U) :
    ((((totalTensor Y R).obj A).obj Q).X n).val.obj U :=
  (CochainComplex.ιMapBifunctor A Q (ordinaryTensor Y R) a b n hab).val.app U
    (pair Y R (A.X a) (Q.X b) U x z)

/-- Transporting a total pure tensor along `a + b = n` gives `generator`. -/
theorem generator_transport (a b n : ℤ) (h : a + b = n)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : (A.X a).val.obj U) (z : (Q.X b).val.obj U) :
    (eqToHom (congrArg (fun k ↦ (((totalTensor Y R).obj A).obj Q).X k) h)).val.app U
      (totalPair Y R A Q a b U x z) = generator Y R A Q a b n h U x z := by
  subst n
  rfl

/-- The first coordinate of `x ⊗ z` with `z` in degree `-1` is `eNeg(z) • x`. -/
theorem generator_neg_fst (n : ℤ)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : (A.X (n + 1)).val.obj U) (z : (Q.X (-1)).val.obj U) :
    (((twoTermTensorIso Y R A Q hzero eNeg eZero n).hom ≫ biprod.fst).val.app U)
      (generator Y R A Q (n + 1) (-1) n (by omega) U x z) =
        (unitSection Y R U (eNeg.hom.val.app U z)) • x := by
  have h := congrArg (fun f ↦ f.val.app U (pair Y R _ _ U x z))
    (neg_coordinate Y R A Q hzero eNeg eZero (n + 1) (-1) n (by omega))
  simp only [dite_true, eqToHom_refl, Category.id_comp] at h
  exact h.trans (contract_pair Y R _ _ eNeg U x z)

/-- The first coordinate of `x ⊗ z` with `z` in degree `0` vanishes. -/
theorem generator_zero_fst (n : ℤ)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : (A.X n).val.obj U) (z : (Q.X 0).val.obj U) :
    (((twoTermTensorIso Y R A Q hzero eNeg eZero n).hom ≫ biprod.fst).val.app U)
      (generator Y R A Q n 0 n (by simp) U x z) = 0 := by
  have h := congrArg (fun f ↦ f.val.app U (pair Y R _ _ U x z))
    (neg_coordinate Y R A Q hzero eNeg eZero n 0 n (by simp))
  simp only [dite_eq_right (by omega : (0 : ℤ) ≠ -1)] at h
  exact h.trans (zero_apply Y R _ _ U _)

/-- The second coordinate of `x ⊗ z` with `z` in degree `-1` vanishes. -/
theorem generator_neg_snd (n : ℤ)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : (A.X (n + 1)).val.obj U) (z : (Q.X (-1)).val.obj U) :
    (((twoTermTensorIso Y R A Q hzero eNeg eZero n).hom ≫ biprod.snd).val.app U)
      (generator Y R A Q (n + 1) (-1) n (by omega) U x z) = 0 := by
  have h := congrArg (fun f ↦ f.val.app U (pair Y R _ _ U x z))
    (zero_coordinate Y R A Q hzero eNeg eZero (n + 1) (-1) n (by omega))
  simp only [dite_eq_right (by omega : (-1 : ℤ) ≠ 0)] at h
  exact h.trans (zero_apply Y R _ _ U _)

/-- The second coordinate of `x ⊗ z` with `z` in degree `0` is `eZero(z) • x`. -/
theorem generator_zero_snd (n : ℤ)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : (A.X n).val.obj U) (z : (Q.X 0).val.obj U) :
    (((twoTermTensorIso Y R A Q hzero eNeg eZero n).hom ≫ biprod.snd).val.app U)
      (generator Y R A Q n 0 n (by simp) U x z) =
        (unitSection Y R U (eZero.hom.val.app U z)) • x := by
  have h := congrArg (fun f ↦ f.val.app U (pair Y R _ _ U x z))
    (zero_coordinate Y R A Q hzero eNeg eZero n 0 n (by simp))
  simp only [dite_true, eqToHom_refl, Category.id_comp] at h
  exact h.trans (contract_pair Y R _ _ eZero U x z)

/-- Version of `generator_neg_fst` for `x` in degree `a` with `a + (-1) = n`. -/
theorem generator_neg_fst_transport (n a : ℤ) (h : a + (-1) = n)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : (A.X a).val.obj U) (z : (Q.X (-1)).val.obj U) :
    (eqToHom (congrArg A.X (show n + 1 = a by omega))).val.app U
      ((((twoTermTensorIso Y R A Q hzero eNeg eZero n).hom ≫ biprod.fst).val.app U)
        (generator Y R A Q a (-1) n h U x z)) =
        (unitSection Y R U (eNeg.hom.val.app U z)) • x := by
  obtain rfl : a = n + 1 := by omega
  simpa only [eqToHom_refl, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply] using generator_neg_fst Y R A Q hzero eNeg eZero n U x z

/-- Version of `generator_neg_snd` for `x` in degree `a` with `a + (-1) = n`. -/
theorem generator_neg_snd_general (n a : ℤ) (h : a + (-1) = n)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (x : (A.X a).val.obj U) (z : (Q.X (-1)).val.obj U) :
    (((twoTermTensorIso Y R A Q hzero eNeg eZero n).hom ≫ biprod.snd).val.app U)
      (generator Y R A Q a (-1) n h U x z) = 0 := by
  obtain rfl : a = n + 1 := by omega
  exact generator_neg_snd Y R A Q hzero eNeg eZero n U x z

end TwoTermCoordinates

end WeilConjectures.IntegralHom
