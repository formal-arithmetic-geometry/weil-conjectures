/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.EmbeddedEllLattice
public import Sheaf.NumberTheory.Padics.CoefficientExtension
import Sheaf.Paper.LatticeScalarExtensionFractions
import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.Topology.ContinuousMap.Algebra

/-! # Rationalization of full embedded lattices -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits Opposite
open scoped ChangeOfRings CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local instance] latticeWeakSheafifyOver latticeWEqualsOver

variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]

section CanonicalMap

variable {X : Scheme.{u}}
  {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
  (a : R ⟶ S) (U : X.ProEt)
  (M : SheafOfModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)))
  (L : SheafOfModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (S.over U)))
  (j : M ⟶ (SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (latticeScalarMap a U))).obj L)

private theorem latticeTensorUnit_zero (T : (Over U)ᵒᵖ) :
    (latticeTensorUnit a U M).app T
      ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
        ((latticeScalarMap a U).hom.app T).hom] (0 : M.val.obj T)) = 0 := by
  rw [TensorProduct.tmul_zero, map_zero]

private def inclusionTensorPresheafMap :
    SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
      (latticeScalarMap a U) M ⟶ L.val where
  app T := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
    ((latticeScalarMap a U).hom.app T).hom (j.val.app T)
  naturality := by
    intro T T' f
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change _ = L.val.map f
      ((1 : (S.over U).obj.obj T) • (show L.val.obj T from j.val.app T m))
    have hm := Classical.choose_spec
      (SheafOfModules.exists_changeOfRingsMap.{u, u + 1, u + 1}
        (latticeScalarMap a U) M f) (1 : (S.over U).obj.obj T) m
    change SheafOfModules.changeOfRingsMap.{u, u + 1, u + 1}
      (latticeScalarMap a U) M f
        ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
          ((latticeScalarMap a U).hom.app T).hom] m) = _ at hm
    change (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
      ((latticeScalarMap a U).hom.app T').hom (j.val.app T'))
        (SheafOfModules.changeOfRingsMap.{u, u + 1, u + 1}
          (latticeScalarMap a U) M f _) = _
    rw [hm]
    change (S.over U).obj.map f 1 • (show L.val.obj T' from j.val.app T' (M.val.map f m)) =
      L.val.map f (1 • (show L.val.obj T from j.val.app T m))
    rw [map_one, one_smul, one_smul]
    exact PresheafOfModules.naturality_apply j.val f m

private def inclusionTensorMap :
    SheafOfModules.changeOfRings.{u, u + 1, u + 1}
      (latticeScalarMap a U) M ⟶ L :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (S.over U)).obj)).symm (inclusionTensorPresheafMap a U M L j)

private theorem inclusionTensorMap_unit (T : (Over U)ᵒᵖ) (m : M.val.obj T) :
    (inclusionTensorMap a U M L j).val.app T ((latticeTensorUnit a U M).app T
      ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
        ((latticeScalarMap a U).hom.app T).hom] m)) = j.val.app T m := by
  have h := (PresheafOfModules.sheafificationHomEquiv
    (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (S.over U)).obj)).apply_symm_apply (inclusionTensorPresheafMap a U M L j)
  change PresheafOfModules.sheafificationHomEquiv _
    (inclusionTensorMap a U M L j) = inclusionTensorPresheafMap a U M L j at h
  have hd := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
    (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (S.over U)).obj) (inclusionTensorMap a U M L j)
  rw [h] at hd
  have he := congrArg (fun f ↦ (f.app T)
    ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
      ((latticeScalarMap a U).hom.app T).hom] m)) hd
  change (1 : (S.over U).obj.obj T) • (show L.val.obj T from j.val.app T m) =
    (inclusionTensorMap a U M L j).val.app T ((latticeTensorUnit a U M).app T
      ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
        ((latticeScalarMap a U).hom.app T).hom] m)) at he
  exact he.symm.trans (one_smul _ _)

end CanonicalMap

omit [FiniteDimensional ℚ_[ell] E] in
private theorem rational_nsmul_injective (X : Scheme.{u}) (U : X.ProEt)
    (L : SheafOfModules.{u + 1} ((latticeModuleRing X E).over U))
    (T : (Over U)ᵒᵖ) (n : ℕ) :
    Function.Injective (fun x : L.val.obj T ↦ ell ^ n • x) := by
  have he : (ell : E) ≠ 0 := by
    have h : (ell : ℚ_[ell]) ≠ 0 := by
      exact_mod_cast (Fact.out : ell.Prime).ne_zero
    simpa only [map_natCast, map_zero] using (algebraMap ℚ_[ell] E).injective.ne h
  have hu : IsUnit ((ell ^ n : ℕ) : (latticeCoefficientSheaf X E).obj.obj
      (op T.unop.left)) := by
    change IsUnit (((ell ^ n : ℕ) : ULift.{u + 1} C(T.unop.left.left, E)))
    rw [Nat.cast_pow]
    apply IsUnit.pow
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr he).map
        (ULift.ringEquiv.symm.toRingHom.comp
          (ContinuousMap.C : E →+* C(T.unop.left.left, E)))
  intro x y h
  apply hu.smul_left_cancel.mp
  simpa only [Nat.cast_smul_eq_nsmul] using h

omit [FiniteDimensional ℚ_[ell] E] in
private theorem rational_inverse_nsmul (X : Scheme.{u}) (U : X.ProEt)
    (L : SheafOfModules.{u + 1} ((latticeModuleRing X E).over U))
    (T : (Over U)ᵒᵖ) (n : ℕ) (x : L.val.obj T) :
    latticeConstantCoefficient X E T.unop.left ((ell : E) ^ n)⁻¹ • (ell ^ n • x) = x := by
  rw [← Nat.cast_smul_eq_nsmul ((latticeCoefficientSheaf X E).obj.obj (op T.unop.left)),
    smul_smul]
  have hr : latticeConstantCoefficient X E T.unop.left ((ell : E) ^ n)⁻¹ *
      ((ell ^ n : ℕ) : (latticeCoefficientSheaf X E).obj.obj (op T.unop.left)) = 1 := by
    apply ULift.ext
    apply ContinuousMap.ext
    intro z
    change ((ell : E) ^ n)⁻¹ * ((ell ^ n : ℕ) : E) = 1
    rw [Nat.cast_pow]
    exact inv_mul_cancel₀ (pow_ne_zero n (by
      have h : (ell : ℚ_[ell]) ≠ 0 := by
        exact_mod_cast (Fact.out : ell.Prime).ne_zero
      simpa only [map_natCast, map_zero] using (algebraMap ℚ_[ell] E).injective.ne h))
  rw [hr, one_smul]

attribute [local irreducible] inclusionTensorMap inclusionTensorPresheafMap latticeTensorUnit

/-- The scalar-multiplication rationalization of a full embedded lattice is invertible.
Source: Bhatt--Scholze, Definition 6.8.3 and Proposition 6.8.4(6);
Stacks Project, Tag 03EK.
(blueprint: lem-sfb-full-embedded-lattice-rationalization).

Proof. Extend the inclusion of N into L by the balanced map s tensor n ↦ sn,
and sheafify. The resulting comparison sends the unit tensor of m to its ambient
section. For a section z in its kernel, local scalar-extension fractions give,
on a covering sieve, ell^n z = eta(1 tensor m). Applying the comparison gives
m = 0, since N is a submodule of L. Multiplication by ell^n is injective on the
rational module, so z is locally zero and hence zero by separatedness.
Fullness says that locally every x in L has ell^n x in N. The section
ell^(-n) eta(1 tensor (ell^n x)) maps to x, proving local surjectivity.
A locally bijective map between sheaves is an isomorphism, and forgetting module
structure reflects isomorphisms. Its unit formula is the original inclusion.
The argument applies to empty covers and the zero lattice, and requires no common
denominator on a non-quasi-compact object. -/
theorem full_embedded_lattice_rationalization (X : Scheme.{u})
    (L : SheafOfModules.{u + 1} (latticeModuleRing X E)) (U : X.ProEt)
    (N : SheafOfModules.EmbeddedEllLattice.{u + 1, u, u + 1} ell
      ((SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (latticeScalarMap (latticeCoefficientSheafMap X
            (Padic.coefficientExtensionIntegers ell E).subtype continuous_subtype_val) U))).obj
              (L.over U))) :
    let a := latticeCoefficientSheafMap X
      (Padic.coefficientExtensionIntegers ell E).subtype continuous_subtype_val
    let M : SheafOfModules.{u + 1}
        ((latticeModuleRing X (Padic.coefficientExtensionIntegers ell E)).over U) :=
      ⟨N.submodule.toPresheafOfModules, N.isSheaf⟩
    ∃ α : SheafOfModules.changeOfRings.{u, u + 1, u + 1} (latticeScalarMap a U) M ≅ L.over U,
      ∀ (T : (Over U)ᵒᵖ) (m : N.submodule.obj T),
        α.hom.val.app T ((latticeTensorUnit a U M).app T
          ((1 : (latticeCoefficientSheaf X E).obj.obj (op T.unop.left)) ⊗ₜ[
            (latticeCoefficientSheaf X
              (Padic.coefficientExtensionIntegers ell E)).obj.obj (op T.unop.left),
            ((a.hom.app (op T.unop.left)).hom)] m)) = Subtype.val m := by
  dsimp only
  let a := latticeCoefficientSheafMap X
    (Padic.coefficientExtensionIntegers ell E).subtype continuous_subtype_val
  let M : SheafOfModules.{u + 1}
      ((latticeModuleRing X (Padic.coefficientExtensionIntegers ell E)).over U) :=
    ⟨N.submodule.toPresheafOfModules, N.isSheaf⟩
  let j : M ⟶ (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (latticeScalarMap a U))).obj (L.over U) := ⟨N.submodule.ι⟩
  let b := inclusionTensorMap a U M (L.over U) j
  have hb := inclusionTensorMap_unit a U M (L.over U) j
  have hb' : ∀ T (m : M.val.obj T), b.val.app T ((latticeTensorUnit a U M).app T
      ((1 : (latticeCoefficientSheaf X E).obj.obj (op T.unop.left)) ⊗ₜ[
        (latticeCoefficientSheaf X
          (Padic.coefficientExtensionIntegers ell E)).obj.obj (op T.unop.left),
          ((a.hom.app (op T.unop.left)).hom)] m)) = (show N.submodule.obj T from m).val :=
    hb
  clear hb
  have hb := hb'
  clear hb'
  clear_value b
  let V := SheafOfModules.toSheaf.{u + 1} ((latticeModuleRing X E).over U)
  have hi : ∀ T, Function.Injective ((V.map b).hom.app T) := by
    intro T x y h
    change b.val.app T x = b.val.app T y at h
    suffices x - y = 0 by exact sub_eq_zero.mp this
    have hzero : b.val.app T (x - y) = 0 := by rw [map_sub, h, sub_self]
    obtain ⟨s, hs, hz⟩ := (lattice_scalar_extension_fractions ell E X U M).2
      T.unop (x - y)
    let Q := SheafOfModules.changeOfRings.{u, u + 1, u + 1} (latticeScalarMap a U) M
    apply Q.isSheaf.isSeparated _ _ hs
    intro W f hf
    obtain ⟨n, m, hm⟩ := hz W f hf
    have hbm := congrArg (b.val.app (op W)) hm
    rw [map_nsmul] at hbm
    rw [hb] at hbm
    have hn := PresheafOfModules.naturality_apply b.val f.op (x - y)
    rw [hn, hzero, map_zero, nsmul_zero] at hbm
    have hmzero : m = 0 := by
      apply Subtype.ext
      exact hbm.symm
    have hzunit := latticeTensorUnit_zero a U M (op W)
    rw [hmzero] at hm
    have hmzero' := hm.trans hzunit
    change Q.val.map f.op (x - y) = Q.val.map f.op 0
    have hm' : ell ^ n • (show Q.val.obj (op W) from Q.val.map f.op (x - y)) = 0 := hmzero'
    rw [map_zero]
    exact (rational_nsmul_injective ell E X U Q (op W) n)
      (by simpa only [nsmul_zero] using hm')
  have hinj : Sheaf.IsLocallyInjective (V.map b) :=
    (Sheaf.isLocallyInjective_iff_injective (V.map b)).mpr hi
  have hsurj : Sheaf.IsLocallySurjective (V.map b) := by
    constructor
    intro T x
    obtain ⟨s, hs, hx⟩ := N.full T x
    apply ((Scheme.ProEt.topology X).over U).superset_covering _ hs
    intro W f hf
    obtain ⟨n, hn⟩ := hx W f hf
    let m : M.val.obj (op W) := ⟨ell ^ n • (L.over U).val.map f.op x, hn⟩
    let r := latticeConstantCoefficient X E W.left ((ell : E) ^ n)⁻¹
    refine ⟨r • (latticeTensorUnit a U M).app (op W)
      ((1 : (latticeCoefficientSheaf X E).obj.obj (op W.left)) ⊗ₜ[
        (latticeCoefficientSheaf X (Padic.coefficientExtensionIntegers ell E)).obj.obj
          (op W.left), ((a.hom.app (op W.left)).hom)] m), ?_⟩
    change b.val.app (op W) (r • _) = (L.over U).val.map f.op x
    rw [(b.val.app (op W)).hom.map_smul]
    change r • b.val.app (op W) ((latticeTensorUnit a U M).app (op W)
      ((1 : (latticeCoefficientSheaf X E).obj.obj (op W.left)) ⊗ₜ[
        (latticeCoefficientSheaf X (Padic.coefficientExtensionIntegers ell E)).obj.obj
          (op W.left), ((a.hom.app (op W.left)).hom)] m)) = _
    have hunit := congrArg (fun z : (L.over U).val.obj (op W) ↦ r • z) (hb (op W) m)
    have hc := rational_inverse_nsmul ell E X U (L.over U) (op W) n
      ((L.over U).val.map f.op x)
    exact hunit.trans hc
  have : IsIso (V.map b) :=
    (Sheaf.isLocallyBijective_iff_isIso (V.map b)).mp ⟨hinj, hsurj⟩
  have : IsIso b := isIso_of_reflects_iso b V
  exact ⟨asIso b, hb⟩

end AlgebraicGeometry.ProEtale
