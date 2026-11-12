/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RingTheory.SimpleModule.Basic
public import WeilConjectures.SixFunctors.NearbyCycles.RestrictScalars
public import WeilConjectures.TraceFormula.Specialization.FiniteCoefficientConstantComap
public import WeilConjectures.TraceFormula.Specialization.FiniteCoefficientConstantTriangle
public import WeilConjectures.TraceFormula.Specialization.NormalizePrecoherent

/-!

# The thick origin for every finite module over a finite `ℓ`-torsion ring

Let `X = 𝔸¹_k` and `Z = V(x^m)` with `m ≥ 1`, and let `T` be a finite commutative ring killed by a
power of a prime `ℓ ≠ char k'`. Blueprint `lemma-case-z-v-x-m--1` asserts that the defect
`C_{X,Z}(M_X)` of the constant complex of every finite `T`-module `M` vanishes
(`ProEtale.CondensedRing.isZero_specializationDefect_polyAffineThickOrigin_finiteModule`).

The proof is a dévissage. The complexes with vanishing defect form a triangulated subcategory,
and short exact sequences of `T`-modules give distinguished triangles of constant complexes
(`ProEtale.exists_distinguished_finiteCoefficientConstantFunctor`), so by a composition series
(`ModuleCat.induction_on_finite`) it suffices to treat the residue fields `T ⧸ 𝔪`. The constant
complex of `T ⧸ 𝔪` is the restriction of scalars of the unit with coefficients in the field
`T ⧸ 𝔪` (`ProEtale.finiteCoefficientConstantFunctorObjComapIso`), in which `ℓ` vanishes. The defect
of the unit with coefficients `T ⧸ 𝔪` vanishes
(`ProEtale.CondensedRing.isZero_specializationDefect_polyAffineThickOrigin_unit_finiteCoefficient`),
and restriction of scalars preserves the invertibility of the zero-section map, a pullback
exchange of nearby cycles
(`ProEtale.CondensedRing.NearbyCyclesModel.Hom.isIso_pullbackExchange_app_comap`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

-- `Mod.comap_additive` and `Mod.instAdditiveComap_weilConjectures` are two instances for the same
-- fact; the results on restriction of scalars used here are stated with the latter, and mixing
-- the two makes unification very slow.
attribute [-instance] Mod.comap_additive

namespace AlgebraicGeometry.ProEtale.CondensedRing

section ZeroSectionMap

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k']
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The zero-section map `ε_{X,Z}(L)` is invertible if and only if the pullback exchange of the
morphism of models `Z × S ⟶ 𝒟_Z X` is invertible at `L`: the former is by definition a
component of the latter. -/
lemma isIso_zeroSectionMap_iff
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))) :
    IsIso (zeroSectionMap X I k' Λ L) ↔
      IsIso (((zeroSectionDeformationModelHom X I k').pullbackExchange Λ).app L) :=
  Iff.rfl

end ZeroSectionMap

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

omit [IsSepClosed k'] [Fact (ringChar k').Prime] [Finite T] in
/-- **Restriction of scalars of a vanishing defect**: for a morphism `ρ : T →+* T'` of finite
coefficient rings, if the defect `C_{X,Z}(T'̲)` of the unit with coefficients `T'` vanishes, then
so does the defect of its restriction of scalars to `T`. The zero-section map is a pullback
exchange of nearby cycles, whose invertibility is preserved by restriction of scalars. -/
theorem isZero_specializationDefect_comap_unit (X : Over (Spec (.of k)))
    (I : X.left.IdealSheafData) {T' : Type} [TopologicalSpace T'] [CommRing T']
    [IsTopologicalRing T'] [DiscreteTopology T'] [Finite T'] (ρ : T →+* T')
    (h : IsZero (specializationDefect X I k' (Profinite.continuousMapRingObj.{u} T') (𝟙_ _))) :
    IsZero (specializationDefect X I k' (Profinite.continuousMapRingObj.{u} T)
      ((Mod.comap (coefficientMap (Profinite.continuousMapRingObjMap.{u} ρ
        continuous_of_discreteTopology) X.left)).mapDerivedCategory.obj (𝟙_ _))) := by
  rw [isZero_specializationDefect_iff, isIso_zeroSectionMap_iff] at h ⊢
  have := (zeroSectionDeformationModelHom X I k').isIso_pullbackExchange_app_comap
    (Profinite.continuousMapRingObjMap.{u} ρ continuous_of_discreteTopology) _ h
  -- the two sides carry different proofs of `Precoherent Profinite`
  revert this
  normalize_precoherent
  exact id

omit [Fact ℓ.Prime] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] in
/-- The residue fields of a finite ring killed by a power of `ℓ` are killed by `ℓ`. -/
lemma natCast_eq_zero_quotient_of_pow_eq_zero {R : Type*} [CommRing R] {n : ℕ}
    (hR : (ℓ : R) ^ n = 0) (𝔪 : Ideal R) [𝔪.IsMaximal] : (ℓ : R ⧸ 𝔪) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk 𝔪), Ideal.Quotient.eq_zero_iff_mem]
  exact (Ideal.IsMaximal.isPrime ‹_›).mem_of_pow_mem n (hR ▸ 𝔪.zero_mem)

/-- **The case `Z = V(x^m)` for the residue fields**: let `T` be a finite commutative ring killed by
a power of a prime `ℓ ≠ char k'` and `𝔪` a maximal ideal of `T`. For `m ≥ 1`, the defect
`C_{𝔸¹, V(x^m)}((T ⧸ 𝔪)_X)` of the constant complex of the residue field vanishes. -/
theorem isZero_specializationDefect_polyAffineThickOrigin_quotient {n : ℕ}
    (hT : (ℓ : T) ^ n = 0) {m : ℕ} (hm : 0 < m) (𝔪 : Ideal (ULift.{u + 1} T)) [𝔪.IsMaximal] :
    IsZero (specializationDefect (polyAffine k 1) (polyAffineThickOrigin k m) k'
      (Profinite.continuousMapRingObj.{u} T)
      ((finiteCoefficientConstantFunctor T (polyAffine k 1).left).obj
        (ModuleCat.of (ULift.{u + 1} T) (ULift.{u + 1} T ⧸ 𝔪)))) := by
  let 𝔪₀ : Ideal T := 𝔪.comap (ULift.ringEquiv.symm : T ≃+* ULift.{u + 1} T).toRingHom
  have : 𝔪₀.IsMaximal := Ideal.comap_isMaximal_of_surjective _ ULift.ringEquiv.symm.surjective
  let ρ : T →+* T ⧸ 𝔪₀ := Ideal.Quotient.mk 𝔪₀
  have : DiscreteTopology (T ⧸ 𝔪₀) :=
    ⟨eq_bot_of_singletons_open fun _ ↦ isOpen_coinduced.mpr (isOpen_discrete _)⟩
  have : Finite (T ⧸ 𝔪₀) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  have hℓ : (ℓ : T ⧸ 𝔪₀) ^ 1 = 0 := by
    rw [pow_one]
    exact natCast_eq_zero_quotient_of_pow_eq_zero hT 𝔪₀
  have h₁ := isZero_specializationDefect_polyAffineThickOrigin_unit_finiteCoefficient (k := k)
    (T ⧸ 𝔪₀) k' hℓ hm
  have h₂ := isZero_specializationDefect_comap_unit k' T _ _ ρ h₁
  -- the residue field `ULift T ⧸ 𝔪`, as a module over `ULift T`, is `T ⧸ 𝔪₀` viewed as a
  -- `T`-module
  let f : ULift.{u + 1} T →ₗ[ULift.{u + 1} T]
      (ModuleCat.restrictScalars ρ.ulift).obj
        (ModuleCat.of (ULift.{u + 1} (T ⧸ 𝔪₀)) (ULift.{u + 1} (T ⧸ 𝔪₀))) :=
    { toFun := fun x ↦ ρ.ulift x
      map_add' := map_add ρ.ulift
      map_smul' := fun c x ↦ by
        change ρ.ulift (c * x) = ρ.ulift c * ρ.ulift x
        exact map_mul ρ.ulift c x }
  have hf : Function.Surjective f := fun y ↦
    ⟨ULift.up (Ideal.Quotient.mk_surjective y.down).choose,
      ULift.ext (Ideal.Quotient.mk_surjective y.down).choose_spec⟩
  have hker : LinearMap.ker f = 𝔪 := by
    ext x
    change ρ.ulift x = 0 ↔ x ∈ 𝔪
    rw [← ULift.down_inj, ULift.zero_down]
    exact Ideal.Quotient.eq_zero_iff_mem
  let e : ModuleCat.of (ULift.{u + 1} T) (ULift.{u + 1} T ⧸ 𝔪) ≅
      (ModuleCat.restrictScalars ρ.ulift).obj
        (ModuleCat.of (ULift.{u + 1} (T ⧸ 𝔪₀)) (ULift.{u + 1} (T ⧸ 𝔪₀))) :=
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hf)).toModuleIso
  exact (vanishingDefect (polyAffine k 1) (polyAffineThickOrigin k m) k' _).prop_of_iso
    ((finiteCoefficientConstantFunctorObjComapIso ρ (polyAffine k 1).left).symm ≪≫
      (finiteCoefficientConstantFunctor T (polyAffine k 1).left).mapIso e.symm) h₂

/-- **The case `Z = V(x^m) ⊆ 𝔸¹`** (blueprint `lemma-case-z-v-x-m--1`): let `T` be a finite
commutative ring killed by a power `ℓ^n` of a prime `ℓ ≠ char k'`. For `X = 𝔸¹_k`,
`Z = V(x^m)` with `m ≥ 1` and every finite `T`-module `M`, the defect `C_{X,Z}(M_X)` of the
constant complex `M_X` vanishes. By dévissage along a composition series of `M`, it suffices to
treat the residue fields of `T`
(`isZero_specializationDefect_polyAffineThickOrigin_quotient`). -/
theorem isZero_specializationDefect_polyAffineThickOrigin_finiteModule {n : ℕ}
    (hT : (ℓ : T) ^ n = 0) {m : ℕ} (hm : 0 < m) (M : ModuleCat.{u + 1} (ULift.{u + 1} T))
    [Module.Finite (ULift.{u + 1} T) M] :
    IsZero (specializationDefect (polyAffine k 1) (polyAffineThickOrigin k m) k'
      (Profinite.continuousMapRingObj.{u} T)
      ((finiteCoefficientConstantFunctor T (polyAffine k 1).left).obj M)) := by
  let G := finiteCoefficientConstantFunctor T (polyAffine k 1).left
  let V := vanishingDefect (polyAffine k 1) (polyAffineThickOrigin k m) k'
    (Profinite.continuousMapRingObj.{u} T)
  refine ModuleCat.induction_on_finite (fun N ↦ V (G.obj N)) (fun e h ↦ V.prop_of_iso
    (G.mapIso e) h) (fun N _ ↦ V.prop_of_isZero (G.map_isZero
      (ModuleCat.isZero_of_subsingleton N))) (fun 𝔪 _ ↦ ?_) (fun S hS h₁ h₃ ↦ ?_) M
  · exact isZero_specializationDefect_polyAffineThickOrigin_quotient k' T hT hm 𝔪
  · obtain ⟨_, hd⟩ := exists_distinguished_finiteCoefficientConstantFunctor T
      (polyAffine k 1).left hS
    exact isZero_specializationDefect_of_distTriang _ _ k' _ hd h₁ h₃

end AlgebraicGeometry.ProEtale.CondensedRing
