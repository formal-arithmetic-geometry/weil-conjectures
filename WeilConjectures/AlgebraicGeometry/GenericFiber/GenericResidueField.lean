/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.GenericFiber.SmoothLocusGenericPoint

/-!
# Residue fields at generic points of integral affine schemes

For an integral affine scheme `T`, the residue field at the generic point is a fraction field of
`Γ(T, ⊤)` (`AlgebraicGeometry.Scheme.isFractionRing_residueField_genericPoint`). For a ring map
`Γ(T, ⊤) ⟶ R'` to a domain `R'` with fraction field `K'`, we identify `K'` with the residue field
of `Spec R'` at its generic point, compatibly with the residue field map of `Spec R' ⟶ T`
(`AlgebraicGeometry.exists_ringEquiv_residueField_genericPoint_Spec`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

@[reassoc]
lemma Scheme.Γevaluation_residueFieldCongr (X : Scheme.{u}) {x y : X} (h : x = y) :
    X.Γevaluation x ≫ (X.residueFieldCongr h).hom = X.Γevaluation y := by
  subst h
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-- For an integral affine scheme `T`, the residue field at the generic point is a fraction field
of `Γ(T, ⊤)`. -/
lemma Scheme.isFractionRing_residueField_genericPoint (T : Scheme.{u}) [IsIntegral T]
    [IsAffine T] :
    letI := (T.Γevaluation (genericPoint T)).hom.toAlgebra
    IsFractionRing Γ(T, ⊤) (T.residueField (genericPoint T)) := by
  let := (T.Γevaluation (genericPoint T)).hom.toAlgebra
  have : Nonempty (⊤ : T.Opens) := ⟨⟨genericPoint T, trivial⟩⟩
  have : IsFractionRing Γ(T, ⊤) T.functionField :=
    functionField_isFractionRing_of_isAffineOpen T ⊤ (isAffineOpen_top T)
  have hη : genericPoint T ∈ genericPoints T := by
    rw [genericPoints_eq_singleton]
    rfl
  let e : T.functionField ≃ₐ[Γ(T, ⊤)] T.residueField (genericPoint T) :=
    { RingEquiv.ofBijective _ (Scheme.bijective_residue_of_mem_genericPoints hη) with
      commutes' := fun r ↦ rfl }
  exact IsLocalization.isLocalization_of_algEquiv _ e

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `T` be an integral affine scheme, `φ : Γ(T, ⊤) ⟶ R'` a ring map to a domain with fraction
field `K'`, and `ψ : κ(η_T) ⟶ K'` compatible with `φ`. Then `K'` is identified with the residue
field of `Spec R'` at its generic point, compatibly with `ψ` and the residue field map of
`Spec R' ⟶ T`. -/
theorem exists_ringEquiv_residueField_genericPoint_Spec {T : Scheme.{u}} [IsIntegral T]
    [IsAffine T] {R' : Type u} [CommRing R'] [IsDomain R'] {K' : Type u} [Field K']
    [Algebra R' K'] [IsFractionRing R' K'] (φ : Γ(T, ⊤) →+* R')
    (ψ : T.residueField (genericPoint T) →+* K')
    (hφψ : (algebraMap R' K').comp φ = ψ.comp (T.Γevaluation (genericPoint T)).hom)
    (h : (Spec.map (CommRingCat.ofHom φ) ≫ T.isoSpec.inv) (genericPoint (Spec (.of R'))) =
      genericPoint T) :
    ∃ e : K' ≃+* (Spec (.of R')).residueField (genericPoint (Spec (.of R'))),
      (e : K' →+* _).comp ψ = ((T.residueFieldCongr h.symm).hom ≫
        (Spec.map (CommRingCat.ofHom φ) ≫ T.isoSpec.inv).residueFieldMap
          (genericPoint (Spec (.of R')))).hom := by
  set S' := Spec (.of R')
  set η' := genericPoint S'
  set π := Spec.map (CommRingCat.ofHom φ) ≫ T.isoSpec.inv
  let := (S'.Γevaluation η').hom.toAlgebra
  have h₁ : IsFractionRing Γ(S', ⊤) (S'.residueField η') :=
    S'.isFractionRing_residueField_genericPoint
  let e₀ : R' ≃+* Γ(S', ⊤) := (Scheme.ΓSpecIso (.of R')).symm.commRingCatIsoToRingEquiv
  let : Algebra R' (S'.residueField η') := ((S'.Γevaluation η').hom.comp e₀.toRingHom).toAlgebra
  have h₂ : IsFractionRing R' (S'.residueField η') :=
    IsFractionRing.of_ringEquiv_left e₀ (fun _ ↦ rfl)
  let e : K' ≃ₐ[R'] S'.residueField η' := IsLocalization.algEquiv (nonZeroDivisors R') _ _
  refine ⟨e.toRingEquiv, ?_⟩
  let := (T.Γevaluation (genericPoint T)).hom.toAlgebra
  have hT : IsFractionRing Γ(T, ⊤) (T.residueField (genericPoint T)) :=
    T.isFractionRing_residueField_genericPoint
  have hinv : T.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(T, ⊤)).inv := by
    have h' := congr(Scheme.Hom.appTop $(T.isoSpec_inv_toSpecΓ))
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.Hom.id_appTop] at h'
    rw [← cancel_epi (Scheme.ΓSpecIso Γ(T, ⊤)).hom, h', Iso.hom_inv_id]
  have hπ : π.appTop = CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (.of R')).inv := by
    rw [Scheme.Hom.comp_appTop, hinv, ← cancel_mono (Scheme.ΓSpecIso (.of R')).hom,
      Category.assoc, Scheme.ΓSpecIso_naturality, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    exact Iso.inv_hom_id_assoc _ _
  -- both sides agree on `Γ(T, ⊤)`
  refine IsLocalization.ringHom_ext (nonZeroDivisors Γ(T, ⊤)) (RingHom.ext fun r ↦ ?_)
  have h3 : (π.appTop ≫ S'.Γevaluation η').hom r = ((T.residueFieldCongr h.symm).hom ≫
      π.residueFieldMap η').hom (T.Γevaluation (genericPoint T) r) := by
    rw [← Scheme.Γevaluation_naturality, ← Scheme.Γevaluation_residueFieldCongr_assoc T h.symm]
    rfl
  rw [hπ] at h3
  have h4 := congr($hφψ r)
  simp only [RingHom.comp_apply] at h4 ⊢
  rw [RingHom.algebraMap_toAlgebra, ← h3, ← h4]
  exact e.commutes (φ r)

end AlgebraicGeometry
