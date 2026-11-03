/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalar

/-! # Identity maps of concrete coefficient presentations -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport

private def scalarIsoOfTopologicalEquiv {A B : Type} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (hi : Continuous e.symm) :
    scalarSixTopologicalRing.{u} A ≅ scalarSixTopologicalRing B where
  hom := scalarSixContinuousMap e.toRingHom he
  inv := scalarSixContinuousMap e.symm.toRingHom hi
  hom_inv_id := by
    apply CommMon.hom_ext
    apply Sheaf.hom_ext
    ext S a
    apply ULift.ext
    apply ContinuousMap.ext
    intro s
    exact e.symm_apply_apply (a.down s)
  inv_hom_id := by
    apply CommMon.hom_ext
    apply Sheaf.hom_ext
    ext S a
    apply ULift.ext
    apply ContinuousMap.ext
    intro s
    exact e.apply_symm_apply (a.down s)

private def bottomField (ell : ℕ) [Fact ell.Prime] :
    PadicAlgCl.FiniteIntermediateField ell :=
  ⟨⊥, inferInstance⟩

private def bottomEquiv (ell : ℕ) [Fact ell.Prime] :
    ℚ_[ell] ≃+* bottomField ell :=
  (IntermediateField.botEquiv ℚ_[ell] (PadicAlgCl ell)).symm.toRingEquiv

private theorem bottomEquiv_isometry (ell : ℕ) [Fact ell.Prime] :
    Isometry (bottomEquiv ell) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  change ‖algebraMap (bottomField ell) (PadicAlgCl ell)
      (algebraMap ℚ_[ell] (bottomField ell) x)‖ = ‖x‖
  rw [← IsScalarTower.algebraMap_apply, PadicAlgCl.norm_extends]

private def bottomIntegersEquiv (ell : ℕ) [Fact ell.Prime] :
    ℤ_[ell] ≃+* PadicAlgCl.integers ell (bottomField ell) :=
  RingEquiv.ofBijective (padicIntToIntegers ell (bottomField ell)) (by
    constructor
    · intro x y h
      apply Subtype.ext
      exact (bottomEquiv ell).injective (congrArg Subtype.val h)
    · intro x
      have hx : ‖(bottomEquiv ell).symm x.val‖ ≤ 1 := by
        have h := x.property
        rw [PadicAlgCl.mem_integers_iff] at h
        have he : algebraMap (bottomField ell) (PadicAlgCl ell) x.val =
            algebraMap ℚ_[ell] (PadicAlgCl ell) ((bottomEquiv ell).symm x.val) := by
          rw [IsScalarTower.algebraMap_apply ℚ_[ell] (bottomField ell) (PadicAlgCl ell)]
          exact congrArg (algebraMap (bottomField ell) (PadicAlgCl ell))
            ((bottomEquiv ell).apply_symm_apply x.val).symm
        rw [he] at h
        have h' : ‖algebraMap ℚ_[ell] (PadicAlgCl ell)
            ((bottomEquiv ell).symm x.val)‖ ≤ 1 := by exact_mod_cast h
        rwa [PadicAlgCl.norm_extends] at h'
      refine ⟨⟨(bottomEquiv ell).symm x.val, hx⟩, ?_⟩
      apply Subtype.ext
      exact (bottomEquiv ell).apply_symm_apply x.val)

private theorem bottomIntegersEquiv_isometry (ell : ℕ) [Fact ell.Prime] :
    Isometry (bottomIntegersEquiv ell) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  exact (bottomEquiv_isometry ell).norm_map_of_map_zero (map_zero _) (x : ℚ_[ell])

/-- Every non-closure concrete coefficient presentation has a listed identity.
Source: the isomorphism-of-presentations convention for coefficient change
(blueprint: lem-pur-coefficient-presentation-identities).
Proof: finite, integral and field identities are primitive listed maps. The bottom
finite subextension is isometrically isomorphic to Q_ell; restricting this equivalence
to norm-at-most-one elements gives the corresponding isometry on Z_ell. Postcomposition
on continuous functions gives coefficient-ring isomorphisms. Transport the primitive
bottom integral and field identity maps along these isomorphisms. Only the separate
closure constructor remains, and its identity is covered by the scalar identity law. -/
theorem coefficient_identity_listed_or_closure (ell : ℕ) [Fact ell.Prime]
    (c : Coefficient ell) :
    IsListedScalarCoefficientMap ell (𝟙 (c.bundled.{u} ell)) ∨ c = .closure := by
  cases c with
  | finite A fin n hA =>
      let : TopologicalSpace A := ⊥
      let : DiscreteTopology A := discreteTopology_bot A
      exact Or.inl (.finite (n + 1) (n + 1) hA hA (RingHom.id A) continuous_id)
  | integral E =>
      left
      convert IsListedScalarCoefficientMap.integral (le_refl E) using 1 <;> rfl
  | rational E => exact Or.inl (.field (le_refl E))
  | closure => exact Or.inr rfl
  | rationals =>
      left
      let i : ℚ_[ell] ≃ᵢ bottomField ell :=
        ⟨(bottomEquiv ell).toEquiv, bottomEquiv_isometry ell⟩
      let e := scalarIsoOfTopologicalEquiv.{u} (bottomEquiv ell)
        i.continuous i.symm.continuous
      have hid : IsListedScalarCoefficientMap ell
          (𝟙 ((Coefficient.rational (bottomField ell)).bundled.{u} ell)) :=
        .field (le_refl (bottomField ell))
      have h : IsListedScalarCoefficientMap ell (e.hom ≫ 𝟙 _ ≫ e.inv) :=
        IsListedScalarCoefficientMap.iso e e.symm hid
      rw [Category.id_comp, e.hom_inv_id] at h
      exact h
  | integers =>
      left
      let i : ℤ_[ell] ≃ᵢ PadicAlgCl.integers ell (bottomField ell) :=
        ⟨(bottomIntegersEquiv ell).toEquiv, bottomIntegersEquiv_isometry ell⟩
      let e := scalarIsoOfTopologicalEquiv.{u} (bottomIntegersEquiv ell)
        i.continuous i.symm.continuous
      have hid : IsListedScalarCoefficientMap ell
          (𝟙 ((Coefficient.integral (bottomField ell)).bundled.{u} ell)) := by
        convert IsListedScalarCoefficientMap.integral (le_refl (bottomField ell)) using 1 <;> rfl
      have h : IsListedScalarCoefficientMap ell (e.hom ≫ 𝟙 _ ≫ e.inv) :=
        IsListedScalarCoefficientMap.iso e e.symm hid
      rw [Category.id_comp, e.hom_inv_id] at h
      exact h

/-- An equality of native coefficient rings is a listed presentation change,
except when both coefficient indices are the single closure index.
Source: the isomorphism-of-presentations convention
(blueprint: lem-pur-coefficient-presentation-identities).
Proof: if either coefficient is not the closure, its identity is listed by the
preceding theorem. Transport that identity along the given equality of rings,
on the target or on the source as appropriate. If neither identity certificate
is obtained, the two coefficients both equal the unique closure constructor. -/
theorem coefficient_eqToHom_listed_or_closure (ell : ℕ) [Fact ell.Prime]
    (c c' : Coefficient ell) (h : c.bundled.{u} ell = c'.bundled ell) :
    IsListedScalarCoefficientMap ell (eqToHom h) ∨ (c = .closure ∧ c' = .closure) := by
  rcases coefficient_identity_listed_or_closure ell c with hid | hc
  · left
    simpa [Iso.refl_hom] using
      IsListedScalarCoefficientMap.iso (Iso.refl _) (eqToIso h) hid
  · rcases coefficient_identity_listed_or_closure ell c' with hid | hc'
    · left
      simpa [Iso.refl_hom] using
        IsListedScalarCoefficientMap.iso (eqToIso h) (Iso.refl _) hid
    · exact Or.inr ⟨hc, hc'⟩

end AlgebraicGeometry.ProEtale.PurityTransport
