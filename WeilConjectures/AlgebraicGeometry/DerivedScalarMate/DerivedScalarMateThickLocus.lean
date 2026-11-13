/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateData
import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateProjectionNormalization
import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateExactStructures
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators

/-! # The derived scalar mate and its thick isomorphism locus

The normalized comparison data are publicly reexported from DerivedScalarMateData.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.Scheme.DerivedScalarMate

private theorem retract_inverse {C D : Type*} [Category C] [Category D]
    {F H : C ⥤ D} (η : F ⟶ H) {K G : C}
    (i : K ⟶ G) (r : G ⟶ K) (hri : i ≫ r = 𝟙 K) [IsIso (η.app G)] :
    IsIso (η.app K) ∧
      H.map i ≫ inv (η.app G) ≫ F.map r ≫ η.app K = 𝟙 _ ∧
      η.app K ≫ H.map i ≫ inv (η.app G) ≫ F.map r = 𝟙 _ := by
  have hj : H.map i ≫ inv (η.app G) ≫ F.map r ≫ η.app K = 𝟙 _ := by
    rw [η.naturality]
    simp only [IsIso.inv_hom_id_assoc, ← H.map_comp, hri, H.map_id]
  have hk : η.app K ≫ H.map i ≫ inv (η.app G) ≫ F.map r = 𝟙 _ := by
    rw [← η.naturality_assoc]
    simp only [IsIso.hom_inv_id_assoc, ← F.map_comp, hri, F.map_id]
  exact ⟨⟨⟨H.map i ≫ inv (η.app G) ≫ F.map r, by
    simpa only [Category.assoc] using hk, by
    simpa only [Category.assoc] using hj⟩⟩, hj, hk⟩

/-- Restricting the canonical derived scalar mate gives exactly the normalized projection
arrow. Its restricted functors have the canonical transported exact structures; the
transformation preserves shifts and all three squares of distinguished triangles.
Its full isomorphism locus is thick, with the specified inverse on each split retract;
no idempotent-completion assumption is needed.

Source: Stacks 03EL, 06YY, 07A4, 07A6, 0G7E, 0FPT and 014A. -/
theorem derivedScalarMateThickLocus
    {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B)
    (t : ProEtaleTensorModel T A) (z : ProEtaleTensorModel Z (inverseRing f A)) :
    (∀ K : DerivedCategory (proEtaleRingModules Z (inverseRing f A)),
      (sourceIso f a t).inv.app K ≫
        (restriction a).mapDerivedCategory.map ((beta f a).app K) ≫
        (targetIso f a z).hom.app K =
      proEtaleProjectionFormulaMate f A (inverseRing f A) (Iso.refl _) t z K
        (DerivedCategory.Q.obj (coefficientComplex a))) ∧
    (∀ K : DerivedCategory (proEtaleRingModules Z (inverseRing f A)),
      (pull f B).map ((beta f a).app K) ≫
          (adjunction f B).counit.app ((proEtaleRingDerivedExtension (inverseMap f a)).obj K) =
        (scalarPullback f a).hom.app ((push f A).obj K) ≫
          (proEtaleRingDerivedExtension (inverseMap f a)).map
            ((adjunction f A).counit.app K)) ∧
    (∃ (_ : (Functor.curryObj t.tensor).CommShift₂Int)
        (_ : (Functor.curryObj z.tensor).CommShift₂Int)
        (_ : (push f A).CommShift ℤ)
        (_ : ((push f A ⋙ proEtaleRingDerivedExtension a) ⋙
          (restriction a).mapDerivedCategory).CommShift ℤ)
        (_ : ((proEtaleRingDerivedExtension (inverseMap f a) ⋙ push f B) ⋙
          (restriction a).mapDerivedCategory).CommShift ℤ),
      CanonicalTensorShifts t ∧ CanonicalTensorShifts z ∧
      (adjunction f A).CommShift ℤ ∧
      NatTrans.CommShift (sourceIso f a t).hom ℤ ∧
      NatTrans.CommShift (targetIso f a z).hom ℤ ∧
      ((push f A ⋙ proEtaleRingDerivedExtension a) ⋙
        (restriction a).mapDerivedCategory).IsTriangulated ∧
      ((proEtaleRingDerivedExtension (inverseMap f a) ⋙ push f B) ⋙
        (restriction a).mapDerivedCategory).IsTriangulated ∧
      NatTrans.CommShift (Functor.whiskerRight (beta f a)
        (restriction a).mapDerivedCategory) ℤ ∧
      ∀ E : Triangle (DerivedCategory (proEtaleRingModules Z (inverseRing f A))),
        E ∈ distTriang _ →
        ∃ m : (((push f A ⋙ proEtaleRingDerivedExtension a) ⋙
              (restriction a).mapDerivedCategory).mapTriangle.obj E) ⟶
            (((proEtaleRingDerivedExtension (inverseMap f a) ⋙ push f B) ⋙
              (restriction a).mapDerivedCategory).mapTriangle.obj E),
          m.hom₁ = (restriction a).mapDerivedCategory.map ((beta f a).app E.obj₁) ∧
          m.hom₂ = (restriction a).mapDerivedCategory.map ((beta f a).app E.obj₂) ∧
          m.hom₃ = (restriction a).mapDerivedCategory.map ((beta f a).app E.obj₃)) ∧
    (locus f a).IsTriangulated ∧ (locus f a).IsStableUnderRetracts ∧
    (∀ (n : ℕ) (K : Fin n → DerivedCategory (proEtaleRingModules Z (inverseRing f A))),
      (∀ i : Fin n, locus f a (K i)) → locus f a (biproduct K)) ∧
    (∀ (K G : DerivedCategory (proEtaleRingModules Z (inverseRing f A)))
      (i : K ⟶ G) (r : G ⟶ K) (_hri : i ≫ r = 𝟙 K)
      [IsIso ((beta f a).app G)],
      IsIso ((beta f a).app K) ∧
        (proEtaleRingDerivedExtension (inverseMap f a) ⋙ push f B).map i ≫
          inv ((beta f a).app G) ≫ (push f A ⋙ proEtaleRingDerivedExtension a).map r ≫
          (beta f a).app K = 𝟙 _ ∧
        (beta f a).app K ≫
          (proEtaleRingDerivedExtension (inverseMap f a) ⋙ push f B).map i ≫
          inv ((beta f a).app G) ≫ (push f A ⋙ proEtaleRingDerivedExtension a).map r = 𝟙 _) := by
  obtain ⟨ht, hz, hp, hF, hH, hct, hcz, hadj, hs, hd, heF, heH, hβ⟩ :=
    scalarMate_canonical_exact_structures f a t z
  let _ := ht
  let _ := hz
  let _ := hp
  let _ := hF
  let _ := hH
  let _ := heF
  let _ := heH
  let _ := hβ
  let R := (restriction a).mapDerivedCategory
  let η := Functor.whiskerRight (beta f a) R
  let _ : R.ReflectsIsomorphisms :=
    (proEtaleRingSheafChangeAdjunction f A B (inverseRing f A) (inverseRing f B)
      a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)).2.1
  have hlocus : locus f a = η.isoLocus := by
    funext K
    apply propext
    constructor
    · intro h
      let _ : IsIso ((beta f a).app K) := h
      exact inferInstanceAs (IsIso (R.map ((beta f a).app K)))
    · intro h
      let _ : IsIso (R.map ((beta f a).app K)) := h
      exact isIso_of_reflects_iso ((beta f a).app K) R
  have htri : (locus f a).IsTriangulated := by
    rw [hlocus]
    exact inferInstanceAs η.isoLocus.IsTriangulated
  let _ := htri
  have hclosed : (locus f a).IsClosedUnderIsomorphisms := by
    rw [hlocus]
    infer_instance
  let _ := hclosed
  refine ⟨scalarMate_projection_normalization f a t z, ?_, ?_, htri, ?_, ?_, ?_⟩
  · intro K
    exact mateEquiv_counit (adjunction f A) (adjunction f B) (scalarPullback f a).hom K
  · refine ⟨ht, hz, hp, hF, hH, hct, hcz, hadj, hs, hd, heF, heH, hβ, ?_⟩
    intro E _
    exact ⟨(NatTrans.mapTriangle η).app E, rfl, rfl, rfl⟩
  · rw [hlocus]
    infer_instance
  · intro n K hK
    exact (locus f a).prop_of_isLimit_fan (biproduct.isLimit K) hK
  · intro K G i r hri _
    exact retract_inverse (beta f a) i r hri

end AlgebraicGeometry.Scheme.DerivedScalarMate
