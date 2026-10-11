/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.TensorProduct.Quotient
public import WeilConjectures.RingTheory.ProEtale.ClosedLift

/-!
# Lifting maps into `H_A(C̄)` and the reduction pushout square

Let `A` be a ring and `C̄` an `A`-algebra, and let `H_A(C̄)` be the lift of
blueprint `def-exc-ind-etale-closed-lift` (`Algebra.ClosedLift`). This file proves two facts used
to lift objects and morphisms of the pro-étale site of a closed subscheme
(`lem-exc-closed-site-adjunction`):

* every `A`-algebra map `B ⟶ C̄` from an ind-étale `A`-algebra `B` factors through the map
  `H_A(C̄) ⟶ C̄` (`Algebra.ClosedLift.exists_toAlgHom_comp_eq`); this is the surjectivity half of
  the adjunction `lem-exc-closed-lift-adjunction`, and needs no filteredness;
* for an ind-étale `A ⧸ I`-algebra `C̄`, the square of rings
  `A ⟶ H_A(C̄)`, `A ⟶ A ⧸ I`, `H_A(C̄) ⟶ C̄`, `A ⧸ I ⟶ C̄` is a pushout
  (`Algebra.ClosedLift.isPushout_reduction`); this is a reformulation of the reduction
  isomorphism `lem-exc-closed-lift-reduction` (`Algebra.ClosedLift.bijective_reduction`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace Algebra.ClosedLift

variable {A : Type u} [CommRing A] {C : Type u} [CommRing C] [Algebra A C]

/-- An étale `A`-algebra `B` with an `A`-algebra map `φ : B ⟶ C̄` is isomorphic to an object of
the small indexing category `N_A(C̄)`, compatibly with the maps to `C̄`. -/
lemma exists_index_of_etale (B : Type u) [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (φ : B →ₐ[A] C) :
    ∃ (X : Index A C) (e : X.alg ≃ₐ[A] B), φ.comp e.toAlgHom = X.toC := by
  obtain ⟨n, f, hf, -⟩ := Algebra.FinitePresentation.out (R := A) (A := B)
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  have : Algebra.Etale A (MvPolynomial (Fin n) A ⧸ RingHom.ker f) :=
    Algebra.Etale.of_equiv e.symm
  exact ⟨⟨n, RingHom.ker f, this, φ.comp e.toAlgHom⟩, e, rfl⟩

/-- Every `A`-algebra map `φ : B ⟶ C̄` from an ind-étale `A`-algebra `B` factors through the map
`H_A(C̄) ⟶ C̄` of blueprint `def-exc-ind-etale-closed-lift`. Writing `B` as a filtered colimit of
étale algebras `B_i`, the maps `B_i ⟶ C̄` are objects of `N_A(C̄)`, and the colimit inclusions of
`H_A(C̄)` at these objects are compatible. -/
theorem exists_toAlgHom_comp_eq (B : Type u) [CommRing B] [Algebra A B] [Algebra.IndEtale A B]
    (φ : B →ₐ[A] C) : ∃ ψ : B →ₐ[A] ClosedLift A C, (toAlgHom A C).comp ψ = φ := by
  obtain ⟨ι, _, _, P, hP⟩ := Algebra.IndEtale.exists_colimitPresentation (R := A) (S := B)
  have key (i : ι) : ∃ (X : Index A C) (e : X.alg ≃ₐ[A] P.diag.obj i),
      (φ.comp (P.ι.app i).hom).comp e.toAlgHom = X.toC :=
    exists_index_of_etale _ _
  choose X e he using key
  let s : Cocone P.diag :=
    { pt := CommAlgCat.of A (ClosedLift A C)
      ι :=
        { app i := CommAlgCat.ofHom ((colimit.ι (diagram A C) (X i)).hom.comp
            (e i).symm.toAlgHom)
          naturality i j t := by
            let m : X i ⟶ X j :=
              ⟨((e j).symm.toAlgHom.comp (P.diag.map t).hom).comp (e i).toAlgHom, by
                rw [← he i, ← he j]
                have h := P.ι.naturality t
                simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h
                ext x
                simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
                rw [← h]
                rfl⟩
            have hw := colimit.w (diagram A C) m
            ext x
            have := congrArg (fun g ↦ (CommAlgCat.Hom.hom g) ((e i).symm x)) hw
            simp [diagram, m] at this
            exact this } }
  refine ⟨(P.isColimit.desc s).hom, ?_⟩
  have h : P.isColimit.desc s ≫ CommAlgCat.ofHom (toAlgHom A C) = CommAlgCat.ofHom φ := by
    refine P.isColimit.hom_ext fun i ↦ ?_
    rw [P.isColimit.fac_assoc]
    ext x
    have h1 := congrArg (fun g ↦ (CommAlgCat.Hom.hom g) ((e i).symm x))
      (colimit.ι_desc (coconeC A C) (X i))
    have h2 := DFunLike.congr_fun (he i) ((e i).symm x)
    simp only [AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.apply_symm_apply] at h2
    simpa [s, toAlgHom, coconeC, diagram, ← h2] using h1
  exact congrArg CommAlgCat.Hom.hom h

variable (A C) (I : Ideal A) [Algebra (A ⧸ I) C] [IsScalarTower A (A ⧸ I) C]

/-- For an ind-étale `A ⧸ I`-algebra `C̄`, the square of rings
```
A ──────→ H_A(C̄)
│            │
↓            ↓
A ⧸ I ────→ C̄
```
is a pushout: this is the reduction isomorphism `H_A(C̄) ⧸ I H_A(C̄) ≅ C̄` of blueprint
`lem-exc-closed-lift-reduction` (`Algebra.ClosedLift.bijective_reduction`), combined with
`H_A(C̄) ⊗_A (A ⧸ I) ≅ H_A(C̄) ⧸ I H_A(C̄)`. -/
theorem isPushout_reduction [Algebra.IndEtale (A ⧸ I) C] :
    CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap A (ClosedLift A C)))
      (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (toAlgHom A C).toRingHom) (CommRingCat.ofHom (algebraMap (A ⧸ I) C)) := by
  let : Algebra (ClosedLift A C) C := (toAlgHom A C).toRingHom.toAlgebra
  have : IsScalarTower A (ClosedLift A C) C :=
    IsScalarTower.of_algebraMap_eq fun a ↦ ((toAlgHom A C).commutes a).symm
  let red₀ : (ClosedLift A C ⧸ I.map (algebraMap A (ClosedLift A C))) →ₐ[ClosedLift A C] C :=
    Ideal.Quotient.liftₐ _ (Algebra.ofId _ _) fun x hx ↦
      map_le_ker_toAlgHom A C I hx
  have hred : (red₀ : _ → C) = reduction A C I := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  let red := AlgEquiv.ofBijective red₀ (by rw [hred]; exact bijective_reduction A C I)
  let e : ClosedLift A C ⊗[A] (A ⧸ I) ≃ₐ[ClosedLift A C] C :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (ClosedLift A C) I).symm.trans red
  have : Algebra.IsPushout A (ClosedLift A C) (A ⧸ I) C := by
    let := Algebra.TensorProduct.rightAlgebra (R := A) (A := ClosedLift A C) (B := A ⧸ I)
    refine Algebra.IsPushout.of_equiv (h := TensorProduct.isPushout) e ?_
    ext a
    change red (Submodule.Quotient.mk (a • 1)) = _
    rw [RingHom.comp_apply, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    change red₀ (Ideal.Quotient.mk _ (a • 1)) = _
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    simp [Algebra.smul_def, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A (A ⧸ I) C]
  exact (CommRingCat.isPushout_iff_isPushout (R := A) (R' := ClosedLift A C) (S := A ⧸ I)
    (S' := C)).2 this

end Algebra.ClosedLift
