/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientModelExtensionIso

/-! # Scalar reduction of two supplied constant quotient models

Source: Stacks Project, Tag 09C6, consecutive quotient balancing.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

/-- Two constant models of consecutive actual tower levels on one nonempty etale
chart admit an algebraic universal reduction arrow. No lissity, etale descent, or
covering construction is part of this assertion.

Source: Stacks Project, proetale.tex, Tag 09C6, the consecutive balancing isomorphism;
Tags 0D6D and 03Q3 for scalar transitivity and constant geometric stalks. -/
theorem constantAdicQuotient_model_reduction
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower X d) (n : ℕ) (W : Y.Etale) (_w : W.left)
    (E' : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1 + 1))))
    (E : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
    (e' : Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d (n + 1)).obj E' ≅
      (adicTowerPullback (W.hom ≫ g)
        ((pbcAdicRings X d).obj (op (n + 1)))).obj (M.level (n + 1))))
    (e : Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ≅
      (adicTowerPullback (W.hom ≫ g)
        ((pbcAdicRings X d).obj (op n))).obj (M.level n))) :
    ∃ t : E' ⟶
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (I := d.ideal.map
          (algebraMap A (AdicCompletion d.ideal A)))
          (Nat.le_succ (n + 1))))).mapDerivedCategory.obj E,
      ∀ N : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
        (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))),
        Function.Bijective (fun k : E ⟶ N ↦ t ≫
          (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.factor
            (Ideal.pow_le_pow_right (I := d.ideal.map
              (algebraMap A (AdicCompletion d.ideal A)))
              (Nat.le_succ (n + 1))))).mapDerivedCategory.map k) := by
  let q := Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (I := d.ideal.map
      (algebraMap A (AdicCompletion d.ideal A))) (Nat.le_succ (n + 1)))
  let adj := CategoryTheory.ConstantScalarRealization.moduleDerivedAdjunction q
  obtain ⟨i⟩ := constantAdicQuotient_model_extension_iso X Y g d M n W _w E' E e' e
  let t : E' ⟶ (ModuleCat.restrictScalars q).mapDerivedCategory.obj E :=
    (adj.homEquiv E' E) i.hom
  refine ⟨t, ?_⟩
  intro N
  have hJ : Function.Bijective (fun k : E ⟶ N ↦ i.hom ≫ k) := by
    refine ⟨?_, ?_⟩
    · intro k l h
      have h' := congrArg (fun z ↦ i.inv ≫ z) h
      simpa using h'
    · intro h
      refine ⟨i.inv ≫ h, ?_⟩
      simp
  have hh := (adj.homEquiv E' N).bijective.comp hJ
  have he : (fun k : E ⟶ N ↦ t ≫ (ModuleCat.restrictScalars q).mapDerivedCategory.map k) =
      (adj.homEquiv E' N) ∘ (fun k ↦ i.hom ≫ k) := by
    funext k
    exact (adj.homEquiv_naturality_right i.hom k).symm
  rw [he]
  exact hh

end AlgebraicGeometry.Scheme
