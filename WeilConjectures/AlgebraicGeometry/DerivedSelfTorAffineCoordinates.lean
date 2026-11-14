/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure

import WeilConjectures.AlgebraicGeometry.DerivedSelfTorChosenAffineCoordinates
import WeilConjectures.Algebra.Homology.QuotientTensorResolutionLiftHomotopy

/-! # Affine coordinates for intrinsic derived self-Tor

## References

* Stacks Project, Tags 08DX, 06YH, 01I9 and 00LS
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- A homology-coordinate identity for one augmented lift holds for every such lift. -/
private theorem quotient_tensor_coordinates_of_chosen
    {A C : Type u} [CommRing A] [CommRing C] {T : Type*}
    (I : Ideal A) (J : Ideal C) (φ : A →+* C)
    (hφ : I ≤ J.comap φ)
    (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)))
    (R : ProjectiveResolution (ModuleCat.of C (C ⧸ J))) (n : ℕ) :
    let TA := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)
    let TC := (tensorRight (ModuleCat.of C (C ⧸ J))).mapHomologicalComplex (.down ℕ)
    let F := (ModuleCat.restrictScalars φ).mapHomologicalComplex (.down ℕ)
    let ψ₀ := Ideal.quotientMap J φ hφ
    ∀ (f : (TA.obj P.complex).homology n → T)
      (g : (F.obj (TC.obj R.complex)).homology n → T),
      (∃ (a₀ : P.complex ⟶ F.obj R.complex)
        (k₀ : TA.obj P.complex ⟶ F.obj (TC.obj R.complex)),
        (∀ x : P.complex.X 0, R.π.f 0 (a₀.f 0 x) = ψ₀ (P.π.f 0 x)) ∧
        (∀ (j : ℕ) (x : P.complex.X j) (y : A ⧸ I),
          k₀.f j (x ⊗ₜ[A] y) = (show R.complex.X j from a₀.f j x) ⊗ₜ[C] (ψ₀ y)) ∧
        ∀ x, f x = g (HomologicalComplex.homologyMap k₀ n x)) →
      ∀ (ψ : (A ⧸ I) →+* (C ⧸ J))
        (a : P.complex ⟶ F.obj R.complex)
        (k : TA.obj P.complex ⟶ F.obj (TC.obj R.complex)),
        (∀ x : A, ψ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (φ x)) →
        (∀ x : P.complex.X 0, R.π.f 0 (a.f 0 x) = ψ (P.π.f 0 x)) →
        (∀ (j : ℕ) (x : P.complex.X j) (y : A ⧸ I),
          k.f j (x ⊗ₜ[A] y) = (show R.complex.X j from a.f j x) ⊗ₜ[C] (ψ y)) →
        ∀ x, f x = g (HomologicalComplex.homologyMap k n x) := by
  intro TA TC F ψ₀ f g hc ψ a k hψ ha hk
  rcases hc with ⟨a₀, k₀, ha₀, hk₀, hnat⟩
  have hψeq : ψ₀ = ψ := by
    apply RingHom.ext
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact (hψ x).symm
  rw [hψeq] at ha₀ hk₀
  rcases ModuleCat.quotient_tensor_resolution_lift_homotopy
    I J φ P R ψ a₀ a k₀ k hψ ha₀ ha hk₀ hk with ⟨H⟩
  intro x
  exact (hnat x).trans (congrArg g (ConcreteCategory.congr_hom (H.homologyMap_eq n) x))

set_option linter.unusedVariables false in
-- The nested hypotheses keep their documented names although the conclusion is nondependent.
/-- The intrinsic derived self-tensor of a closed-immersion quotient has normalized
projective-resolution coordinates on affine opens. The restriction equation holds
for any augmented quotient-resolution comparison, whose existence is not asserted here
(Stacks, Tags 08DX, 06YH, 01I9 and 00LS). -/
theorem exists_derived_selfTor_affine_coordinates
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] (n : ℕ) :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let D := DerivedCategory.Q.obj (S.obj B)
    let Q := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj (D ⊗ D)
    ∃ c : ∀ U : Y.affineOpens,
        ((((tensorRight (ModuleCat.of (Γ(Y, U.1) : Type u)
          ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U))).mapHomologicalComplex (.down ℕ)).obj
            (projectiveResolution (ModuleCat.of (Γ(Y, U.1) : Type u)
              ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U))).complex).homology n) ≃ₗ[Γ(Y, U.1)]
              Q.val.obj (op U.1),
      ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
        (_hbasic : ∃ f : Γ(Y, U.1), Y.basicOpen f = V.1),
          let A := (Γ(Y, U.1) : Type u)
          let C := (Γ(Y, V.1) : Type u)
          let I := i.ker.ideal U
          let J := i.ker.ideal V
          let φ := (Y.presheaf.map (homOfLE h).op).hom
          let P := projectiveResolution (ModuleCat.of A (A ⧸ I))
          let R := projectiveResolution (ModuleCat.of C (C ⧸ J))
          let TA := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex
            (.down ℕ)
          let TC := (tensorRight (ModuleCat.of C (C ⧸ J))).mapHomologicalComplex
            (.down ℕ)
          ∀ (ψ : (A ⧸ I) →+* (C ⧸ J))
            (a : P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
              (.down ℕ)).obj R.complex)
            (k : TA.obj P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
              (.down ℕ)).obj (TC.obj R.complex))
            (hψ : ∀ x : A, ψ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (φ x))
            (ha : ∀ x : P.complex.X 0, R.π.f 0 (a.f 0 x) = ψ (P.π.f 0 x))
            (hk : ∀ (j : ℕ) (x : P.complex.X j) (y : A ⧸ I),
              k.f j (x ⊗ₜ[A] y) = (show R.complex.X j from a.f j x) ⊗ₜ[C] (ψ y)),
            let e := ((TC.obj R.complex).sc n).mapHomologyIso
              (ModuleCat.restrictScalars φ)
          ∀ x, Q.val.map (homOfLE h).op (c U x) =
            c V (e.hom (HomologicalComplex.homologyMap k n x)) := by
  intro B S D Q
  rcases exists_derived_selfTor_chosen_affine_coordinates i n with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro V U h hbasic A C I J φ P R TA TC ψ a k hψ ha hk e x
  exact quotient_tensor_coordinates_of_chosen I J φ
    (fun x hx ↦ i.ker.ideal_le_comap_ideal h hx) P R n
    (fun x ↦ Q.val.map (homOfLE h).op (c U x)) (fun x ↦ c V (e.hom x))
    (hc V U h hbasic) ψ a k hψ ha hk x


end AlgebraicGeometry
