/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

import WeilConjectures.AlgebraicGeometry.SelfTorAmbientLocalizedComparisons
import WeilConjectures.Algebra.Homology.QuotientTensorResolutionLiftHomotopy

/-! # Ambient self-Tor coordinates on affine sections

## References

* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 06YG](https://stacks.math.columbia.edu/tag/06YG)
* [Stacks Project, Tag 00LS](https://stacks.math.columbia.edu/tag/00LS)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- Algebraic self-Tor gives linear coordinates on the affine sections of the
ambient tensor homology, compatible with augmented resolution comparisons. -/
theorem exists_selfTor_ambient_section_coordinates
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let Q :=
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
          (S.obj B ⊗ S.obj B))
    ∃ c : ∀ U : Y.affineOpens,
        ((tensorRight (ModuleCat.of (Γ(Y, U.1) : Type u)
          ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U))).leftDerived n).obj
          (ModuleCat.of (Γ(Y, U.1) : Type u)
            ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U)) ≃ₗ[Γ(Y, U.1)]
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
              (.down ℕ)).obj (TC.obj R.complex)),
            (∀ x : A, ψ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (φ x)) →
            (∀ x : P.complex.X 0, R.π.f 0 (a.f 0 x) = ψ (P.π.f 0 x)) →
            (∀ (j : ℕ) (x : P.complex.X j) (y : A ⧸ I),
              k.f j (x ⊗ₜ[A] y) = (show R.complex.X j from a.f j x) ⊗ₜ[C] (ψ y)) →
            let e := ((TC.obj R.complex).sc n).mapHomologyIso
              (ModuleCat.restrictScalars φ)
            let q := fun x ↦
              (R.isoLeftDerivedObj (tensorRight (ModuleCat.of C (C ⧸ J))) n).inv
                (e.hom (HomologicalComplex.homologyMap k n
                  ((P.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).hom x)))
          ∀ x, Q.val.map (homOfLE h).op (c U x) = c V (q x) := by
  intro B S Q
  obtain ⟨d, hc⟩ := exists_selfTor_ambient_localized_comparisons.{u, w} i n
  let c := fun U : Y.affineOpens ↦
    ((projectiveResolution (ModuleCat.of (Γ(Y, U.1) : Type u)
      ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U))).isoLeftDerivedObj
        (tensorRight (ModuleCat.of (Γ(Y, U.1) : Type u)
          ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U))) n).toLinearEquiv.trans (d U)
  refine ⟨c, ?_⟩
  intro V U h hbasic A C I J φ P R TA TC ψ a k hψ ha hk
  obtain ⟨ψ₀, a₀, k₀, hψ₀, ha₀, hk₀, hc₀⟩ := hc V U h hbasic
  have hψeq : ψ₀ = ψ := by
    apply RingHom.ext
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact (hψ₀ x).trans (hψ x).symm
  subst ψ₀
  obtain ⟨H⟩ := ModuleCat.quotient_tensor_resolution_lift_homotopy
    (i.ker.ideal U) (i.ker.ideal V) (Y.presheaf.map (homOfLE h).op).hom
    (projectiveResolution _) (projectiveResolution _) ψ a₀ a k₀ k hψ ha₀ ha hk₀ hk
  have heq := H.homologyMap_eq n
  intro e q x
  have hnat := hc₀ ((P.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).hom x)
  simp only [c]
  change _ = d V
    ((R.isoLeftDerivedObj (tensorRight (ModuleCat.of C (C ⧸ J))) n).hom
      ((R.isoLeftDerivedObj (tensorRight (ModuleCat.of C (C ⧸ J))) n).inv
        (e.hom (HomologicalComplex.homologyMap k n
          ((P.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).hom x)))))
  rw [Iso.inv_hom_id_apply]
  simpa only [heq] using! hnat

end AlgebraicGeometry
