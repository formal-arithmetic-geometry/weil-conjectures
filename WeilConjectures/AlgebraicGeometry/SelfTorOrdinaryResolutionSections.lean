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
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

import WeilConjectures.AlgebraicGeometry.SelfTorOrdinaryLocalizedComparisons
import WeilConjectures.Algebra.Homology.QuotientTensorResolutionLiftHomotopy

/-! # Affine sections of ordinary tensor with a K-flat quotient resolution

## References

* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 06YG](https://stacks.math.columbia.edu/tag/06YG)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 00LS](https://stacks.math.columbia.edu/tag/00LS)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- Affine tensor-resolution homology computes the sections of the ordinary total tensor
with a global K-flat resolution. This is a statement entirely about complexes and homology;
no derived tensor or existence of algebraic resolution lifts occurs in its conclusion. -/
theorem exists_selfTor_ordinary_resolution_sections
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    (hK : CochainComplex.IsKFlatTensor (R := Y.sheaf) K) (hq : QuasiIso q) (n : ℕ) :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let Q := (CochainComplex.mapBifunctor K (S.obj B)
      (curriedTensor (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))).homology
        (-(n : ℤ))
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
              (.down ℕ)).obj (TC.obj R.complex)),
            (∀ x : A, ψ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (φ x)) →
            (∀ x : P.complex.X 0, R.π.f 0 (a.f 0 x) = ψ (P.π.f 0 x)) →
            (∀ (j : ℕ) (x : P.complex.X j) (y : A ⧸ I),
              k.f j (x ⊗ₜ[A] y) = (show R.complex.X j from a.f j x) ⊗ₜ[C] (ψ y)) →
            let e := ((TC.obj R.complex).sc n).mapHomologyIso
              (ModuleCat.restrictScalars φ)
          ∀ x, Q.val.map (homOfLE h).op (c U x) =
            c V (e.hom (HomologicalComplex.homologyMap k n x)) := by
  intro B S Q
  obtain ⟨c, hc⟩ := exists_selfTor_ordinary_localized_comparisons i K q hK hq n
  refine ⟨c, ?_⟩
  intro V U h hbasic A C I J φ P R TA TC ψ a k hψ ha hk
  obtain ⟨ψ₀, a₀, k₀, hlift⟩ := hc V U h hbasic
  have hψeq : ψ₀ = ψ := by
    apply RingHom.ext
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact (hlift.1 x).trans (hψ x).symm
  subst ψ₀
  obtain ⟨H⟩ := ModuleCat.quotient_tensor_resolution_lift_homotopy
    I J φ P R ψ a₀ a k₀ k hψ hlift.2.1 ha hlift.2.2.1 hk
  have heq := H.homologyMap_eq n
  intro e x
  exact (hlift.2.2.2 x).trans
    (congrArg (fun y ↦ c V (e.hom y)) (ConcreteCategory.congr_hom heq x))


end AlgebraicGeometry
