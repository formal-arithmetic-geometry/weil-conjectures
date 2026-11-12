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
Source: Stacks Project, Tags 08DX(2), 06YH, 01I9 and 00LS(1).
(blueprint: new-p1-derived-self-tor-affine-coordinates). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

set_option linter.unusedVariables false in
-- The nested hypotheses keep their documented names although the conclusion is nondependent.
set_option maxHeartbeats 800000 in
set_option profiler true in
-- Elaborating the two restricted tensor lifts needs additional heartbeats.
/-- The intrinsic derived self-tensor of a closed-immersion quotient has normalized
projective-resolution coordinates on affine opens. The restriction equation holds
for any augmented quotient-resolution comparison, whose existence is not asserted here.

Source: Stacks Project, Tags 08DX(2), 06YH, 01I9 and 00LS(1).
(blueprint: new-p1-derived-self-tor-affine-coordinates).

Proof: Restrict the intrinsic derived tensor to an affine U. The quotient section
map identifies the restricted coefficient with the associated sheaf of A/I, where
A = Gamma(U) and I is the kernel ideal. Sheafify the chosen projective resolution
P of A/I, including its quotient-normalized augmentation, and extend chain degree
j to cochain degree -j. Exactness of associated sheaf makes this a resolution.
Projective terms are flat, their associated sheaves are flat, and the extended
complex is nonpositive, hence K-flat. The derived tensor counit and the normalized
affine tensor comparison identify the intrinsic self-tensor with associated sheaf
of P tensor A/I, extended to nonpositive degrees. Exact associated sheaf commutes
with homology; extension identifies degree -n with chain degree n. Compose with
the associated-sheaf section unit to obtain the coordinate equivalence.

On a basic inclusion, a supplied augmented comparison a sheafifies to a morphism
of these resolutions. The augmentation equation makes its image in the derived
category the coefficient restriction map. The pure-tensor equation for k identifies
its associated-sheaf tensor morphism. Naturality of the derived tensor counit,
affine tensor comparison and exact homology comparison gives the restriction square.
Naturality of the section unit and restriction-of-scalars homology isomorphism turns
this square into the displayed element equation. Different augmented lifts induce
the same map: the comparison homotopy of projective resolutions tensors with the
quotient map, and homotopic chain maps act equally on homology. Zero quotients,
degree zero and empty basic opens use the same units and comparisons. -/
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
  obtain ⟨c, hc⟩ := exists_derived_selfTor_chosen_affine_coordinates i n
  refine ⟨c, ?_⟩
  intro V U h hbasic A C I J φ P R TA TC ψ a k hψ ha hk
  obtain ⟨a₀, k₀, ha₀, hk₀, hnat⟩ := hc V U h hbasic
  have hψeq : Ideal.quotientMap J φ
      (fun x hx ↦ i.ker.ideal_le_comap_ideal h hx) = ψ := by
    apply RingHom.ext
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact (hψ x).symm
  rw [hψeq] at ha₀ hk₀
  obtain ⟨H⟩ := ModuleCat.quotient_tensor_resolution_lift_homotopy
    I J φ P R ψ a₀ a k₀ k hψ ha₀ ha hk₀ hk
  have heq := H.homologyMap_eq n
  intro e x
  simpa only [heq] using hnat x


end AlgebraicGeometry
