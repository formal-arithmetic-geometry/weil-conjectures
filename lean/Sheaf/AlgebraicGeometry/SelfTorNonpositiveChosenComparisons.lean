/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

import Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import Sheaf.AlgebraicGeometry.Modules.IsKFlatRestriction
import Sheaf.AlgebraicGeometry.AffineChartTotalTensor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

import Sheaf.AlgebraicGeometry.QuotientResolutionTensorComparison

/-! # Chosen affine comparison for nonpositive flat resolutions
Source: Stacks Project, Tags 08DX(2), 06YG, 06YB, 01I9, and 00LS(1).
(blueprint: new-h3-self-tor-nonpositive-chosen-comparisons). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- Nonpositive flat resolutions have affine coordinates compatible with one
augmented quotient-resolution lift on each basic inclusion. Compatibility with
arbitrary supplied lifts is a separate algebraic homotopy argument.

Source: Stacks Project, Tags 08DX(2), 06YG, 06YB, 01I9, and 00LS(1).
(blueprint: new-h3-self-tor-nonpositive-chosen-comparisons).

Proof: On an affine U, put A = Gamma(U), I = ker(i)(U), and B = i_*O_Z.
The closed-immersion quotient presentation identifies B restricted to U with
 tilde(A/I), normalized by the quotient section map. Sheafify the chosen
projective resolution P_U of A/I and its augmentation; exactness of tilde gives
an augmented resolution. Extend chain degree j to cochain degree -j, obtaining
p_U : L_U -> B|U[0]. Projective module terms are flat, and associated sheaf
terms are flat. Both L_U and K|U are bounded above and termwise flat, so are
K-flat. The zigzag
K|U tensor B|U[0] <- K|U tensor L_U -> B|U[0] tensor L_U
-> L_U tensor B|U[0]
uses id tensor p_U, q|U tensor id, and braiding. The first two arrows are
quasi-isomorphisms: their mapping cones are tensors of an acyclic augmentation
cone with a K-flat complex. Take homology and invert those two homology maps.
The affine total-tensor comparison, exact tilde homology comparison, extension
homology in degree -n, and normalized tilde section unit give c_U. Choose this
normalization on every chart, rather than unrelated pointwise isomorphisms.

On a basic inclusion V in U, restriction carries I_U into I_V, giving psi.
Projectivity of the source resolution and exactness of the restricted target
resolution lift the augmentation to a chain map a. Tensor degreewise with psi
to obtain k; this gives the three displayed quotient, augmentation, and pure
tensor equations. Via the tilde adjunction, a gives a map of the sheafified
resolutions on V. Its augmentation square commutes, since it does so on affine
sections and tilde is fully faithful. The pure tensor equation identifies its
tensor map with k. Restrict the U zigzag to V and compare it with the V zigzag.
Tensor functoriality and naturality of braiding make every square commute.
Taking homology and cancelling the invertible legs makes the normalized
coordinate maps commute. Naturality of the tilde section unit and the exact
restriction-of-scalars homology comparison give the displayed element equation
for this chosen lift. No independence from other augmented lifts is claimed.
For degree zero the augmentation calculation is unchanged; for I = top and
empty charts the relevant quotient modules vanish and the same maps apply. -/
theorem exists_selfTor_nonpositive_chosen_comparisons
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    (hbounded : ∀ j : ℤ, 0 < j → IsZero (K.X j))
    (hflat : ∀ j : ℤ, SheafOfModules.IsFlat (K.X j)) (hq : QuasiIso q) (n : ℕ) :
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
          ∃ (ψ : (A ⧸ I) →+* (C ⧸ J))
            (a : P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
              (.down ℕ)).obj R.complex)
            (k : TA.obj P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
              (.down ℕ)).obj (TC.obj R.complex)),
            (∀ x : A, ψ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (φ x)) ∧
            (∀ x : P.complex.X 0, R.π.f 0 (a.f 0 x) = ψ (P.π.f 0 x)) ∧
            (∀ (j : ℕ) (x : P.complex.X j) (y : A ⧸ I),
              k.f j (x ⊗ₜ[A] y) = (show R.complex.X j from a.f j x) ⊗ₜ[C] (ψ y)) ∧
            let e := ((TC.obj R.complex).sc n).mapHomologyIso
              (ModuleCat.restrictScalars φ)
          ∀ x, Q.val.map (homOfLE h).op (c U x) =
            c V (e.hom (HomologicalComplex.homologyMap k n x)) := by sorry

end AlgebraicGeometry
