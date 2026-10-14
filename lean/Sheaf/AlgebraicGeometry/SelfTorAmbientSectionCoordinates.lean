/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

import Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison

/-! # Ambient self-Tor coordinates on affine sections

Source: Stacks Project, Tags 08DX(2), 06YG and 00LS.
(blueprint: new-a3-self-tor-ambient-section-coordinates). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- Algebraic self-Tor gives linear coordinates on the affine sections of the
ambient tensor homology, compatible with augmented resolution comparisons.
Source: Stacks Project, Tag 08DX(2), Tag 06YG and Tag 00LS.
(blueprint: new-a3-self-tor-ambient-section-coordinates).

Proof: On U = Spec A, identify the closed structure sheaf with tilde(A/I).
Sheafify the chosen projective resolution of A/I and its augmentation using
lem-sc-affine-quotient-resolution-sheafification. Projective terms are flat;
extend into nonpositive degrees and apply lem-pc-bounded-above-flat-kflat.
The natural affine derived tensor comparison of
lem-pc-affine-derived-pullback-tensor-tilde computes the restricted ambient
self-tensor as tilde of that resolution tensored with A/I. Exactness of tilde
identifies its negative-n homology with tilde of the chain homology in degree n.
Apply affine sections and the tilde adjunction unit, then compose with
ProjectiveResolution.isoLeftDerivedObj to obtain the linear equivalence c U.
This constructs section coordinates only, not a sheaf isomorphism on the
category of opens below U.

For a basic inclusion V in U, localize the resolution. Localization is exact
and preserves projectives. The quotient ring equation identifies the induced
map of the closed structure sheaves. The augmentation equation makes a a lift
of that map, and the pure tensor equation identifies k with the tensor lift.
Compare the localized resolution with the chosen resolution over C: the lifts
of the same augmentation are homotopic by the projective comparison argument
of 00LS, which holds for projectives by the lifting property. Tensoring carries
this homotopy to the corresponding tensor complexes. Thus their homology maps
agree. The natural K-flat comparison of
lem-pc-kflat-derived-tensor-comparison makes this the restriction map of the
ambient tensor, before any pullback to Z. Exact restriction of scalars gives
mapHomologyIso, and conjugating by isoLeftDerivedObj yields precisely q.
Naturality of the affine section unit gives the displayed equation.
The same constructions apply for n = 0, I = top, and empty basic opens;
zero rings and zero section modules require no additional hypotheses. -/
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
          ∀ x, Q.val.map (homOfLE h).op (c U x) = c V (q x) := by sorry

end AlgebraicGeometry
