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

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

import Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison

/-! # Ambient affine self-Tor comparison

Source: Stacks Project, Tags 08DX, 06YG and 00LS.
(blueprint: lem-pc-self-tor-ambient-resolution-charts). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- The affine quotient tensor resolutions compute the ambient homology sheaf,
before any pullback to the closed subscheme.
Source: Stacks Project, Tag 08DX(2), Tag 06YG, and Tag 00LS.
(blueprint: lem-pc-self-tor-ambient-resolution-charts).

Proof: Identify the restriction of the pushforward structure sheaf on each
chart with the associated quotient module. Sheafify the chosen projective
resolution and its augmentation. Its terms are flat because projective modules
are retracts of free modules, and the nonpositive extension is K-flat by the
bounded-above flat criterion. The affine derived tensor formula of 08DX(2)
therefore identifies its quotient tensor complex with the restriction of the
fixed derived tensor on Y. Exactness of tilde commutes with homology; compose
this identification with isoLeftDerivedObj to construct t on the chart.
For a basic inclusion, sheafify the supplied a and k. The augmentation equation
identifies their maps on the quotient sheaf, while the pure tensor equation
identifies the tensor map. The resulting derived tensor square commutes before
homology: invert the augmentation quasi-isomorphisms and use 06YG to compare
K-flat models. Taking homology and the exact restriction-of-scalars comparison
gives precisely q. Naturality of the tilde unit and chart restriction isomorphism
gives the displayed section equation. No assertion about pullback occurs here.
Degree zero, zero quotient rings, and empty basic opens use the same exact
functors and augmentation comparisons, so require no extra assumptions. -/
theorem exists_selfTor_ambient_resolution_charts
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
    let T := fun U : Y.affineOpens ↦
      tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
        Scheme.Modules.pushforward U.1.ι
    let s := fun (U : Y.affineOpens)
      (M : ModuleCat.{u} (Γ(Y, U.1) : Type u)) (x : M) ↦
        let L := (tilde.functor Γ(Y, U.1)).obj M
        (Scheme.Modules.restrictAppIso U.2.isoSpec.hom L
          (U.1.ι ⁻¹ᵁ U.1)).inv
          (L.val.map (homOfLE le_top).op ((tilde.adjunction.unit.app M) x))
    ∃ t : ∀ U : Y.affineOpens,
        ((T U).obj _).over (U.1) ≅ Q.over (U.1),
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
          ∀ x,
            (t U).hom.val.app (op (Over.mk (homOfLE (h))))
                (((T U).obj _).val.map (homOfLE (h)).op
                  (s U _ x)) =
              (t V).hom.val.app (op (Over.mk (𝟙 (V.1))))
                (s V _ (q x)) := by sorry

end AlgebraicGeometry
