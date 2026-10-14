/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

import Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import Sheaf.AlgebraicGeometry.Modules.IsKFlatRestriction
import Sheaf.AlgebraicGeometry.AffineChartTotalTensor
import Sheaf.AlgebraicGeometry.OpenKFlatTensorHomologyComparison
import Sheaf.AlgebraicGeometry.QuotientResolutionTensorComparison

/-! # Chosen-lift affine sections of ordinary tensor

Source: Stacks Project, Tags 08DX(2), 06YG, 06YB, 01I9 and 00LS.
(blueprint: new-h3-self-tor-ordinary-localized-comparisons). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- The ordinary affine tensor comparison is compatible with one augmented algebraic
comparison for each basic inclusion. Independence of the supplied comparison is not
part of this statement.

Source: Stacks Project, Tag 08DX(2), affine calculation, Tags 06YG and 06YB for
K-flat comparison, Tag 01I9 for affine sections, and Tag 00LS(1) for existence of lifts.
(blueprint: new-h3-self-tor-ordinary-localized-comparisons).

Proof: For each affine U, write A = Γ(Y,U), I = ker(i)(U), B = i_*O_Z.
Identify B restricted to U with tilde(A/I) by the quotient presentation of the
closed immersion. Sheafify the chosen projective resolution P_U and its augmentation,
then extend from chain degree j to cochain degree -j. Exactness of tilde makes the
augmentation a quasi-isomorphism. Projective terms give flat associated sheaves;
bounded-above flat complexes are K-flat. Restriction preserves K-flatness of K.
Compare K|U tensor B|U[0] with P_U~ tensor B|U[0] by the augmented zigzag
K|U tensor B|U[0] <- K|U tensor P_U~ -> B|U[0] tensor P_U~
-> P_U~ tensor B|U[0], the last arrow being braiding. K-flat tensor invariance
makes the first two arrows quasi-isomorphisms. The affine total tensor comparison,
exact tilde homology comparison, extension homology in degree -n, and the tilde
section unit give c_U. These are homology isomorphisms; no chain inverse is used.

For a basic inclusion V in U, ideal restriction gives the quotient homomorphism
psi. Choose an augmented comparison a from P_U to the restricted P_V by projective
lifting through the exact augmented resolution; tensor a with psi to obtain k.
On the associated sheaf complexes, the augmentation square commutes: this follows
from its equality on affine sections and full faithfulness of tilde. The pure
tensor formula identifies the associated k with tensor of a and the quotient map.
Restrict the U zigzag to V and compare it with the V zigzag using this square.
Tensor functoriality and naturality of braiding give commuting squares. Homology
and inversion of the quasi-isomorphism legs give the section equality for these
chosen a and k. Exact restriction of scalars supplies the displayed homology iso.
Naturality of the affine section unit completes the comparison. No assertion
about other lifts is needed here. Zero rings, I = top, n = 0 and empty basic opens
are covered by the same constructions and zero modules. -/
theorem exists_selfTor_ordinary_localized_comparisons
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    (hK : CochainComplex.IsKFlat (R := Y.sheaf) K) (hq : QuasiIso q) (n : ℕ) :
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
