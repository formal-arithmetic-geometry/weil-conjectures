/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q112
-/
module

public import Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient
public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import Sheaf.AlgebraicGeometry.NormalScheme
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Sheaf.AlgebraicGeometry.ClosedDominantDimension
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.AlgebraicGeometry.AlterationCoverCalculus
import Sheaf.AlgebraicGeometry.EquivariantMarkedNodalAlteration
import Sheaf.AlgebraicGeometry.FreeFiniteActionTorsor
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.AlgebraicGeometry.NodalQuotientNormalizedBaseRefinement
import Sheaf.AlgebraicGeometry.PrimeToEllMarkedAlgebraization
import Sheaf.AlgebraicGeometry.ProperGenericCurvePreparation
import Sheaf.AlgebraicGeometry.RegularPairAlterationPullback
import Sheaf.AlgebraicGeometry.UniformizationCompleteLocalDescent
import WeilConjectures.AlgebraicGeometry.Regular

/-!
# Reduction of prime-to-ell uniformization to marked nodal quotients

Source: ILO, Travaux de Gabber, Expose IX, 1.3--1.4, pp. 132--133; III Proposition
6.2, pp. 43--45; V 3.1.3--3.1.4, p. 66
(blueprint: lem-per-uniformization-nodal-quotient-reduction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Resolution of every marked nodal quotient model in situation (*) implies prime-to-ell
uniformization for all reduced quasi-excellent Noetherian schemes. The torsor is identified
with the actual inverse-image open, and its action is the restriction of the base action.
The function-field algebra is required to be the one induced by `b`, and the normalization
is over `Y`. Birationality uses dense opens, and boundary equalities are exact supports.

Source: ILO, Expose IX, 1.3--1.4, pp. 132--133; III 6.2; V 3.1.3--3.1.4
(blueprint: lem-per-uniformization-nodal-quotient-reduction).

Proof plan, following the node:
1. Use lem-per-uniformization-complete-local-descent in its bounded form and strong
   induction on dimension. Noetherian complete local rings have finite Krull dimension
   (lem-weil-pbc-noetherian-local-finite-krull-dimension); its unbounded form handles S.
2. Dimensions zero and one are fields and DVRs (lem-sc-normal-dim1-dvr). The identity
   covers, with empty boundary or the uniformizer boundary, by alteration-cover calculus.
3. Apply lem-per-prime-to-ell-marked-algebraization and pull back regular pairs by
   lem-per-regular-pair-alteration-pullback. Compose the prime-to-ell finite cover.
4. Apply lem-per-proper-generic-curve-preparation, compactify and prepare the Cartier
   marking. Restrict to its open over the original scheme and compose covering families.
5. Use lem-per-equivariant-marked-nodal-alteration and replace total space and base by
   their G-quotients. Closed-dominant dimension bounds the base by d-1.
6. Choose an ell-Sylow subgroup (lem-weil-pbc-sylow-subgroup-prime-index). The admissible
   quotient generic-degree lemma gives prime-to-ell index covers. The free-action torsor
   lemma identifies the torsor open. The schemes are finite type over an affine excellent
   base with trivial action, as required by lem-per-admissible-quotient-generic-degree.
7. Apply induction on the base, refine by affine connected opens, use excellence under
   finite type and localization and regular-connected integrality. Apply
   lem-per-nodal-quotient-normalized-base-refinement: normalized dominating components,
   decomposition subgroups and their pulled-back curves give a covering of the quotient.
8. Each model meets every hypothesis below. Apply hresolve to get its proper birational
   regular resolution with the exact inverse-image boundary. Each resolution covers.
9. Compose the finite covers, restrict over the prepared open, pull back by the regular
   completion map and compose with the initial finite cover. Bounded descent completes
   induction, then unbounded descent gives S. The final arrows are objects of alt/S,
   hence finite type (def-per-prime-to-ell-alteration-topology). -/
theorem uniformization_of_marked_nodal_quotient_resolution
    (ell : ℕ) [Fact ell.Prime]
    (hresolve : ∀ (Y Y' C X : Scheme.{u})
      [IsAffine Y] [IsIntegral Y] [IsNoetherian Y] [IsIntegral Y']
      [IsIntegral C] [IsNoetherian C] [C.IsSeparated] [IsIntegral X] [IsNoetherian X]
      (T : Y.IdealSheafData),
      (∀ U : Y.affineOpens, IsExcellent Γ(Y, U)) → IsRegularScheme Y →
      (∃ d : ℕ, topologicalKrullDim Y ≤ d) →
      (∀ y : Y, IsUnit (ell : Y.presheaf.stalk y)) →
      IsStrictNormalCrossingsBoundary T →
      ∀ (G : Type u) [Group G] [Finite G],
      (∃ n : ℕ, Nat.card G = ell ^ n) →
      ∀ (b : Y' ⟶ Y) [IsFinite b] (aY' : G →* Aut Y'),
      (∀ U : Y'.affineOpens, IsExcellent Γ(Y', U)) → IsNormalScheme Y' →
      (∀ g : G, (aY' g).hom ≫ b = b) →
      ∀ (A : Scheme.GaloisCoverAction G (Scheme.Opens.toScheme T.support.compl))
        [ConnectedSpace A.Z]
        (e : A.Z ≅ (b ⁻¹ᵁ T.support.compl).toScheme),
      e.hom ≫ (b ∣_ T.support.compl) = A.π →
      (∀ g : G, A.smul g ≫ e.hom ≫ (b ⁻¹ᵁ T.support.compl).ι =
        e.hom ≫ (b ⁻¹ᵁ T.support.compl).ι ≫ (aY' g).hom) →
      ∀ [Algebra Y.functionField Y'.functionField],
      Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Y'.functionField)) ≫
        Y.fromSpecFunctionField = Y'.fromSpecFunctionField ≫ b →
      (∃ en : Y' ≅ Y.normalizationIn Y'.functionField,
        en.hom ≫ Y.fromNormalizationIn Y'.functionField = b) →
      ∀ (f : C ⟶ Y') [IsHProjective f] [Flat f] [LocallyOfFinitePresentation f]
        (aC : G →* Aut C),
      (∀ U : C.affineOpens, IsExcellent Γ(C, U)) →
      (∀ g : G, (aC g).hom ≫ f = f ≫ (aY' g).hom) →
      HasNodalGeometricFibres f →
      (∀ c : C, b (f c) ∉ T.support → c ∈ f.smoothLocus) →
      ∀ D : C.IdealSheafData, D.IsInvertible →
      (∀ g : G, D.comap (aC g).hom = D) →
      IsFinite (D.subschemeι ≫ f) → Etale (D.subschemeι ≫ f) →
      (∀ c : C, c ∈ D.support → c ∈ f.smoothLocus) →
      ∀ π : C ⟶ X, IsAdmissibleFiniteSchemeQuotient aC π →
      (∀ U : X.affineOpens, IsExcellent Γ(X, U)) →
      ∀ E : X.IdealSheafData, E.IsInvertible →
      (π ⁻¹' (E.support : Set X) ⊆
        (D.support : Set C) ∪ (f ≫ b) ⁻¹' (T.support : Set Y)) →
      ∃ (R : Scheme.{u}) (r : R ⟶ X),
        IsIntegral R ∧ IsRegularScheme R ∧ IsNoetherian R ∧ IsProper r ∧
        (∃ U : X.Opens, Dense (U : Set X) ∧ Dense (r ⁻¹' (U : Set X)) ∧
          IsIso (r ∣_ U)) ∧
        ∃ H : R.IdealSheafData, IsStrictNormalCrossingsBoundary H ∧
          (H.support : Set R) = r ⁻¹' (E.support : Set X))
    (S : Scheme.{u}) [IsReduced S] [IsNoetherian S]
    (hS : ∀ U : S.affineOpens, IsQuasiExcellent Γ(S, U))
    (hinv : ∀ s : S, IsUnit (ell : S.presheaf.stalk s))
    (Z : Set S) (hZ : IsClosed Z) (hZrare : IsNowhereDense Z) :
    ∃ base : PrimeToEllAlteration.Alt S,
      base.obj = Over.mk (𝟙 S) ∧
      ∃ (n : ℕ) (T : Fin n → PrimeToEllAlteration.Alt S) (q : ∀ i, T i ⟶ base),
        PrimeToEllAlteration.IsCoveringFamily ell T q ∧
        (∀ i, IsRegularScheme (T i).obj.left ∧ IsNoetherian (T i).obj.left) ∧
        ∀ i, ∃ H : (T i).obj.left.IdealSheafData,
          IsStrictNormalCrossingsBoundary H ∧
          (H.support : Set (T i).obj.left) = (T i).obj.hom ⁻¹' Z := by
  sorry

end AlgebraicGeometry
