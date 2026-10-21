/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Sheaf.Paper.OrientedHypercoverDescentDatum
public import Sheaf.AlgebraicGeometry.ProperHypercover
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.AlgebraicGeometry.ProperHypercoverEtaleDescent
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import Sheaf.Paper.OrientedNearbyCycles

/-!
# Proper hypercover descent for oriented nearby cycles

Source: Orgogozo, Modifications et cycles proches sur une base générale, §9.2,
printed p. 22; Stacks Project, Tags 0DHL and 0D7F
(blueprint: lem-trf-oriented-nearby-hypercover-spectral-sequence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.AdicSites

namespace AlgebraicGeometry.OrientedNearbyCycles.Hypercover

/-- Proper hypercover descent for nearby cycles, including its finite filtration and
ordinary base-change naturality. No properness of f and no Psi-goodness is assumed.
Source: Orgogozo §9.2, printed p. 22; Stacks 0DHL and 0D7F
(blueprint: lem-trf-oriented-nearby-hypercover-spectral-sequence).

Proof:
1. Form the total étale topos of Y and the total vanishing topos. The universal oriented
   projection descriptions identify the component squares compatibly with every face
   and degeneracy (def-trf-oriented-nearby-cycles), hence identify the total composites
   (lem-trf-total-site-augmentation-spectral-sequence).
2. Proper hypercover étale descent gives the canonical unit K ≅ Repsilon_*epsilon^*K
   (lem-trf-proper-hypercover-etale-descent). Only bounded-below torsion is needed.
3. Put L=Rpsi_bullet,*epsilon^*K. Component restriction gives Rpsi_i,*K_i. Exact inverse
   image preserves the bound c. Left t-exact direct image and joint conservativity of
   component restriction imply H^j(L)=0 for j<c
   (lem-weil-pbc-derived-functor-negative-vanishing,
   lem-weil-pbc-ring-sheaves-grothendieck).
4. Derived direct-image composition identifies Rbarepsilon_*L with Rpsi_f,*K, with the
   augmentation equal to Rpsi_f,* of the ordinary descent unit. The composite-adjunction
   normalization fixes its direction and its component mates
   (lem-weil-pbc-ringed-topoi-derived-pushforward-composition,
   lem-sfb-derived-composition-adjunction-normalization).
5. Apply the total-site augmentation spectral sequence. Its first page is the displayed
   term and its abutment the nearby-cycle complex. The half-plane i>=0,j>=c makes each
   diagonal finite: the associated graded at (i,n-i) stabilizes by page max(1,n-c+2).
   Its filtration is full at 0 and zero at n-c+1; for n<c the entire abutment is zero
   (lem-trf-total-site-augmentation-spectral-sequence).
6. For an arbitrary base change, the total comparison and the coefficient comparison
   induce the page morphisms. Restriction to component i is precisely termChange:
   ordinary base change for barepsilon_i followed by beta_i. Mate pasting identifies
   the abutment with beta_f and makes the augmented edge commute; functoriality also
   preserves the finite filtration and its quotient comparisons
   (lem-weil-pbc-mate-pasting; Stacks 0D99). The page-1 normalization determines all
   later pages, so mate pasting gives identity and composition compatibility as well.
-/
theorem exists_descent {X S : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (m : ℤ) (hmΛ : (m : Λ) = 0) (hmS : IsUnit (m : Γ(S, ⊤)))
    (Y : SimplicialObject (Over X)) (hY : IsProperHypercover Y)
    (hfp : ∀ i : ℕ, LocallyOfFinitePresentation (epsilon Y i ≫ f) ∧
      QuasiCompact (epsilon Y i ≫ f) ∧ QuasiSeparated (epsilon Y i ≫ f))
    (K : EtaleDerived X Λ)
    (hK : Etale.DerivedCategory.isBoundedConstructible (Coeff.{u, u + 1} Λ) X
      ((readModules X Λ).mapDerivedCategory.obj K))
    (c : ℤ) (hc : ∀ j : ℤ, j < c →
      IsZero ((DerivedCategory.homologyFunctor _ j).obj K)) :
    ∃ D : Descent f Y Λ K c,
      ∃ Db : ∀ b : Change f Y,
        Descent b.f' b.Y' Λ (((etaleModules.{u, u + 1} b.h).pull (Coeff.{u, u + 1} Λ)).obj K) c,
        (∀ b : Change f Y, Nonempty (Comparison D b (𝟙 _) (Db b))) ∧
        (∀ (b₁ b₂ : Change f Y) (q : Between b₁ b₂),
          Nonempty (Comparison (Db b₁) q.change (q.coefficients Λ K) (Db b₂))) := by
  sorry

end AlgebraicGeometry.OrientedNearbyCycles.Hypercover
