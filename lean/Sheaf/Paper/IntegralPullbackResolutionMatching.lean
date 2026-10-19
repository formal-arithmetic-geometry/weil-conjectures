/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.Paper.IntegralTowerInverseImageUnit
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.Algebra.Homology.KFlat
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.TraceFormula.IntegralConeCounitRealization
import Sheaf.CategoryTheory.DiagramSiteRealization
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.StrictRoosComparison
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# The counit identity for the integral inverse-image comparison

Source: blueprint Global powers in
`sec-trace-formula/sk-thm-trace-transport/thm-trf-l-function-euler-product.proof.md`;
Stacks Project, Tags 0FND, 0DVC, 03CZ, 06YY and 0941
(blueprint: lem-trf-integral-pullback-resolution-matching).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

/-- Translate invertibility of ell in the stalks into the residue-field instance
required by the recorded realization. This is the image of the same unit under
Scheme.residue, with no new hypothesis. Source: blueprint Global powers
(blueprint: lem-trf-integral-pullback-resolution-matching). -/
@[instance_reducible] def integralResolutionMatchingResidueInvertible (l : ℕ) (X : Scheme.{u})
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x)) :
    ∀ x : X, Invertible (l : X.residueField x) :=
  fun x ↦
    ((map_natCast (X.residue x).hom l) ▸
      ((hX x).map (X.residue x).hom)).invertible

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (D : IntegralComparisonSystem.{u} l)
  {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)

/-- The first pullback's actual whole quotient diagram, in the normalized
presentation supplied by the recorded realization. Source: blueprint Global powers;
Stacks 0941 (blueprint: lem-trf-integral-pullback-resolution-matching). -/
abbrev integralResolutionMatchingTower (N : sfIntegralConstructibleCategory l E V) :=
  (integralComparisonDerivedSequencePullback l E k).obj
    (((D.coefficient E).system V).reduction.obj N.obj)

/-- The recorded eta, using the stalk formulation of ell invertibility.
The instances merely transport those units to the residue fields.
Source: blueprint Global powers; Stacks 0941
(blueprint: lem-trf-integral-pullback-resolution-matching). -/
def integralResolutionMatchingEta
    (hV : ∀ v : V, IsUnit (l : V.presheaf.stalk v))
    (hW : ∀ w : W, IsUnit (l : W.presheaf.stalk w))
    (hZ : ∀ z : Z, IsUnit (l : Z.presheaf.stalk z))
    (N : sfIntegralConstructibleCategory l E V) :
    (integralDerivedPullback l E h).obj ((integralDerivedPullback l E k).obj N.obj) ≅
      (coefficientSequenceLimit l E Z).obj
        ((integralComparisonDerivedSequencePullback l E h).obj
          (integralResolutionMatchingTower l E D k N)) := by
  letI := integralResolutionMatchingResidueInvertible l V hV
  letI := integralResolutionMatchingResidueInvertible l W hW
  letI := integralResolutionMatchingResidueInvertible l Z hZ
  exact integralComparisonEta l E D h k N

/-- The counit image of eta after kappa is exactly the termwise tensor-unit map
applied to the inverse image of the original counit. The equation lives in the
derived category of entire strict completed-coefficient towers. The defining
realization for k explicitly transports M to Rlim C; no levelwise reduction or
realization is applied to the asserted equality.

Source: blueprint Global powers in
sec-trace-formula/sk-thm-trace-transport/thm-trf-l-function-euler-product.proof.md;
Stacks Project, Tags 0FND, 0DVC, 03CZ, 06YY and 0941
(blueprint: lem-trf-integral-pullback-resolution-matching).

Proof:
1. Put C=C_k, D=h-star C and H=h-inverse. Choose the separate flat-term K-flat
   resolution q:P' to M used by kappa. Its quotient tower is B and its pulled-back
   tower is C_h. The strict compatible family is theta=u_B after H(r), where r is
   the actual quotient map. The definition gives kappa=r_theta after H(q) inverse
   [def-pur-integral-derived-operations, def-weil-inverse-image-pullback-comparison].
2. The diagonal is exact by levelwise exactness of tower categories. Deriving the
   diagonal/limit adjunction by lem-pc-pre-derived-adjoint-functors-general gives
   the K-injective-normalized counit epsilon. Its naturality says epsilon_T' after
   Delta(Rlim psi)=psi after epsilon_T for every derived tower morphism psi,
   including roofs [lem-weil-pbc-ringed-strict-tower-homotopy-limit].
3. On the small diagram site, extension from the constant completed ring to the
   entire quotient-ring sheaf is left adjoint to exact coefficient restriction.
   Delta P' is K-flat with flat terms because tensor products and acyclicity are
   levelwise. Derived adjunction sends phi:B to C to U(phi) after r
   [lem-weil-pbc-diagram-site-realization, def-pc-sheaf-restrict-scalars,
   lem-pur-derived-change-of-rings, def-pc-kflat-complex, def-pur-sheaf-tensor-product].
4. Take phi adjunct to epsilon_C after Delta(q). The normalization of
   lem-trf-integral-pullback-comparison-realization identifies eta with Rlim(h-star
   phi); the adjunct identity is U(phi) after r=epsilon_C after Delta(q).
5. Exact countable products and lem-weil-strict-roos-comparison identify the cone
   used by kappa with the normalized Rlim C_h. Applying
   lem-trf-integral-cone-counit-realization to its compatible family gives
   epsilon_C_h after Delta(r_theta)=theta.
6. The finite unit is natural: both composites send x to phi(x) tensor 1.
   This commutes with quotient transitions and extends to roofs by exactness of
   H and finite pullback [lem-weil-tower-category-levelwise-abelian]. Therefore
   h-star(phi) after theta=u_C after H(epsilon_C) after Delta(H(q)).
7. Counit naturality, followed by steps 4--6, identifies the two sides after
   precomposition with Delta(H(q)). Exactness makes H(q) a quasi-isomorphism;
   cancel its invertible class to obtain the displayed whole-tower identity. -/
theorem integralPullbackResolutionMatching
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (D : IntegralComparisonSystem.{u} l) {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k]
    (hV : ∀ v : V, IsUnit (l : V.presheaf.stalk v))
    (hW : ∀ w : W, IsUnit (l : W.presheaf.stalk w))
    (hZ : ∀ z : Z, IsUnit (l : Z.presheaf.stalk z))
    (N : sfIntegralConstructibleCategory l E V) :
    (integralComparisonConstantTower l E Z).map
        (inverseImagePullbackComparisonDerived l E h hZ hW
            ((integralDerivedPullback l E k).obj N.obj) ≫
          (integralResolutionMatchingEta l E D h k hV hW hZ N).hom) ≫
        (integralComparisonTowerCounit l E Z).app
          ((coefficientSequenceDerivedRestriction l E Z).obj
            ((integralComparisonDerivedSequencePullback l E h).obj
              (integralResolutionMatchingTower l E D k N))) =
      (integralTowerInverseImageDiagonal l E h).hom.app
          ((integralDerivedPullback l E k).obj N.obj) ≫
        (integralDerivedTowerInverseImage l E h).map
          ((integralComparisonConstantTower l E W).map
              (((D.coefficient E).pullback k).realization.hom.app N.obj) ≫
            (integralComparisonTowerCounit l E W).app
              ((coefficientSequenceDerivedRestriction l E W).obj
                (integralResolutionMatchingTower l E D k N))) ≫
        (integralDerivedTowerInverseImageUnit l E h).hom.app
          (integralResolutionMatchingTower l E D k N) := by
  sorry

end WeilConjectures
