/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import Sheaf.Paper.SupportedCup
public import Sheaf.Paper.SupportedCupFunctoriality
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.SupportedCohomologyHom
import Sheaf.Paper.SupportedHomPullback
import Sheaf.Paper.FiniteTateSiteDescent
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.Paper.RingedTopoiDerivedTensorPullback
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
import Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.Paper.DerivedPullbackTensorIso
import Sheaf.Paper.ShiftedTensorMorphismCalculus
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorResolution
import Sheaf.Paper.SupportedHomAdjunctionTranspose

/-!
# Vanishing of the closed-support cup action

Source: Stacks Project, Cohomology, Tags 0G75--0G77, and the finite-coefficient
pro-etale tensor-morphism construction (blueprint: lem-pur-closed-supported-cup-vanishing).
The three helper definitions only specialize the published supported cup to full support
and transport its intersection support along the canonical identity-pullback isomorphism.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- Regard an ordinary class as a class with full support using the direct-image
identity isomorphism. Source: the full-support case of the supported-Hom construction,
Stacks 0G76 (blueprint: lem-pur-closed-supported-cup-vanishing). -/
def closedCupFullSupport (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (a t : ℤ)
    (α : P.FunctorialCupOrdinaryH true X a t) : P.FunctorialCupH true (𝟙 X) a t :=
  (P.functorialCupSingle true X).map
    ((ProEtale.lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).hom.app (P.constant X)) ≫ α

/-- The existing supported cup with first support all of X, transported from
X times_X Z to Z along the canonical second-projection isomorphism.
Source: the tensor-morphism definition of def-pur-supported-cup, and Stacks 0G76
(blueprint: lem-pur-closed-supported-cup-vanishing). -/
def closedSupportedCup (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    (i : Z ⟶ X) [IsClosedImmersion i] (a b t s : ℤ)
    (α : P.FunctorialCupOrdinaryH true X a t) (β : P.FunctorialCupH true i b s) :
    P.FunctorialCupH true i (a + b) (t + s) :=
  P.functorialCupChangeSupport true i (ProEtale.cupIntersection (𝟙 X) i)
    (pullback.snd (𝟙 X) i)
    (pullback.condition.symm) (a + b) (t + s)
    (P.functorialCup true (X ↘ Spec (.of P.field.k)) (𝟙 X) i a b t s
      (P.closedCupFullSupport X a t α) β)

/-- The ordinary cup is the full-support specialization of the same supported cup,
followed by the canonical map forgetting full support. Source: Stacks 0G77,
its lower horizontal arrow (blueprint: lem-pur-closed-supported-cup-vanishing). -/
def closedOrdinaryCup (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))] (a b t s : ℤ)
    (α : P.FunctorialCupOrdinaryH true X a t)
    (β : P.FunctorialCupOrdinaryH true X b s) :
    P.FunctorialCupOrdinaryH true X (a + b) (t + s) :=
  P.functorialCupForget true (𝟙 X) (a + b) (t + s)
    (P.closedSupportedCup (𝟙 X) a b t s α (P.closedCupFullSupport X b s β))

/-- Restriction to a closed support detects the zero cup action, both before and
 after forgetting support. Source: Stacks 0G75--0G77, interpreted on the ordinary
 finite-coefficient pro-etale sites via the prescribed supported tensor product
 (blueprint: lem-pur-closed-supported-cup-vanishing).

Proof:
1. Finite type over the field makes X Noetherian by
lem-weil-pbc-finite-type-over-noetherian. Every open in an affine of X is quasi-compact
by lem-weil-pbc-noetherian-open-subscheme-noetherian, so the open complement of i is
quasi-compact (def-weil-finite-type-morphism).
2. By lem-pur-supported-hom, write alpha as A_X to A_X(t)[a] and beta as
S=i_*A_Z to A_X(s)[b]. For supports (X,Z), the coefficient multiplication in
def-pur-supported-cup is the left unitor of S. Thus the product is the signed shifted
tensor of alpha and beta, precomposed with the inverse unitor and followed by twist
multiplication.
3. The normalization lem-pur-supported-hom-adjunction-transpose evaluates a sheaf
map at q(1), where q:A_X to S restricts constants. Applying this termwise to injective
resolutions identifies forgetting support with precomposition by q, on both the input
and the output.
4. Lem-pur-supported-hom-pullback identifies ordinary restriction with Li^*alpha.
Lem-amb-finite-tate-site-descent and lem-asd-etale-finite-twist-pullback give the
finite-twist comparisons. For negative twists, dualize the rank-one lines; exactness
lem-sf-comparison-pullback-exact and the tensor comparison
lem-weil-pbc-ringed-topoi-derived-tensor-pullback preserve evaluation at the dual basis.
Consequently the hypothesis says Li^*alpha=0.
5. The coefficient calculation of def-pur-supported-cup makes S flat, so
T=A_X(t)[a] tensor S is H[a], for the sheaf H=A_X(t) tensor S.
Lem-sf-ringed-closed-kernel-adjoint gives j^*S=0, and
lem-pur-proetale-inverse-image-tensor-comparison gives j^*H=0.
Lem-exc-proetale-closed-essential-image makes the actual unit H to i_*i^*H invertible;
prop-weil-pbc-proetale-constant-exact supplies the constant-ring identifications.
6. Both functors of Li^* adjoint to i_* are exact. The termwise adjunction of
lem-weil-pbc-termwise-adjunction-homotopy and localization factorization of
lem-weil-pbc-exact-functor-derived-factorization identify their derived unit on T with
the shift of the sheaf unit on H. Hence that unit is invertible. This only treats a
shifted sheaf; it does not test arbitrary derived morphisms on cohomology sheaves.
7. Put m=(alpha tensor 1_S) after the inverse left unitor. Naturality of the
finite comparison lem-pur-derived-pullback-tensor-iso identifies Li^*m with
Li^*alpha tensor 1, up to invertible comparisons. This is zero: additivity in
lem-pur-shifted-tensor-morphism-calculus sends a zero first factor to zero.
8. Unit naturality gives eta_T after m = i_*(Li^*m) after eta_S = 0.
Since eta_T is invertible, m=0.
9. Bifunctoriality lem-weil-derived-tensor-functorial factors alpha tensor beta as
(1 tensor beta) after (alpha tensor 1_S). The product of Step 2 therefore factors
through m, and is zero. Supported Hom gives the first assertion.
10. Naturality of the left unitor gives lambda_S inverse after q =
(1 tensor q) after lambda_A inverse. Thus precomposing the product by q equals the
ordinary cup of alpha with beta after q, with the same shift and twist maps.
By Step 3 this is the forgetting-support square of Stacks 0G77. The first assertion
therefore gives the second. -/
theorem closed_supported_cup_vanishing (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (i : Z ⟶ X) [IsClosedImmersion i] (a b : ℕ) (t s : ℤ)
    (α : P.FunctorialCupOrdinaryH true X (a : ℤ) t)
    (β : P.FunctorialCupH true i (b : ℤ) s)
    (hα : P.functorialCupOrdinaryPullback true i (X ↘ Spec (.of P.field.k)) a t α = 0) :
    P.closedSupportedCup i a b t s α β = 0 ∧
      P.closedOrdinaryCup X a b t s α (P.functorialCupForget true i b s β) = 0 := by
  sorry

end WeilConjectures.PurityFiniteSetting
