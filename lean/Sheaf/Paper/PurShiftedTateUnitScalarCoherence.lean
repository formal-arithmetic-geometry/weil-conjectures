/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.Paper.IntegralTwistDerivedScalarCanonical
public import Sheaf.Paper.ConstantCoefficientScalarNormalization
public import Sheaf.Paper.CompletedScalarShift
public import Sheaf.Paper.CompletedLineTensorCoherence
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.SfIntegralConstructible
import Sheaf.Paper.TwistPreservesFiniteness
import Sheaf.Paper.IntegralCtfTriangulated
import Sheaf.Paper.CompletedScalarChainShift
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Paper.IntegralTwistBaseChange

/-! # Coherence of normalized shifted Tate-unit comparisons

Source: main-20261015, sec-smooth-purity/sk-thm-purity-transport,
`thm-pur-rational-and-qbar-purity.md`, coefficient transport, Step 3
(blueprint: lem-pur-shifted-tate-unit-scalar-coherence).

The coefficient unit and all scalar, twist and completion functors are the existing
constructions. The helper maps below assemble their specified normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
namespace PurShiftedTate

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
  (ι : E →ₐ[Padic l] F) (S : Scheme.{u})

/-- Ordinary multiplication on the coefficient unit, normalized by the actual quotient
completion map and the strict coefficient-unit isomorphism. Their quotient coordinates
are multiplication and its inverse, so this is the ordinary K-flat multiplication map.
Source: purity transport Step 3, completed-unit normalization
(blueprint: lem-pur-shifted-tate-unit-scalar-coherence). -/
def unitIso (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    (completedDerivedScalarExtension l E F ι S).obj
        (integralConstantCoefficientObject l E S) ≅ integralConstantCoefficientObject l F S :=
  (@asIso _ _ _ _ ((completedScalarComparison l E F ι S).app
    (integralConstantCoefficientObject l E S))
    (((finiteFreeCompletedScalarComparison l E F ι S).2.1 _
      (integralConstantCoefficient_constructible l E S D hl).2.2.1).1)) ≪≫
    constantCoefficientIntegralScalarIso l E F ι S

/-- Canonical ordinary derived shift, fixed by its termwise tensor and universal-counit
normalization. The selected structure is uniquely fixed by that normalization.
Source: purity transport Step 3, canonical cochain shift comparison
(blueprint: lem-pur-shifted-tate-unit-scalar-coherence). -/
def shiftIso (n : ℤ) :
    shiftFunctor (DerivedCategory (integralTowerModules l E S)) n ⋙
        completedDerivedScalarExtension l E F ι S ≅
      completedDerivedScalarExtension l E F ι S ⋙
        shiftFunctor (DerivedCategory (integralTowerModules l F S)) n :=
  Functor.commShiftIso (completedDerivedScalarExtension l E F ι S)
    (self := (completedScalarComparison_commutesWithShift l E F ι S).choose_spec.choose) n

/-- Q_l in the coefficient universe, with its canonical algebra inclusion.
Source: purity transport Step 3, E_0 = Q_l
(blueprint: lem-pur-shifted-tate-unit-scalar-coherence). -/
def baseInclusion : ULift.{u} (Padic l) →ₐ[Padic l] E :=
  (Algebra.ofId (Padic l) E).comp ULift.algEquiv.toAlgHom

end PurShiftedTate

namespace PurityFiniteSetting

variable (P : PurityFiniteSetting.{u})

/-- The specified inverse of the coefficient prime in each residue field, inherited
from l distinct from p through the structure map. This adds no hypothesis.
Source: purity conventions and transport Step 3
(blueprint: lem-pur-shifted-tate-unit-scalar-coherence). -/
@[instance_reducible]
def shiftedTateResidueInverse (S : Scheme.{u}) [S.Over (Spec (.of P.field.k))] :
    ∀ x : S, Invertible (P.coefficients.l : S.residueField x) :=
  fun x ↦ (map_natCast (IsLocalRing.residue (S.presheaf.stalk x)) P.coefficients.l) ▸
    ((P.coefficientPrime_isUnit_stalk S (S ↘ Spec (.of P.field.k)) x).map
      (IsLocalRing.residue (S.presheaf.stalk x))).invertible

variable (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
  [FiniteDimensional (Padic P.coefficients.l) E]
  (S : Scheme.{u}) [S.Over (Spec (.of P.field.k))]

/-- U_E(d)[2d], using the recorded exact sheaf tensor and the standard cochain shift.
Source: purity transport Step 3, the displayed definition of T_L
(blueprint: lem-pur-shifted-tate-unit-scalar-coherence). -/
def shiftedTateUnit (d : ℕ) : DerivedCategory (integralTowerModules P.coefficients.l E S) :=
  letI := P.shiftedTateResidueInverse S
  ((sfIntegralTwistingFunctor P.coefficients.l E S (d : ℤ)).obj
    (integralConstantCoefficientObject P.coefficients.l E S))⟦2 * (d : ℤ)⟧

/-- Membership and the two uniform containing Tor intervals asserted for one stage.
The index n denotes the positive reduction exponent n+1.
Source: purity transport Step 3, the unit and shifted-unit domains
(blueprint: lem-pur-shifted-tate-unit-scalar-coherence). -/
def shiftedTateUnitDomain (d : ℕ) : Prop :=
  finiteTorConstructibleIntegral P.coefficients.l E S
      (integralConstantCoefficientObject P.coefficients.l E S) ∧
    finiteTorConstructibleIntegral P.coefficients.l E S (P.shiftedTateUnit E S d) ∧
    (∀ n : ℕ, AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude S
      (Padic.coefficientExtensionRing P.coefficients.l E (n + 1))
      ((scalarReductionDerivedExtension P.coefficients.l E S n).obj
        (integralConstantCoefficientObject P.coefficients.l E S)) 0 0) ∧
    ∀ n : ℕ, AlgebraicGeometry.Scheme.HasProEtaleTorAmplitude S
      (Padic.coefficientExtensionRing P.coefficients.l E (n + 1))
      ((scalarReductionDerivedExtension P.coefficients.l E S n).obj
        (P.shiftedTateUnit E S d)) (-(2 * (d : ℤ))) (-(2 * (d : ℤ)))

variable (F : Type u) [Field F] [Algebra (Padic P.coefficients.l) F]
  [FiniteDimensional (Padic P.coefficients.l) F]
  (ι : E →ₐ[Padic P.coefficients.l] F)

/-- The specified q: canonical shift, then the shifted composite of beta and twisted
coefficient multiplication. Each factor is the published normalized comparison.
Source: purity transport Step 3, q_{H/L} = (u(d) beta)[2d] s
(blueprint: lem-pur-shifted-tate-unit-scalar-coherence). -/
def shiftedTateScalarIso (d : ℕ) :
    (completedDerivedScalarExtension P.coefficients.l E F ι S).obj
        (P.shiftedTateUnit E S d) ≅ P.shiftedTateUnit F S d :=
  letI := P.shiftedTateResidueInverse S
  (PurShiftedTate.shiftIso P.coefficients.l E F ι S (2 * (d : ℤ))).app
      ((sfIntegralTwistingFunctor P.coefficients.l E S (d : ℤ)).obj
        (integralConstantCoefficientObject P.coefficients.l E S)) ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      ((integralTwistOrdinaryBeta P.coefficients.l E F ι S (d : ℤ)).app
          (constantWeilIntegralObject P.coefficients.l E P.field P.coefficients.different S) ≪≫
        (sfIntegralTwistingFunctor P.coefficients.l F S (d : ℤ)).mapIso
          (PurShiftedTate.unitIso P.coefficients.l E F ι S P.field P.coefficients.different))

end PurityFiniteSetting
end WeilConjectures

namespace WeilConjectures
namespace PurityFiniteSetting

variable (P : PurityFiniteSetting.{u})
  (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
  [FiniteDimensional (Padic P.coefficients.l) E]
  (F : Type u) [Field F] [Algebra (Padic P.coefficients.l) F]
  [FiniteDimensional (Padic P.coefficients.l) F]
  (ι : E →ₐ[Padic P.coefficients.l] F)
  (S : Scheme.{u}) [S.Over (Spec (.of P.field.k))]
  [hft : LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
  [hqc : QuasiCompact (S ↘ Spec (.of P.field.k))]
  [hsep : IsSeparated (S ↘ Spec (.of P.field.k))]

include hft hqc hsep in
/-- The normalized coefficient-unit and shifted Tate-unit maps commute in the tower
Q_l ⊆ E ⊆ F. The stated Tor intervals contain the supports, also for the empty scheme.
Source: main-20261015, `thm-pur-rational-and-qbar-purity.md`, coefficient transport Step 3
(blueprint: lem-pur-shifted-tate-unit-scalar-coherence).

Proof:
1. The regular unit and each rank-one Tate line are flat in degree zero. Tensoring
   with either preserves acyclicity; their shifts are K-flat with flat terms. Thus
   derived change of rings computes them on these very models. The specified chi
   compares this computation with the strict quotient tower, including repeated fields.
2. Constant coefficient constructibility gives completeness, constructible reductions
   and support in [0,0]. Tensoring a reduction with a module returns that module, so
   its Tor interval is [0,0], uniformly in the positive reduction level.
3. Twist preservation gives the same intervals for U(d). The standard cochain shift
   by 2d moves the interval to [-2d,-2d]. Integral ctf triangulatedness supplies shift
   and isomorphism closure, including the zero object on an empty scheme.
4. On ((x tensor b) tensor c), both unit paths multiply to iota(x)*iota(b)*c.
   The completed coefficient inclusions compose, and local pure tensor generation
   extends equality through sheafification and the canonical K-flat counits.
5. Before shifting, beta followed by twisted multiplication sends
   (x tensor z) tensor b to iota(x)*b times the target twist-line image of z.
   The two tower paths coincide by the twist-line base-change tower equation.
6. The termwise shift comparison is identity on tensor components and respects
   the differential (-1)^(2d)*d. It commutes with associativity and the maps of step 5.
   Shifting that equation gives the displayed q equation. Completed-scalar-chain-shift
   identifies its completion normalization with the actual zero-second-coordinate chi.
7. q identifies A(T_0) with T_E, so isomorphism closure gives its ctf membership.
   Identity extensions use coefficient multiplication and the natural completeness
   map under chi; the same tensor calculations apply without any strictness assumption.
-/
theorem shiftedTateUnitScalarCoherence (d : ℕ) :
    P.shiftedTateUnitDomain (ULift.{u} (Padic P.coefficients.l)) S d ∧
    P.shiftedTateUnitDomain E S d ∧ P.shiftedTateUnitDomain F S d ∧
    finiteTorConstructibleIntegral P.coefficients.l E S
      ((completedDerivedScalarExtension P.coefficients.l (ULift.{u} (Padic P.coefficients.l)) E
        (PurShiftedTate.baseInclusion P.coefficients.l E) S).obj
          (P.shiftedTateUnit (ULift.{u} (Padic P.coefficients.l)) S d)) ∧
    ((CompletedLineTensor.associatorData P.coefficients.l
        (ULift.{u} (Padic P.coefficients.l)) S E
        (PurShiftedTate.baseInclusion P.coefficients.l E) F ι).derived.hom.app
          (integralConstantCoefficientObject P.coefficients.l
            (ULift.{u} (Padic P.coefficients.l)) S)) ≫
      (PurShiftedTate.unitIso P.coefficients.l (ULift.{u} (Padic P.coefficients.l)) F
        (ι.comp (PurShiftedTate.baseInclusion P.coefficients.l E)) S
          P.field P.coefficients.different).hom =
      (completedDerivedScalarExtension P.coefficients.l E F ι S).map
        (PurShiftedTate.unitIso P.coefficients.l (ULift.{u} (Padic P.coefficients.l)) E
          (PurShiftedTate.baseInclusion P.coefficients.l E) S
            P.field P.coefficients.different).hom ≫
        (PurShiftedTate.unitIso P.coefficients.l E F ι S
          P.field P.coefficients.different).hom ∧
    ((CompletedLineTensor.associatorData P.coefficients.l
        (ULift.{u} (Padic P.coefficients.l)) S E
        (PurShiftedTate.baseInclusion P.coefficients.l E) F ι).derived.hom.app
          (P.shiftedTateUnit (ULift.{u} (Padic P.coefficients.l)) S d)) ≫
      (P.shiftedTateScalarIso (ULift.{u} (Padic P.coefficients.l)) S F
        (ι.comp (PurShiftedTate.baseInclusion P.coefficients.l E)) d).hom =
      (completedDerivedScalarExtension P.coefficients.l E F ι S).map
        (P.shiftedTateScalarIso (ULift.{u} (Padic P.coefficients.l)) S E
          (PurShiftedTate.baseInclusion P.coefficients.l E) d).hom ≫
        (P.shiftedTateScalarIso E S F ι d).hom := by
  sorry

end PurityFiniteSetting
end WeilConjectures
