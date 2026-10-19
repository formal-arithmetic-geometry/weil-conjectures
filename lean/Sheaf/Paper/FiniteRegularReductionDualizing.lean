/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.AdicExceptionalProjection
public import Sheaf.Paper.FiniteSmoothCoefficientArrows
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Compactification.NagataCompactification
import Sheaf.RingTheory.FieldsExcellent
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic
import Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula
import Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons

/-!
# Finite normalized dualizing complexes on schemes with regular reduction

Source: ILO, Expose XVII, Propositions 2.4.4.1 and 4.1.2, Remark 4.1.3,
Theorem 5.1.1 and Proposition 6.2.2.1; Bhatt--Scholze, Lemma 6.7.20
(blueprint: lem-per-finite-regular-reduction-dualizing).

The natural index `n` means coefficient exponent `n + 1`. All categories are on the
small etale site. The ambient exceptional adjoint is evaluated at the coefficient
unit; its bounded constructibility identifies it with the constructible adjoint.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.RegularReductionDualizing

/-- The existing nonnegative Tate sheaf, at a positive prime-power level.
Source: ILO XVII 2.1 and 2.4 (blueprint: lem-per-finite-regular-reduction-dualizing). -/
abbrev twist (l n : ℕ) (X : Scheme.{u}) (d : ℕ) :=
  Scheme.finiteEtaleTateTwist X (l ^ (n + 1)) (FiniteReduction.Coeff.{u} l (n + 1))
    (CharP.cast_eq_zero _ _) d

/-- The Tate sheaf placed in degree zero, before the dimension shift.
Source: ILO XVII 6.2.2.1 (blueprint: lem-per-finite-regular-reduction-dualizing). -/
abbrev twistComplex (l n : ℕ) (X : Scheme.{u}) (d : ℕ) :=
  (_root_.DerivedCategory.singleFunctor _ 0).obj (twist l n X d)

/-- The published quotient, with positive levels indexed from zero.
Source: Bhatt--Scholze 6.7.20 (blueprint: lem-per-finite-regular-reduction-dualizing). -/
abbrev quotient (l n : ℕ) :=
  FiniteReduction.quotient.{u} l (Nat.le_succ (n + 1))

/-- Actual scalar reduction of the exceptional image of the coefficient unit.
It is the compact-support counit transpose, followed by scalar-unit normalization.
Source: ILO XVII 4.1.2 and Bhatt--Scholze 6.7.20
(blueprint: lem-per-finite-regular-reduction-dualizing). -/
def dualizingReduction (l n : ℕ) [Fact l.Prime] {X Y : Scheme.{u}}
    (a : X ⟶ Y) [HasCompactification a] :
    (scalarExtension (quotient l n) X).obj
        (dualizingComplex (ModuleCat.{u + 1} (FiniteReduction.Coeff l (n + 2))) a) ⟶
      dualizingComplex (ModuleCat.{u + 1} (FiniteReduction.Coeff l (n + 1))) a :=
  ExceptionalCoefficients.mateMap (quotient l n) a
      (constantComplex (FiniteReduction.Coeff l (n + 2)) Y) ≫
    (rightDerivedUpperShriek (ModuleCat.{u + 1} (FiniteReduction.Coeff l (n + 1))) a).map
      (ExceptionalCoefficients.unitIso (quotient l n) Y).hom

/-- Shifted reduction induced by an ordinary scalar-extension map of Tate sheaves.
The scalar/single counit is retained, so invertibility asserts absence of higher Tor.
Source: Bhatt--Scholze 6.7.20 (blueprint: lem-per-finite-regular-reduction-dualizing). -/
def shiftedTwistReduction (l n : ℕ) (X : Scheme.{u}) (d : ℕ)
    (t : (ProEtale.etaleSheafExtendScalars (quotient l n) X).obj (twist l (n + 1) X d) ≅
      twist l n X d) :
    (scalarExtension (quotient l n) X).obj ((twistComplex l (n + 1) X d)⟦(2 * d : ℤ)⟧) ⟶
      (twistComplex l n X d)⟦(2 * d : ℤ)⟧ :=
  (FiniteSmoothPurity.scalarShiftIso (quotient l n) X (2 * d : ℤ)).hom.app _ ≫
    (shiftFunctor _ (2 * d : ℤ)).map
      (FiniteSmoothPurity.scalarSingleMap (quotient l n) X (twist l (n + 1) X d) ≫
        (_root_.DerivedCategory.singleFunctor _ 0).map t.hom)

/-- Witnesses for the regular-reduction model and its ordinary rank-one reduction tower.
The root-line data prescribe the power map and every scalar/root generator. The other
Tate powers use ordinary tensor balancing, with the scalar unit at degree zero.
The only geometric normalization is the actual exceptional image of the base unit,
which has relative dimension function trdeg_k kappa(x), with no separability condition.
Source: ILO XVII 2.4.4.1, 4.1.2, 5.1.1, 6.2.2.1; Bhatt--Scholze 6.7.20
(blueprint: lem-per-finite-regular-reduction-dualizing). -/
def Model (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (a : X ⟶ Y)
    [HasCompactification a] (d : ℕ) : Prop :=
  ∃ (roots : ∀ n : ℕ, FiniteSmoothPurity.CoefficientLineComparison (quotient l n)
      (l ^ (n + 2)) (l ^ (n + 1)) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) X)
    (sheafReduction : ∀ n r : ℕ,
      (ProEtale.etaleSheafExtendScalars (quotient l n) X).obj (twist l (n + 1) X r) ≅
        twist l n X r),
    (∀ n : ℕ,
      FiniteSmoothPurity.scalarSingleMap (quotient l n) X (twist l (n + 1) X 0) ≫
          (_root_.DerivedCategory.singleFunctor _ 0).map (sheafReduction n 0).hom =
        (FiniteSmoothPurity.scalarZeroLineIso (quotient l n) (l ^ (n + 2)) (l ^ (n + 1))
          (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) X).hom) ∧
    (∀ n : ℕ, sheafReduction n 1 = (roots n).sheafIso) ∧
    (∀ n r : ℕ, HEq (sheafReduction n (r + 2)).hom
      (Functor.OplaxMonoidal.δ (ProEtale.etaleSheafExtendScalars (quotient l n) X)
          (twist l (n + 1) X (r + 1)) (twist l (n + 1) X 1) ≫
        tensorHom (sheafReduction n (r + 1)).hom (sheafReduction n 1).hom)) ∧
    (∀ n : ℕ, ∃ U : Scheme.Cover.{u} Scheme.etalePrecoverage X, ∀ i : U.I₀,
      Nonempty ((twist l n X d).over (U.etalePrecoverageToEtale i) ≅
        (constantSheaf (X.smallEtaleTopology.over (U.etalePrecoverageToEtale i))
          (ModuleCat.{u + 1} (FiniteReduction.Coeff l (n + 1)))).obj
            (ModuleCat.of (FiniteReduction.Coeff l (n + 1))
              (FiniteReduction.Coeff l (n + 1))))) ∧
    ∃ theta : ∀ n : ℕ,
        dualizingComplex (ModuleCat.{u + 1} (FiniteReduction.Coeff l (n + 1))) a ≅
          (twistComplex l n X d)⟦(2 * d : ℤ)⟧,
      (∀ n : ℕ, DerivedCategory.isBoundedConstructible
        (FiniteReduction.Coeff l (n + 1)) X
          (dualizingComplex (ModuleCat.{u + 1} (FiniteReduction.Coeff l (n + 1))) a)) ∧
      (∀ n : ℕ, IsIso
        (FiniteSmoothPurity.scalarSingleMap (quotient l n) X (twist l (n + 1) X d))) ∧
      ∀ n : ℕ,
        (scalarExtension (quotient l n) X).map (theta (n + 1)).hom ≫
            shiftedTwistReduction l n X d (sheafReduction n d) =
          dualizingReduction l n a ≫ (theta n).hom

/-- A nonempty irreducible finite-type scheme with regular reduction has normalized
finite dualizing complex Lambda(d)[2d], compatibly at every positive coefficient level.

Source: ILO XVII 2.4.4.1, 4.1.2 and Remark 4.1.3, 5.1.1, 6.2.2.1;
Bhatt--Scholze 6.7.20 (blueprint: lem-per-finite-regular-reduction-dualizing).

Proof plan:
1. Fields and finite-type algebras are excellent (lem-exc-fields-excellent,
lem-exc-finite-type-localization-excellent). Apply this to X and its reduction T.
Both are Noetherian; Nagata compactifies their structure maps (thm-nagata-compactification).
The reduction inclusion is proper (lem-weil-pbc-closed-immersion-proper). Dimension is
finite (lem-kun-dimension-finite-type), and pqf-lem-lft-fp-locnoeth gives finite presentation.
2. Use lem-asd-etale-finite-twist-pullback for the rank-one Tate lines, their pullback
under T -> X, and the generator-normalized root power maps at consecutive levels.
3. Irreducibility and lem-sc-dimension-locally-algebraic identify each local dimension
with d. By lem-kun-dimension-formula, d = dim O_(T,t) + trdeg_k kappa(t).
4. The coefficient unit at Spec k has its regular pinnings. By
lem-per-potential-dualizing-finite-pullback its exceptional pullback has dimension function
trdeg_k kappa(t). By lem-per-potential-dualizing-regular-unit, Lambda_T(d)[2d] has the
same pinnings for d - dim O_(T,t), with identity pinning at the generic point before twisting.
5. Apply lem-per-potential-dualizing-uniqueness to obtain the pinning-preserving
isomorphism on T, with bounded constructibility and finite Tor amplitude.
6. By thm-weil-pbc-universal-homeomorphism-invariance, reduction induces inverse exact
etale equivalences. Properness identifies its exceptional inverse image with ordinary
inverse image (def-amb-etale-compact-support, lem-amb-etale-compact-comparisons).
Full faithfulness lifts the isomorphism uniquely to X. On bounded constructible inputs,
Yoneda identifies this ambient exceptional image with the finite constructible adjoint
of lem-per-adic-exceptional-projection, with the same counit.
7. Apply lem-per-potential-dualizing-coefficient-tower: exceptional scalar reduction
preserves pinnings; uniqueness makes the square commute on T. Locally a generator zeta
of mu_(l^(n+2)) maps to zeta^l, a generator at the next level. Tensor powers give ordinary
reduction of all twists; local freeness eliminates higher Tor.
8. The identification of exceptional inverse image under reduction preserves pinnings
by transitivity. Thus its transported coefficient comparison equals the comparison on T
by uniqueness. Faithfulness of the etale equivalence carries the commuting square back
to X. Shifting by -2d gives precisely the ordinary sheaf tower. This uses no perfectness
or separable-generation hypothesis. -/
theorem finiteRegularReductionDualizing (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    [Fact (IsUnit (l : k))] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IrreducibleSpace X]
    (_hregular : IsRegularScheme X.nilradical.subscheme) :
    ∃ d : ℕ, topologicalKrullDim X = (d : WithBot ℕ∞) ∧
      Model l (X ↘ Spec (.of k)) d := by
  sorry

end AlgebraicGeometry.Etale.RegularReductionDualizing
