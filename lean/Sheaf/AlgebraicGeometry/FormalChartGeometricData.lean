/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.RingTheory.FormalMonoidExtensionModel
public import Sheaf.RingTheory.CompleteToricModel
public import Sheaf.AlgebraicGeometry.LogRegularPair
public import Sheaf.TraceFormula.ChartFaceResidualUnitDecomposition
public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Sheaf.AlgebraicGeometry.IsRegularScheme

/-!
# Notation for formal chart geometric regularity

Canonical ring maps and the two completion predicates, extracted without changing
any definition from `FormalChartGeometricRegularity`.
Source: ILO VI 1.6 and 1.8; Stacks 04HX and 04GP
(blueprint: def-trf-formal-chart-geometric-data).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry
namespace FormalChartGeometric

/-- The map of integral toric schemes induced by the given chart homomorphism.
Source: ILO VI 1.8 (blueprint: def-trf-formal-chart-geometric-data). -/
noncomputable abbrev toricMap {R Q : Type u} [CommMonoid R] [CommMonoid Q]
    (h : R →* Q) :
    Spec (.of (MonoidAlgebra ℤ Q)) ⟶ Spec (.of (MonoidAlgebra ℤ R)) :=
  Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ h))

/-- The chart base change, with the factor order used in the node.
Source: ILO VI 1.8 (blueprint: def-trf-formal-chart-geometric-data). -/
noncomputable abbrev chartScheme {W : Scheme.{u}} {R Q : Type u}
    [CommMonoid R] [CommMonoid Q]
    (y : W ⟶ Spec (.of (MonoidAlgebra ℤ R))) (h : R →* Q) :=
  pullback y (toricMap h)

/-- The canonical affine-neighbourhood strict henselization of the base point.
Source: Stacks 04HX and 04GP (blueprint: def-trf-formal-chart-geometric-data). -/
noncomputable abbrev baseRing {W : Scheme.{u}} {R Q : Type u}
    [CommMonoid R] [CommMonoid Q]
    (y : W ⟶ Spec (.of (MonoidAlgebra ℤ R))) (h : R →* Q)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ chartScheme y h) :=
  Scheme.strictHenselization (z ≫ pullback.fst y (toricMap h))

/-- Its canonical structural morphism to the base scheme.
Source: Stacks 04HX (blueprint: def-trf-formal-chart-geometric-data). -/
noncomputable abbrev baseMap {W : Scheme.{u}} {R Q : Type u}
    [CommMonoid R] [CommMonoid Q]
    (y : W ⟶ Spec (.of (MonoidAlgebra ℤ R))) (h : R →* Q)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ chartScheme y h) :=
  Scheme.strictLocalizationToBase (z ≫ pullback.fst y (toricMap h))

/-- The chart on the strict base ring, obtained from the actual toric scheme map.
Source: ILO VI 1.6 (blueprint: def-trf-formal-chart-geometric-data). -/
noncomputable def alpha {W : Scheme.{u}} {R Q : Type u}
    [CommMonoid R] [CommMonoid Q]
    (y : W ⟶ Spec (.of (MonoidAlgebra ℤ R))) (h : R →* Q)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ chartScheme y h) :
    R →* baseRing y h z :=
  (Spec.preimage (baseMap y h z ≫ y)).hom.toMonoidHom.comp (MonoidAlgebra.of ℤ R)

/-- The canonical integral monoid-algebra map into the tensor ring.
Source: ILO VIII 3.1.2 (blueprint: def-trf-formal-chart-geometric-data). -/
noncomputable def tensorRight {A R Q : Type u} [CommRing A] [CommMonoid R] [CommMonoid Q]
    (α : R →* A) (h : R →* Q) : MonoidAlgebra ℤ Q →+* Algebra.monoidChartTensor α h :=
  by
    letI := (MonoidAlgebra.lift ℤ A R α).toRingHom.toAlgebra
    letI := (MonoidAlgebra.mapDomainRingHom ℤ h).toAlgebra
    exact (Algebra.TensorProduct.includeRight (R := MonoidAlgebra ℤ R)
      (A := A) (B := MonoidAlgebra ℤ Q)).toRingHom

/-- The rational rank of the group completion of the sharp target chart.
Source: ILO VI 1.2 (blueprint: def-trf-formal-chart-geometric-data). -/
noncomputable abbrev rank (T : Type u) [CommMonoid T] : WithBot ℕ∞ :=
  (Cardinal.toENat (Module.rank ℚ
    (TensorProduct ℤ ℚ (Additive (Algebra.GrothendieckGroup T)))) : WithBot ℕ∞)

/-- Exactly the two monomial-compatible completion hypotheses. `false` is the
residue-field case; `true` is the Cohen hypersurface case, including its residue
field identification and the full congruence modulo monomials AND parameters.
Source: ILO VI 1.6(i)--(ii) (blueprint: def-trf-formal-chart-geometric-data). -/
def HasCompletion (A : Type u) [CommRing A] [IsLocalRing A]
    {R : Type u} [CommMonoid R] (α : R →* A)
    (a : Multiplicative (Algebra.chartSharpMonoid α) →* A) (mixed : Bool) : Prop :=
  match mixed with
  | false => ∃ (n : ℕ)
      (e : ToricMonoid.Complete (IsLocalRing.ResidueField A)
        (Algebra.chartSharpMonoid α) n ≃+* AdicCompletion (IsLocalRing.maximalIdeal A) A),
      ∀ s : Algebra.chartSharpMonoid α,
        e (algebraMap (MvPolynomial (Fin n)
            (AddMonoidAlgebra (IsLocalRing.ResidueField A) (Algebra.chartSharpMonoid α))) _
          (MvPolynomial.C (AddMonoidAlgebra.single s (1 : IsLocalRing.ResidueField A)))) =
          algebraMap A _ (a (Multiplicative.ofAdd s))
  | true => ∃ (V : Type u) (_ : CommRing V) (_ : IsLocalRing V) (p : ℕ),
      IsCohenRing p V ∧
      Nonempty (IsLocalRing.ResidueField V ≃+* IsLocalRing.ResidueField A) ∧
      ∃ (n : ℕ) (θ : ToricMonoid.Complete V (Algebra.chartSharpMonoid α) n),
        θ - (p : ToricMonoid.Complete V (Algebra.chartSharpMonoid α) n) ∈
          ToricMonoid.completedChartIdeal V (Algebra.chartSharpMonoid α) n ∧
        ∃ e : (ToricMonoid.Complete V (Algebra.chartSharpMonoid α) n ⧸
            Ideal.span {θ}) ≃+* AdicCompletion (IsLocalRing.maximalIdeal A) A,
          ∀ s : Algebra.chartSharpMonoid α,
            e (Ideal.Quotient.mk (Ideal.span {θ})
              (algebraMap (MvPolynomial (Fin n)
                  (AddMonoidAlgebra V (Algebra.chartSharpMonoid α))) _
                (MvPolynomial.C (AddMonoidAlgebra.single s (1 : V))))) =
                algebraMap A _ (a (Multiplicative.ofAdd s))

/-- The completed pair and its two dimensions, retaining one and the same coefficient
ring `D` throughout. Dimension drops use addition of `e` to avoid truncated subtraction.
Source: ILO VI 1.6, with the formal-model refinement and Stacks 07NV
(blueprint: def-trf-formal-chart-geometric-data). -/
def ModelDimensions (B : Type u) [CommRing B] [IsLocalRing B]
    (T : Type u) [CommMonoid T] (J : Ideal B) (mixed : Bool) : Prop :=
  ∃ (D : Type u) (_ : CommRing D) (_ : Nontrivial D) (_ : IsRegularLocalRing D),
    IsAdicComplete (IsLocalRing.maximalIdeal D) D ∧
    IsRegularRing (AdicCompletion (IsLocalRing.maximalIdeal B) B ⧸
      J.map (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B))) ∧
    (match mixed with
    | false => ∃ e : AdicCompletion (IsLocalRing.maximalIdeal B) B ≃+*
          ToricMonoid.Complete D (Additive T) 0,
        (J.map (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B))).map e.toRingHom =
          ToricMonoid.completedChartIdeal D (Additive T) 0
    | true => ∃ (η : ToricMonoid.Complete D (Additive T) 0)
        (ρ : (ToricMonoid.Complete D (Additive T) 0 ⧸
          ToricMonoid.completedChartIdeal D (Additive T) 0) ≃ₐ[D] D),
        ρ (Ideal.Quotient.mk _ η) ∈ IsLocalRing.maximalIdeal D ∧
        ρ (Ideal.Quotient.mk _ η) ∉ (IsLocalRing.maximalIdeal D) ^ 2 ∧
        ∃ e : AdicCompletion (IsLocalRing.maximalIdeal B) B ≃+*
            (ToricMonoid.Complete D (Additive T) 0 ⧸ Ideal.span {η}),
          (J.map (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B))).map e.toRingHom =
            (ToricMonoid.completedChartIdeal D (Additive T) 0).map
              (Ideal.Quotient.mk (Ideal.span {η}))) ∧
    ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal B) B) +
      (if mixed then 1 else 0) = ringKrullDim D + rank T ∧
    ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal B) B ⧸
      J.map (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B))) +
        (if mixed then 1 else 0) = ringKrullDim D

/-- The canonical ring map into the affine strict localization.
Source: Stacks 04HX (blueprint: def-trf-formal-chart-geometric-data). -/
noncomputable def strictBase {B : Type u} [CommRing B]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of B)) :
    B →+* Scheme.strictHenselization t :=
  (Spec.preimage (Scheme.strictLocalizationToBase t)).hom

/-- The nonunit ideal after strict henselization, using the actual canonical ring map.
Source: ILO VI 1.2 and Stacks 05WS
(blueprint: def-trf-formal-chart-geometric-data). -/
noncomputable abbrev strictIdeal {B : Type u} [CommRing B]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of B))
    (J : Ideal B) := J.map (strictBase t)

end FormalChartGeometric
end AlgebraicGeometry
