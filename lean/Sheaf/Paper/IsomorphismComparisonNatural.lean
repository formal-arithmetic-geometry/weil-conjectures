/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q119
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Naturality of the specified inverse-image comparison

Source: Deligne, Weil II, (1.1.3), p. 150 and (1.1.7), pp. 150--151;
the explicit pro-etale/completed argument is agent-written, extracted from
`lem-weil-frobenius-point-transport-natural`, steps 3--6 and 9
(blueprint: lem-weil-isomorphism-comparison-natural).

The finite comparison is fixed on every complex by the recorded tensor-unit map.
The integral comparison is the recorded chosen-resolution map, on every ambient
object, and agrees with the actual completion unit through the normalization
isomorphism. Both natural transformations can be postcomposed with any functor
and preceded by any natural transformation. The finite index `n` means exponent `n+1`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u r s

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilConjectures

/-- The finite tensor-unit components descend to one natural transformation on the
entire unbounded derived category, and remain natural after the stated composition.
Source: Deligne, Weil II, (1.1.3), (1.1.7), as motivation; the explicit argument uses
Stacks Tags 03D6, 03EK and 04VG
(blueprint: lem-weil-isomorphism-comparison-natural).

Proof, node steps 1, 2 and 5: on every site object and in each degree, the two
composites send x to g⁻¹(v)(x) tensor 1. This respects restrictions, differentials
and the action transported through c_A inverse. The tensor universal property and
sheafification adjunction identify the sheaf maps (def-pur-sheaf-tensor-product,
def-weil-pbc-sheafification). Both functors are exact
(prop-weil-pbc-proetale-constant-exact), so preserve quasi-isomorphisms. Apply
lem-weil-pbc-localization-universal-property (2) with the exact-functor factorization
isomorphisms to descend this precise transformation. The component equality below
fixes it on every complex. Naturality for an inverted quasi-isomorphism follows by
multiplying the chain-map square by the two inverses; localization supplies the
square for every derived morphism, without a boundedness condition. Finally take
η = ρ followed by the right whiskering of κ with S: functoriality of S and the
naturality of κ and ρ give the required component square. -/
theorem inverseImagePullbackComparisonFinite_natural
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) (n : ℕ) :
    ∃ κ : inverseImageFiniteDerived l E g n ⟶
        (integralOperationsLevelPullback l E g n).mapDerivedCategory,
      (∀ K : CochainComplex (integralOperationsFiniteModules l E Y n) ℤ,
        κ.app (DerivedCategory.Q.obj K) =
          inverseImagePullbackComparisonFinite l E g hX hY n K) ∧
      (∀ (T : Type r) [Category.{s} T]
        (S : DerivedCategory (integralOperationsFiniteModules l E X n) ⥤ T)
        (H : DerivedCategory (integralOperationsFiniteModules l E Y n) ⥤ T)
        (ρ : H ⟶ inverseImageFiniteDerived l E g n ⋙ S),
        ∃ η : H ⟶ (integralOperationsLevelPullback l E g n).mapDerivedCategory ⋙ S,
          ∀ N : DerivedCategory (integralOperationsFiniteModules l E Y n),
            η.app N = ρ.app N ≫ S.map (κ.app N)) := by
  sorry

/-- The specified ambient integral components are natural, independent of the
chosen flat-term K-flat resolutions, and are the inverse normalization followed
by inverse image of the actual completion unit. They remain natural after the
stated composition, including on incomplete objects.
Source: Deligne, Weil II, (1.1.3), (1.1.7), as motivation; blueprint
`sec-trace-formula/sk-d-weil/prop-trf-rational-frobenius-integral-model.proof.md`,
clauses (2)--(3), through the agent-written entire-cone normalization
(blueprint: lem-weil-isomorphism-comparison-natural).

Proof, node steps 3--5: apply
lem-weil-isomorphism-derived-pullback-comparison-normalization to the canonical
calculus S of lem-coef-derived-system-evaluation-calculus. Its entire-cone identity
is κ_N followed by θ_N = G(u_N), with zero shifted coordinate, for every ambient
N and under the canonical resolution comparisons. Thus κ_N = G(u_N) followed by
θ_N inverse. The completion is S.reduction followed by coefficientSequenceLimit,
and u is the actual adjunction unit. For v : N → N', unit naturality gives
completion(v) u_N = u_N' v. Naturality of θ therefore identifies θ_N' P_g(v) κ_N
with G(completion(v)) G(u_N), hence with θ_N' κ_N' G(v). Cancel θ_N' to obtain
naturality of the specified κ. No inverse of u_N is used. The same normalization
and the canonical representative comparisons identify the chosen derived component
with inverseImagePullbackComparison for every good resolution q : P → K.
Finally η = ρ followed by the right whiskering of κ with S has components
ρ_N followed by S(κ_N), and its naturality is the composite of the two squares. -/
theorem inverseImagePullbackComparisonIntegral_natural
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    ∃ κ : inverseImageIntegralDerived l E g ⟶ integralDerivedPullback l E g,
      (∀ N : DerivedCategory (integralTowerModules l E Y),
        κ.app N = inverseImagePullbackComparisonDerived l E g hX hY N) ∧
      (∀ (K : CochainComplex (integralTowerModules l E Y) ℤ)
        (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (q : P.obj ⟶ K) [QuasiIso q],
        κ.app (DerivedCategory.Q.obj K) =
          inverseImagePullbackComparison l E g hX hY K P q) ∧
      (∀ (C : CoefficientDerivedSystemCalculus l E Y),
        Nonempty (CoefficientDerivedSystemCoherence l E Y C) →
        ∃ θ : integralDerivedPullback l E g ≅
            (C.reduction ⋙ coefficientSequenceLimit l E Y) ⋙
              inverseImageIntegralDerived l E g,
          ∀ N : DerivedCategory (integralTowerModules l E Y),
            κ.app N = (inverseImageIntegralDerived l E g).map (C.adjunction.unit.app N) ≫
              θ.inv.app N) ∧
      (∀ (T : Type r) [Category.{s} T]
        (S : DerivedCategory (integralTowerModules l E X) ⥤ T)
        (H : DerivedCategory (integralTowerModules l E Y) ⥤ T)
        (ρ : H ⟶ inverseImageIntegralDerived l E g ⋙ S),
        ∃ η : H ⟶ integralDerivedPullback l E g ⋙ S,
          ∀ N : DerivedCategory (integralTowerModules l E Y),
            η.app N = ρ.app N ≫ S.map (κ.app N)) := by
  sorry

end WeilConjectures
