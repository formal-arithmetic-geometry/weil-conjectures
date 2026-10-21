/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.Paper.RationalModuleRealizationFunctor
public import Sheaf.CategoryTheory.ScalarLocalizationDerivedHom
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Linear.Basic
import Sheaf.Paper.IntegralConstructibleHomSums
import Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization

/-!
# Constructible rational Hom comparison

Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61--62
(blueprint: lem-per-constructible-rational-hom-comparison).

The completed integral category and the realization, including its normalized coefficient
maps, are the published ones. The general scalar-localization comparison predicate includes
all fraction, naturality, identity, composition and simultaneous-shift equations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (X : Scheme.{u}) [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- Restrict the realization's normalized constant field action along the canonical
identification of the localized valuation ring with E. This constructs only the scalar
structure required to apply the existing localized-Hom comparison predicate.
Source: Bhatt--Scholze, Proposition 6.8.14(2)
(blueprint: lem-per-constructible-rational-hom-comparison). -/
@[instance_reducible]
def rationalRealizationLocalizedLinear (R : RationalModuleRealization l E X) :
    Linear (Localization.Away (pbcUniformizer l E))
      (DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E))) :=
  letI := R.moduleLinear
  letI : Linear E (DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E))) :=
    inferInstance
  { homModule := fun M N ↦
      Module.compHom (M ⟶ N) (pbcRationalCoefficientEquiv l E).toRingHom
    smul_comp := fun M N P a f g ↦
      Linear.smul_comp M N P (pbcRationalCoefficientEquiv l E a) f g
    comp_smul := fun M N P f a g ↦
      Linear.comp_smul M N P f (pbcRationalCoefficientEquiv l E a) g }

/-- Specialize the existing fraction-normalized comparison to completed integral objects
and the actual derived scalar extension of a rational module realization. The existential
shift structure expresses commutation with shifts for this derived functor; the predicate
records the shift comparison explicitly in its fraction and compatibility formulas.
Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2)
(blueprint: lem-per-constructible-rational-hom-comparison). -/
def ConstructibleRationalHomComparison (R : RationalModuleRealization l E X) : Prop :=
  (fun [_localizedLinear : Linear (Localization.Away (pbcUniformizer l E))
      (DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E)))] ↦
    ∃ (_shift : (pbcDerivedExtend (R.integralIso.hom ≫ R.inclusion)).CommShift ℤ),
      scalarLocalizationHomComparison (PbcIntegralRing l E) (pbcUniformizer l E)
        (pbcDerivedExtend (R.integralIso.hom ≫ R.inclusion))
        (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E))
        (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)))
    (_localizedLinear := rationalRealizationLocalizedLinear l E X R)

open Classical in
/-- Constructible completed integral objects satisfy the countable, uniformly bounded-below
coproduct-Hom comparison. Actual scalar extension therefore identifies every localized
shifted Hom with its rational ambient Hom, naturally and compatibly with identities,
composition and shifts. The specified realization of the raw rationalization is full
and faithful into the actual ambient derived category.

Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61--62
(blueprint: lem-per-constructible-rational-hom-comparison).

Proof, following the node's four steps:
1. Use the coefficient identification of lem-per-rational-module-realization-functor.
Apply lem-weil-pbc-integral-constructible-hom-sums to K and the countable family,
with its common lower bound. Its shifted coprojection map is precisely the displayed
DirectSum.toModule map. This is the passage from the global-derived-Hom continuity
of lem-weil-pbc-integral-constructible-bounded-below-compactness to ordinary Hom.
2. Apply lem-weil-pbc-integral-stratified-perfect-characterization to L. Membership
in the integral category, including compatible etale origins, implies boundedness
and hence boundedness below. Its closure statement also retains all shifts.
3. Apply lem-weil-pbc-scalar-localization-derived-hom with the completed coefficient
ring sheaf, constant uniformizer and actual localization functor. Step 1 verifies
its Hom-coproduct hypothesis; step 2 verifies its target lower-bound hypothesis.
The coefficient identifications and K-flat comparison of the realization identify
its exact scalar localization with E_X tensor^L over B_X. Transport the comparison
along those identifications and the canonical localized-ring equivalence with E.
4. The fraction formula sends f/varpi^n to varpi^(-n) F(f), followed by the shift
comparison. Functoriality and linear composition give naturality, identities and
composition on fractions; the derived shift comparison gives simultaneous shifts.
Every localized morphism is a fraction, so these identities cover every morphism.
At q=0 the comparisons are the Hom maps of R.J by its objects and fractions fields.
The integral subcategory is full and raw rationalization has exactly its localized
Hom modules, proving that R.J is full and faithful. -/
theorem constructibleRationalHomComparison :
    (∀ (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l E))
      (I : Type (u + 1)) [Countable I]
      (M : I → PbcCompletedDerived X (pbcIntegralDatum l E)),
      (∃ n : ℤ, ∀ i : I, (M i).IsGE n) →
      ∀ (q : ℤ) (s : Cofan M), IsColimit s →
        Function.Bijective
          (DirectSum.toModule (PbcIntegralRing l E) I (K.obj ⟶ s.pt⟦q⟧)
            (fun i : I ↦ Linear.rightComp (PbcIntegralRing l E) K.obj
              ((shiftFunctor (PbcCompletedDerived X (pbcIntegralDatum l E)) q).map
                (s.inj i))))) ∧
    ∀ R : RationalModuleRealization l E X,
      ConstructibleRationalHomComparison l E X R ∧ R.J.Full ∧ R.J.Faithful := by
  sorry

end AlgebraicGeometry.Scheme
