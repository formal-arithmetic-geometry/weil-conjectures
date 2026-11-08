/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import Submission.WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
import all Submission.WeilConjectures.AlgebraicGeometry.Standard.StandardQuotientsPerfectSupplement
import Mathlib.GroupTheory.OrderOfElement
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplete

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Bounded constructible derived-complete objects

Source: blueprint, proper base change, order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete).
The coefficient ring is the actual inverse limit. The three defining conditions
are properties; no origin, local model, or completion representative is retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 512
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
open ProEtale
variable (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A)

/-- The actual completed-coefficient ambient category. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
abbrev PbcCompletedDerived := DerivedCategory (pbcModules T (pbcAdicCompletion T d))

/-- Derived extension along the actual limit projection. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
abbrev pbcCompletedReduction (n : ℕ) := pbcDerivedExtend (pbcAdicProjection T d n)

/-- Constants mapped to the continuous-function coefficient presentation.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcFunctionScalars (n : ℕ) :
    (Functor.const T.ProEtᵒᵖ).obj (RingCat.of (PbcQuotient d n)) ⟶
      ((adicLisseForget T).obj ((pbcAdicRings T d).obj (op n))).obj :=
  finiteCoefficientScalarMap T (PbcQuotient d n) ≫
    (AdicCoefficients.finiteRingComparison T (PbcQuotient d n)).inv.hom

/-- The coefficient-presentation transport preserves local bijectivity of constants.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete).
Proof: finiteCoefficientScalarMap is locally bijective. The second factor is a ring
sheaf isomorphism, so composing it preserves local injectivity and local surjectivity. -/
theorem pbcFunctionScalars_locallyBijective (n : ℕ) :
    Presheaf.IsLocallyInjective (ProEt.topology T) (pbcFunctionScalars T d n) ∧
      Presheaf.IsLocallySurjective (ProEt.topology T) (pbcFunctionScalars T d n) := by
  dsimp only [pbcFunctionScalars]
  constructor <;> infer_instance

/-- Local injectivity of the specified coefficient presentation. Source: blueprint
order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
instance pbcFunctionScalars_injective (n : ℕ) :
    Presheaf.IsLocallyInjective (ProEt.topology T) (pbcFunctionScalars T d n) :=
  (pbcFunctionScalars_locallyBijective T d n).1

/-- Local surjectivity of the specified coefficient presentation. Source: blueprint
order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
instance pbcFunctionScalars_surjective (n : ℕ) :
    Presheaf.IsLocallySurjective (ProEt.topology T) (pbcFunctionScalars T d n) :=
  (pbcFunctionScalars_locallyBijective T d n).2

/-- Associated modules for any locally bijective coefficient presentation.
Keeping the presentation abstract avoids expanding the quotient limit during
normalization. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
def pbcAssociatedModule (P : Type (u + 1)) [CommRing P]
    (R : Sheaf (ProEt.topology T) RingCat.{u + 1})
    (α : (Functor.const T.ProEtᵒᵖ).obj (RingCat.of P) ⟶ R.obj)
    [Presheaf.IsLocallyInjective (ProEt.topology T) α]
    [Presheaf.IsLocallySurjective (ProEt.topology T) α] :
    Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P) ⥤ ringedSiteModules.{u + 1} R :=
  sheafToPresheaf _ _ ⋙ finiteCoefficientModulePresheaf T.ProEt P ⋙
    PresheafOfModules.sheafification α

/-- Canonical associated-module-sheaf realization, with the coefficient presentation
changed along the recorded isomorphism. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
abbrev pbcFunctionRealization (n : ℕ) :
    Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (PbcQuotient d n)) ⥤
      pbcModules T ((pbcAdicRings T d).obj (op n)) :=
  pbcAssociatedModule T (PbcQuotient d n)
    ((adicLisseForget T).obj ((pbcAdicRings T d).obj (op n)))
    (pbcFunctionScalars T d n)

/-- Realization is the canonical exact additive equivalence, including for zero rings.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete).
Proof: finiteRingComparison is fixed by the coefficient sheafification units.
Its composite with the constants map is locally bijective. Associated module
sheafification therefore has invertible unit and counit on module sheaves.
They identify the underlying sheaves and scalar actions. The equivalence is additive
sectionwise and hence preserves finite limits and colimits. -/
theorem pbcFunctionRealization_exact (n : ℕ) :
    (pbcFunctionRealization T d n).IsEquivalence ∧
      (pbcFunctionRealization T d n).Additive ∧
      PreservesFiniteLimits (pbcFunctionRealization T d n) ∧
      PreservesFiniteColimits (pbcFunctionRealization T d n) := by
  have : (pbcFunctionRealization T d n).IsEquivalence :=
    coefficientRealization_isEquivalence (ProEt.topology T) (PbcQuotient d n)
      ((adicLisseForget T).obj ((pbcAdicRings T d).obj (op n)))
      (pbcFunctionScalars T d n)
  exact ⟨this, Functor.additive_of_preserves_binary_products _, inferInstance, inferInstance⟩

/-- The canonical realization equivalence. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
instance pbcFunctionRealization_equivalence (n : ℕ) :
    (pbcFunctionRealization T d n).IsEquivalence :=
  (pbcFunctionRealization_exact T d n).1

/-- Exact realization, additive part. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
instance pbcFunctionRealization_additive (n : ℕ) :
    (pbcFunctionRealization T d n).Additive :=
  (pbcFunctionRealization_exact T d n).2.1

/-- Exact realization, left exact part. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
instance pbcFunctionRealization_limits (n : ℕ) :
    PreservesFiniteLimits (pbcFunctionRealization T d n) :=
  (pbcFunctionRealization_exact T d n).2.2.1

/-- Exact realization, right exact part. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
instance pbcFunctionRealization_colimits (n : ℕ) :
    PreservesFiniteColimits (pbcFunctionRealization T d n) :=
  (pbcFunctionRealization_exact T d n).2.2.2

/-- Realization on derived categories. Source: blueprint order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete). -/
abbrev pbcDerivedFunctionRealization (n : ℕ) :=
  (pbcFunctionRealization T d n).mapDerivedCategory

/-- The exact coefficient-presentation equivalence descends to an equivalence.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete).
Proof: apply the ordinary inverse equivalence termwise to cochain complexes.
Exactness preserves quasi-isomorphisms on both sides. Localize both functors and
the unit and counit, which remain isomorphisms and satisfy the triangle identities. -/
@[instance] theorem pbcDerivedFunctionRealization_equivalence (n : ℕ) :
    (pbcDerivedFunctionRealization T d n).IsEquivalence := by
  infer_instance

/-- Intrinsic completeness transported along the normalized completed-ring comparison.
The generator tuple and complex representative are existential proof witnesses only.
Source: blueprint order 1300 (blueprint: def-weil-pbc-bounded-constructible-complete). -/
def PbcIsIntrinsicallyComplete (K : PbcCompletedDerived T d) : Prop :=
  ∃ (r : ℕ) (f : Fin r → A) (hf : Ideal.span (Set.range f) = d.ideal)
    (C : CochainComplex (adicDatumModules T
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
        quotientFinite := d.quotientFinite }) ℤ)
    (e : (completedConstantQ _).obj C ≅
      (pbcDerivedExtend (pbcCompletedComparison T d).inv).obj K),
    IsCompletedIntrinsicallyDerivedComplete T
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum,
        quotientFinite := d.quotientFinite } r f hf C e

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
variable [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.Scheme
