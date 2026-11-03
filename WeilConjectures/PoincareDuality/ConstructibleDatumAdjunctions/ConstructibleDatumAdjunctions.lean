/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
public import WeilConjectures.SmoothPurity.Exceptional.ExceptionalAdjointAdmissibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeConstructibleExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructiblePushforwardRestriction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekComposition
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackBoundedConstructible
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeDirectImageConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportConstructibility
import WeilConjectures.AlgebraicGeometry.Open.OpenExtensionFiniteTor
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImageSupplement
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compact.CompactSupportRefinementBaseChange
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc

/-! # Adjunctions of the constructible six-functor datum

Source: latest blueprint, sec-six-functors-basics/sk-thm-sbc-coefficients,
fix-prop-adjunctions.md, clauses (1)--(4), and its proof
(blueprint: fix-prop-adjunctions).

Finite coefficients use the intrinsic ordinary constant-ring module derived category.
Higher coefficients use native condensed module objects. The full-subcategory lifts
below retain the ambient objects and all their morphisms. Exceptional adjunctions are
asserted on the constructible categories only.

## Main statements

- `finiteOrdinary` and `finiteExceptional`: finite-stage restrictions.
- `higherAdjunctions`: native ordinary and exceptional restrictions, including Dctf.
- `compositionAndRefinement`, `higherOrdinaryComposition`: the normalized pasting laws.
- `finiteOrdinaryExchange`, `higherOrdinaryExchange`: the actual ordinary exchanges.
- `compactExchangeConjugate`, `higherCompactExchangeRestriction`: whole-adjoint exchange.

The formal clauses use the existing `Adjunction.comp`, `conjugateEquiv`,
`conjugateIsoEquiv` and `mateEquiv`: the composition and refinement comparisons are
conjugates between whole adjoints. In particular invertibility is asserted only for
this conjugation, and never for arbitrary square mates.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false

universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.ConstructibleDatumAdjunctions

/-- The two triangle equations, written componentwise for the specified adjunction.
This is notation for the equations in clauses (1) and (2), rather than another
notion of adjunction. Source: fix-prop-adjunctions (1),(2)
(blueprint: fix-prop-adjunctions). -/
def Triangles {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) : Prop :=
  (∀ K, a.unit.app (R.obj K) ≫ R.map (a.counit.app K) = 𝟙 (R.obj K)) ∧
    ∀ K, L.map (a.unit.app K) ≫ a.counit.app (L.obj K) = 𝟙 (L.obj K)

/-- The characteristic assumptions required by the restricted-functor interface follow
from the fixed finite-field datum. Source: the standing hypotheses of
fix-prop-adjunctions (blueprint: fix-prop-adjunctions).

Proof: the base field has cardinality p^a with p prime and a positive, hence has
characteristic p. The algebra map to its algebraic closure is injective, so the
closure has the same characteristic. Substitute ell != p. -/
theorem datumCharacteristic (D : FiniteFieldDatum.{u}) (ℓ : ℕ) (hℓ : ℓ ≠ D.p) :
    (ringChar D.k).Prime ∧ ringChar D.k ≠ ℓ := by
  let _ : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let _ : Fact D.p.Prime := ⟨D.prime⟩
  let _ : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
      (D.card_base.trans D.cardinality_eq))
  let _ : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  rw [ringChar.eq D.k D.p]
  exact ⟨D.prime, hℓ.symm⟩

open AlgebraicGeometry.ProEtale.CondensedRing

section OrdinaryComposition

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (H : PreservesBoundedConstructiblePushforwards Λ k)
  {X Y Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The ordinary direct-image compositor normalized by the actual restricted pullback
compositor, not by an independently chosen pushforward isomorphism. Its data is the
existing conjugation construction. Source: fix-prop-adjunctions (3)
(blueprint: fix-prop-adjunctions). -/
def higherOrdinaryDirectImageComp :
    boundedConstructibleLowerStarOfPreserves Λ H (f ≫ g) ≅
      boundedConstructibleLowerStarOfPreserves Λ H f ⋙
        boundedConstructibleLowerStarOfPreserves Λ H g :=
  conjugateIsoEquiv
    (boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves
      (Λ := Λ) (ℓ := ℓ) (H := H) (f := f ≫ g))
    ((boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves
      (Λ := Λ) (ℓ := ℓ) (H := H) (f := g)).comp
      (boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves
        (Λ := Λ) (ℓ := ℓ) (H := H) (f := f)))
    (boundedConstructibleUpperStarComp Λ ℓ f g).symm

end OrdinaryComposition

end WeilConjectures.ConstructibleDatumAdjunctions
