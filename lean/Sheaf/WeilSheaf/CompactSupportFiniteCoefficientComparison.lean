/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Constant
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.CommonStageCompactWeilCohomology
import Sheaf.Paper.ConstantCoefficientScalarNormalization
import Sheaf.Paper.ConstantWeilStructure
import Sheaf.Paper.FiniteCoefficientPoint
import Sheaf.Paper.FiniteCompactSupportConstructibility
import Sheaf.Paper.FiniteMittagLeffler
import Sheaf.Paper.QcqsCompactSupportRealization

/-!
# A finite-coefficient comparison for compactly supported constant cohomology

Source: Bhatt--Scholze, The pro-etale topology for schemes, §§6.5, 6.7, 6.8;
Milne, Lectures on Etale Cohomology, §§18--19.
(blueprint: lem-pod-compact-support-finite-coefficient-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (.of k₀))]
  [IsSeparated (X ↘ Spec (.of k₀))] [QuasiCompact (X ↘ Spec (.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of k₀))]

/-- The finite-coefficient group `H_c^r(X ⊗ k̄, ℤ/ℓ^(n+1))`, regarded as a `ℤ_ℓ`-module.

At the algebraically closed point, global sections are exact, so taking sections of the
cohomology sheaf of `Ra_!` computes compactly supported cohomology. The positive levels are
indexed by `n + 1`. Restriction of scalars uses reduction `ℤ_ℓ → ℤ/ℓ^(n+1)`.
(blueprint: lem-pod-compact-support-finite-coefficient-comparison). -/
noncomputable def finiteLevelCompactSupportSections (n : ℕ) (r : ℤ) :
    ModuleCat.{u + 1} (PadicInt l) :=
  let Λ := ULift.{u + 1} (ZMod (l ^ (n + 1)))
  let f := (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure
  haveI : HasCompactification f := by
    dsimp only [f, Scheme.Hom.geometricFiberToAlgebraicClosure]
    infer_instance
  let ρ : PadicInt l →+* Λ :=
    ULift.ringEquiv.symm.toRingHom.comp (PadicInt.toZModPow (n + 1))
  (ModuleCat.restrictScalars ρ).obj
    ((Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).obj
      ((DerivedCategory.homologyFunctor _ r).obj
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj
          ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)))))

/-- Constant adic compactly supported cohomology embeds into the scalar extension of the
product of its finite-coefficient groups. There is no dimension or degree restriction.

Source: Bhatt--Scholze, Lemmas 6.1.13, 6.5.8--6.5.9, 6.7.7, Proposition 6.8.14,
and Remark 6.8.15;
Milne, Lectures on Etale Cohomology, §18 and Theorems 19.1--19.2.
(blueprint: lem-pod-compact-support-finite-coefficient-comparison).

Proof: Use the canonical refinement comparisons to work with the same compactification
of the geometric structure morphism at every coefficient stage. Put
`C = RΓ(bar X, j_! ℤ_ℓ)` on the pro-etale site. Here `j_!` commutes with homotopy
limits (Lemma 6.1.13) and preserves constructibility (Lemma 6.5.8), so the constant lattice
and its extension by zero are derived complete. The finite-level comparison identifies `C`
with `R lim_n RΓ(bar X_et, j_! ℤ/ℓ^(n+1))`. The groups at every finite
level are finite, by constructible torsion finiteness on the proper compactification.
Consequently their inverse systems are Mittag--Leffler: the images in each finite group
stabilize. The Milnor exact sequence has zero `lim¹` term, giving
`H^r(C) ≅ lim_n H_c^r(X ⊗ k̄, ℤ/ℓ^(n+1))` as `ℤ_ℓ`-modules. The limit is a submodule of the
product appearing here. Coefficient extension identifies the source with
`ℚ̄_ℓ ⊗[ℤ_ℓ] H^r(C)`: first invert `ℓ`, then extend the field, using the constant integral
lattice. Both extensions are flat, so tensoring the inclusion of the limit into the product
is injective. Compose it with this coefficient comparison. Forgetting the Weil structure
identifies the source with the ordinary constant adic cohomology used in this calculation;
no Frobenius compatibility of the embedding is required. The empty scheme and negative
degrees give zero groups on both sides by the same construction. -/
theorem exists_injective_compactSupportFiniteCoefficientComparison (r : ℤ) :
    ∃ f : ((adicConstant k₀ l X).compactlySupportedCohomology r).carrier →ₗ[PadicAlgCl l]
        PadicAlgCl l ⊗[PadicInt l]
          (∀ n, finiteLevelCompactSupportSections (k₀ := k₀) l X n r),
      Function.Injective f := by sorry

end AlgebraicGeometry.WeilSheaf
