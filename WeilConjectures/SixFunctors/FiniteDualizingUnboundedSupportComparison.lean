/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingSystemTraceData

/-! # Unbounded compact-support comparison with fixed finite counit

Source: prop-coef-integral-dualizing.proof.md, paragraph 2; unbounded direct-image
comparison over an algebraic closure of a finite field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

include hl in
/-- The compact-support comparison extends to every unbounded etale input and has
exactly the counit normalization used by the finite dualizing system.
Source: prop-coef-integral-dualizing.proof.md, paragraph 2, site comparison;
Stacks 09AF and 099R; unbounded direct-image comparison
(blueprint: lem-coef-finite-dualizing-unbounded-support-comparison).

Proof: express compact support as exact extension by zero followed by proper
right derived direct image. The exact open site comparison is unbounded. For the
proper factor apply unboundedDirectImageComparison over D.k: both schemes are
finite type over the algebraically closed field and the finite coefficient ring
is l-primary. The canonical mate is therefore invertible on every complex, and
its naturality assembles the proper comparison isomorphism. Compose with the
open comparison and the intrinsic module realization equivalences to obtain beta.
On a bounded below input the total derived mate is the included bounded below
mate: apply the pullback adjunction, use derivedPlus/total counit compatibility,
and cancel the common pullback isomorphism. The same statement for exact open
extension is termwise localization compatibility. Thus beta at the bounded below
etale dualizing object is the specified compactSupportSiteComparison followed by
the intrinsic comparison. Expanding integralDualizingFiniteSystemCounit gives the
stated equation after composing the fixed origin inverse and etale counit.
This works also for zero inputs and empty schemes. -/
theorem integralDualizingFiniteSupport_unboundedComparison (n : ℕ) :
    ∃ β : finiteDualizingRealization l E X n ⋙
        sfIntrinsicCompactSupport (finiteDualizingCompactification D X)
          (Padic.coefficientExtensionRing l E (n + 1)) ≅
      finiteDualizingEtaleSupport l E D X n ⋙
        finiteDualizingRealization l E (Spec (.of D.k)) n,
      (sfIntrinsicCompactSupport (finiteDualizingCompactification D X)
        (Padic.coefficientExtensionRing l E (n + 1))).map
          (finiteDualizingOrigin l E D X n).inv ≫
        β.hom.app (finiteDualizingEtaleTerm l E D X n) ≫
        (finiteDualizingRealization l E (Spec (.of D.k)) n).map
          (finiteDualizingEtaleCounit l E D X n) =
        integralDualizingFiniteSystemCounit D l E X n := by
  sorry

end WeilConjectures
