/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P7
-/
module

public import Sheaf.SixFunctors.FiniteDualizingData

/-! # Coherence of finite-coefficient realization restriction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (X : Scheme.{u})

/-- Realization identifies the canonical identity restriction maps.
Source: current blueprint, lem-coef-finite-dualizing.proof.md, final sentence;
the identity part of lem-coef-dualizing-scalar-realization, proof step 1
(blueprint: lem-coef-dualizing-realization-restriction-unit).

Proof: before deriving, the intrinsic comparison is fixed by its value on the
scalar-unit sections. For the identity ring map both paths act identically on
every such section, so the uniqueness in finiteDualizingRestriction_existsUnique
identifies them. The comparison-site restriction square has the same identity
normalization. Apply exact localization to these two commuting squares. The
identity constraint of mapDerivedCategory identifies localization of the ordinary
identity with normalizedDVRResUnit. Pasting the two localized squares gives the
displayed equality. This includes n = 0 (the first positive quotient), and the
identity ring or sheaf on the empty scheme requires no separate assumption. -/
theorem finiteDualizingRealizationRestriction_unit (n : ℕ)
    (K : Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) X) :
    (finiteDualizingRealizationRestriction l E X (le_refl n)).inv.app K ≫
        (normalizedDVRResUnit l E X n).hom.app
          ((finiteDualizingRealization l E X n).obj K) =
      (finiteDualizingRealization l E X n).map
        ((Functor.mapDerivedCategoryNatIso
          (ProEtale.normalizedOriginRestrictionUnit X.smallEtaleTopology _
            (finiteDualizingQuotient_id l E n)) ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app K) := by sorry

end WeilConjectures
