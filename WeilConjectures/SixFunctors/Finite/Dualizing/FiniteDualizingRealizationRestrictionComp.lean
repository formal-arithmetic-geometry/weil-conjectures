/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData
import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingIntrinsicRestrictionComp
import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingRestrictionTransport

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

/-- Realization identifies the canonical successive-restriction maps.
Source: current blueprint, lem-coef-finite-dualizing.proof.md, final sentence;
the composition part of lem-coef-dualizing-scalar-realization, proof step 1
(blueprint: lem-coef-dualizing-realization-restriction-comp).

Proof: restriction before localization leaves underlying sections unchanged and
precomposes their scalar action with the quotient. Thus the two successive
section-normalized intrinsic comparisons and the comparison for the composite
have equal values on every scalar-unit section. The actual quotient composition
identity identifies their scalar actions. The uniqueness theorem for the intrinsic
comparison gives equality of these ordinary squares. The comparison-site
restriction square satisfies the same pasting identity by conjugation of ordinary
restriction. Exact localization preserves the pasting identity, with
mapDerivedCategoryCompIso accounting for successive derived restrictions.
Pasting the intrinsic and comparison-site identities, and evaluating at K, gives
the displayed equation, with the inverse compositors because both paths go from
the direct restriction to the iterated one. Repeated levels satisfy the same
calculation, without quotient flatness or finiteness conditions on K. -/
theorem finiteDualizingRealizationRestriction_comp
    {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m)
    (K : Etale.DerivedCategoryModule (finiteDualizingCoeff l E n) X) :
    (finiteDualizingRealizationRestriction l E X (hmn.trans hrm)).inv.app K ≫
        (normalizedDVRResComp l E X hrm hmn).inv.app
          ((finiteDualizingRealization l E X n).obj K) =
      (finiteDualizingRealization l E X r).map
        ((Sheaf.derivedRestrictScalarsCompIso X.smallEtaleTopology
          (finiteDualizingQuotient_comp l E hrm hmn)).inv.app K) ≫
        (finiteDualizingRealizationRestriction l E X hrm).inv.app
          ((Sheaf.derivedRestrictScalars X.smallEtaleTopology
            (finiteDualizingQuotient l E hmn)).obj K) ≫
        (normalizedDVRRes l E X hrm).map
          ((finiteDualizingRealizationRestriction l E X hmn).inv.app K) := by
  unfold finiteDualizingRealizationRestriction
  dsimp only [finiteDualizingRealization]
  simp only [Functor.comp_obj, Iso.trans_inv, Functor.isoWhiskerRight_inv,
    Iso.symm_inv, Category.assoc, Functor.isoWhiskerLeft_inv, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.comp_id, Category.id_comp, Functor.comp_map,
    Functor.map_comp]
  let Cn := ProEtale.comparisonUpperStar
    (ModuleCat (finiteDualizingCoeff l E n)) X
  let CK := Cn.mapDerivedCategory.obj K
  rw [finiteDualizingIntrinsicRestriction_comp l E X hrm hmn CK]
  exact finiteDualizingRealizationRestriction_transport l E X hrm hmn K

end WeilConjectures
