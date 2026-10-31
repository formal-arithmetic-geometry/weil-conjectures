/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Iso

/-! # Cancellation for a specified four-factor comparison isomorphism -/
@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

/-- The inverse of a specified composite is identified by precomposition with its last
two factors. Source: Mathlib Iso.trans_inv, Iso.hom_inv_id_assoc and cancel_epi;
used for the comparison of projection maps in Stacks Tags 0944 and 099R.
(blueprint: lem-route-coefficient-first-compact-support-site-square-constructed-iso).

Proof: cancel the epimorphism c.hom followed by d.hom. The inverse of the four-factor
composite is d.inv, c.inv, b.inv, a.inv. The two adjacent inverse pairs cancel, giving
b.inv followed by a.inv, which is also the supplied composite with q. -/
theorem coefficientFirstCompactSupportInverseCancellation
    {C : Type*} [Category C] {X Y Z T U : C}
    (a : X ≅ Y) (b : Y ≅ Z) (c : Z ≅ T) (d : T ≅ U) (q : U ⟶ X)
    (h : c.hom ≫ d.hom ≫ q = b.inv ≫ a.inv) :
    (a ≪≫ b ≪≫ c ≪≫ d).inv = q := by
  apply (cancel_epi (c.hom ≫ d.hom)).mp
  simpa only [Category.assoc, Iso.trans_inv, Iso.hom_inv_id_assoc] using h.symm

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
