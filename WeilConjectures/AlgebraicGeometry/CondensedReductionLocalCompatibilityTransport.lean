/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedReductionTransportData

/-! # Weil and residue-fibre compatibility under reduction

Source: latest blueprint, sec-deligne-laumon-general/sk-i-dl-general-real/
thm-zl-real-mixed-by-curves.proof.md, paragraph 6.
(blueprint: lem-zl-condensed-reduction-local-compatibility-transport)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.Endofunctor
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedReduction

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The fixed-pair equivalence has the normalized local scalar-fibre compatibility.

Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, paragraph 6.
Proof: transport the invertible Frobenius fixed pairs across the commuting square using the
canonical upper-star compositors. The reduction is a universal homeomorphism, hence it
bijects closed points and induces residue-field isomorphisms. Compose the canonical fibre
comparison with the equivariant unit and counit; naturality and triangle identities give both
intertwining equations, including empty schemes and zero fibres.
(blueprint: lem-zl-condensed-reduction-local-compatibility-transport)
-/
 theorem local_compatibility_transport (hl : l ≠ D.p) [IsSeparated X₀.hom]
    (h : Commutes D X₀) :
    ∃ E : WeilEquivalence D l X₀ h, LocalCompatibility D l X₀ E := by
  sorry

end WeilConjectures.CondensedReduction
