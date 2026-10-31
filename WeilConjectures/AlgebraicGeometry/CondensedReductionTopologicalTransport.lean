/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedReductionTransportData
import WeilConjectures.AlgebraicGeometry.CondensedReductionModuleEquivalenceTransport
import WeilConjectures.AlgebraicGeometry.CondensedReductionLocalCompatibilityTransport

/-! # The actual module and local Weil equivalences under reduction

Source: latest blueprint, sec-deligne-laumon-general/sk-i-dl-general-real/
thm-zl-real-mixed-by-curves.proof.md, paragraph 6.
(blueprint: lem-zl-condensed-reduction-topological-transport)
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

/-- The reduction immersion induces the actual ordinary and Weil equivalences, with
both module functors and their adjunction normalized as in the data, and with the
canonical local fibre comparison. No numerical weight or filtration assertion is made.

Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, paragraph 6;
Stacks Tags 054M, 09AB and 03CR; parent proof steps 2--8.
(blueprint: lem-zl-condensed-reduction-topological-transport).

Proof:
1. Apply `module_equivalence_transport` to the reduction data and `hl`, obtaining the
   specified ordinary constructible module equivalence.
2. Apply `local_compatibility_transport` to the same reduction data, `hl` and the
   commuting-square equality `h`, obtaining a Weil equivalence `E` with
   `LocalCompatibility D l X₀ E`.
3. Package the two results as the conjunction stated below.
-/
theorem reduction_topological_transport (hl : l ≠ D.p) [IsSeparated X₀.hom]
    (h : Commutes D X₀) :
    Nonempty (ModuleEquivalence D l X₀) ∧
      ∃ E : WeilEquivalence D l X₀ h, LocalCompatibility D l X₀ E := by
  obtain ⟨hm⟩ := module_equivalence_transport D l X₀ hl
  obtain ⟨E, hE⟩ := local_compatibility_transport D l X₀ hl h
  exact ⟨⟨hm⟩, E, hE⟩

end WeilConjectures.CondensedReduction
