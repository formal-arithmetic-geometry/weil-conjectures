/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedReductionTransportData

/-! # Constructible module equivalence under reduction

Source: latest blueprint, sec-deligne-laumon-general/sk-i-dl-general-real/
thm-zl-real-mixed-by-curves.proof.md, paragraph 6.
(blueprint: lem-zl-condensed-reduction-module-equivalence-transport)
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

/-- The actual upper-star/lower-star adjunction restricts to the constructible module hearts.

Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, paragraph 6.
Proof: apply pro-etale topological invariance to the reduction universal homeomorphism and
transport the ringed module presentation. The finite constant-model stratification is carried
across the slice equivalences; closure under kernels and cokernels gives the abelian hearts.
Restrict the specified upper-star/lower-star adjunction. The transported unit and counit are
invertible, and the restricted functors preserve finite limits, finite colimits and addition.
(blueprint: lem-zl-condensed-reduction-module-equivalence-transport)
-/
 theorem module_equivalence_transport (hl : l ≠ D.p) [IsSeparated X₀.hom] :
    Nonempty (ModuleEquivalence D l X₀) := by
  sorry

end WeilConjectures.CondensedReduction
