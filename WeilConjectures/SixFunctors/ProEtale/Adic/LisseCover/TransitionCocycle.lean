/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseUniversalCover
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.CompactOpenLattice

/-!
# The transition cocycle of a trivialisation

Let `G` be an `ℓ`-adic sheaf on `Y` trivialised, `ε : f^* G ≅ ℚ̄_ℓⁿ`, on a weakly étale
`f : V ⟶ Y` with `V ×_Y V` compact. Its transition matrices take values in `GL_n(E)` for a finite
extension `E` of `ℚ_ℓ` and form a continuous cocycle `γ : V ×_Y V → GL_n(E)`
(`AlgebraicGeometry.ProEtale.AdicSheaf.exists_transitionCocycle`). Acting on the lattices of
`Eⁿ` (`PadicAlgCl.CompactOpenLattice`), `γ` is a descent cocycle
(`AlgebraicGeometry.ProEtale.AdicSheaf.isDescentCocycle_smul_compactOpenLattice`), whose
twisted sections are the lattices of `G`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {Y V : Scheme.{u}}

open PadicAlgCl AdicSheaf

end AlgebraicGeometry.ProEtale
