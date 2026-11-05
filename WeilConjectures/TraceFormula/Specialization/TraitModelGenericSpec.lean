/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitModelCompactification

/-!

# The generic fibre of a trait model over the base

Let `S = Spec k'⟦t⟧` be the trait, `Spec K ⟶ S` its generic point (`K = Frac k'⟦t⟧`) and
`Spec Ω ⟶ Spec K` the geometric generic point. For a `k`-scheme `X`, `X ×_k Spec Ω` is the base
change of `X ×_k Spec K` along the faithfully flat `Spec Ω ⟶ Spec K`
(`AlgebraicGeometry.isPullback_traitGenericBaseChangeMap`).

If `M` is a trait model of `X` over the base whose geometric generic fibre is all of
`X ×_k Spec Ω`, and `e : 𝒳 ⟶ X` factors the identification `ε`, then `(e, q)` identifies the
generic fibre `𝒳 ×_S Spec K` with `X ×_k Spec K`
(`NearbyCyclesModel.IsTraitModelOfBase.exists_isPullback_traitGenericSpec`):
this holds over `Spec Ω` and descends along `Spec Ω ⟶ Spec K` (Stacks 02L4). Consequently
morphisms into `𝒳` over `Spec K` are determined by their composites with `e`
(`NearbyCyclesModel.eq_of_isPullback_traitGenericSpec`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

section TraitGenericBaseChange

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k']

end TraitGenericBaseChange

namespace ProEtale.CondensedRing.NearbyCyclesModel

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

end ProEtale.CondensedRing.NearbyCyclesModel

end AlgebraicGeometry

