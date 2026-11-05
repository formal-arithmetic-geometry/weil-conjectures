/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.GaloisClosure
public import WeilConjectures.FieldTheory.Galois.NormalFixedField

/-!
# Restriction of automorphisms along a map of field extensions

Consider a commutative square of fields
```
Ω₁ --ω--> Ω₂
 ^         ^
 |         |
L₁ --l--> L₂
```
with `Ω₁ / L₁` normal. Every `σ ∈ Aut(Ω₂/L₂)` maps `ω(Ω₁)` onto itself, hence restricts to an
automorphism of `Ω₁ / L₁`. This gives a group homomorphism
`AlgEquiv.restrictNormalHomAlong : Aut(Ω₂/L₂) →* Aut(Ω₁/L₁)` characterised by
`ω (restrictNormalHomAlong hω σ x) = σ (ω x)`.

If moreover `Ω₂ / L₂` is normal and `L₁` is relatively closed in `L₂` inside `Ω₂` (an element of
`Ω₁` whose image lies in `L₂` already lies in `L₁`), the image of this homomorphism is dense:
it surjects onto `Gal(L'/L₁)` for every finite Galois subextension `L'` of `Ω₁ / L₁`
(`AlgEquiv.exists_restrictNormalHomAlong_eq`, `AlgEquiv.exists_eq_of_forall_mem_range`).

The group-theoretic form of "the wild kernels map onto each other" (for a commutative square
`q₁ ∘ r = ψ ∘ q₂` of groups with `r` surjective and `ψ` injective, `r` maps `ker q₂` onto
`ker q₁`) is `MonoidHom.map_ker_eq_ker_of_comp_eq`.
-/

@[expose] public section

open IntermediateField

namespace AlgEquiv

variable {L₁ Ω₁ L₂ Ω₂ : Type*} [Field L₁] [Field Ω₁] [Field L₂] [Field Ω₂]
  [Algebra L₁ Ω₁] [Algebra L₂ Ω₂] {l : L₁ →+* L₂} {ω : Ω₁ →+* Ω₂}

section Inertia

variable {K₁ K₂ : Type*} [Field K₁] [Field K₂] [Algebra K₁ L₁] [Algebra K₁ Ω₁]
  [IsScalarTower K₁ L₁ Ω₁] [Algebra K₂ Ω₂]

end Inertia

end AlgEquiv
