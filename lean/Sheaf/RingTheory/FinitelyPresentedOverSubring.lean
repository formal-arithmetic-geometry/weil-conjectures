/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Finite presentation over a finite type algebra

Source: Stacks Project, `algebra.tex`, Lemma Tag 0561
(lemma-finitely-presented-over-subring), statement and proof
(blueprint: lem-trf-finitely-presented-over-subring).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Module.FinitePresentation

/-- An `S`-module finitely presented over `R` is finitely presented over `S` when the ring map
`R → S` is of finite type. The `R`-module structure is restriction along the given ring map.

Source: Stacks Project, `algebra.tex`, Lemma Tag 0561
(lemma-finitely-presented-over-subring), statement and proof
(blueprint: lem-trf-finitely-presented-over-subring).

Proof: (1) By `def-weil-pbc-finite-type-algebra`, choose algebra generators `x₁, …, xₙ` of `S`.
By `def-sc-finitely-presented-module`, choose `R`-module generators `y₁, …, yₘ` of `M` and
finitely many vectors generating their relation module.
(2) Express each `xᵢ yⱼ` as an `R`-linear combination of the `yₖ`. Define `N` with the same
`m` generators over `S`, the original finitely many relations, and these `nm` action
relations. This is a finite presentation of `N` over `S`.
(3) Sending the generators of `N` to the corresponding `yⱼ` respects every relation and
induces a surjective `S`-linear map `N → M`, since the `yⱼ` already generate over `R`.
(4) By `lem-trf-polynomial-action-reduction`, the action relations lower polynomial degree
and express any element of `N` as an `R`-linear combination of the generators. If its image
in `M` vanishes, its coefficient vector belongs to the `R`-span of the original relation
vectors, which are relations in `N` too. Thus the map is injective.
(5) The map is an isomorphism, so the finite presentation of `N` transfers to `M`.
-/
theorem of_finiteType_subring
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [AddCommGroup M]
    (f : R →+* S) [Module S M] (hS : RingHom.FiniteType f)
    (hM : @Module.FinitePresentation R M _ _ (Module.compHom M f)) :
    Module.FinitePresentation S M := by
  sorry

end Module.FinitePresentation
