/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: SHEAF group M1
-/
module

public import Sheaf.RingTheory.JapaneseDomain
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# N-2 ascends along a finite extension of Noetherian domains

Source: Stacks Project, Algebra, Lemma Tag 032I, lines 45202-45232
(blueprint: lem-weil-pbc-n2-ascends-finite-domain-extension).
-/

@[expose] public section

universe uA uB uK uE

set_option autoImplicit false

/-- If `A ⊆ B` is a finite extension of Noetherian domains and `A` is N-2, then `B` is N-2.
Source: Stacks Project, Algebra, Lemma Tag 032I, lines 45202-45232
(blueprint: lem-weil-pbc-n2-ascends-finite-domain-extension).

Proof (the six steps of Tag 032I). (1) The injective map `A → B` induces an embedding of
fraction fields `K → E`, so every finite extension of the latter
is also an `A`-algebra through the former (using
`def-weil-pbc-localization-at-prime` and `def-pc-field-extension`). (2) Finite generators
of `B` over `A` span a finite-dimensional domain over `K`; the
finite-dimensional-domain-is-a-field lemma identifies this span with `E`, so
the fraction-field extension is finite (using
`lem-weil-pbc-finite-dimensional-domain-is-field`). (3) The tower law
(`lem-weil-pbc-field-degree-multiplicativity`) makes every finite extension of
`E` finite over `K`. (4) `IsN2 A K` therefore makes the integral
closure of `A` in that extension finite over `A` (using
`def-weil-pbc-integral-closure` and `def-weil-pbc-japanese-domain`). (5) Since `B` is finite
over `A`, it is integral, and integrality transitivity identifies that closure with the
integral closure of `B` (using `lem-weil-pbc-finite-algebra-is-integral` and
`lem-weil-pbc-integral-transitive`). (6) The same generators over `A` generate this closure
over `B`, proving `IsN2 B E` (using `def-weil-finitely-generated-module`).
-/
theorem isN2_of_finite_domain_extension (A : Type uA) (B : Type uB)
    (K : Type uK) (E : Type uE) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [IsNoetherianRing A] [Module.Finite A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field E] [Algebra B E] [IsFractionRing B E]
    (hAB : Function.Injective (algebraMap A B)) (hA : IsN2 A K) : IsN2 B E := by
  sorry
