/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.Away.Basic

import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Finiteness.Small

/-! # Spreading a finite module from an element localization

Source: Stacks Project, Algebra, Tag 05N5 (`algebra-lemma-construct-fp-module`),
clause (1), with ideal zero and multiplicative subset the powers of `f`.
(blueprint: lem-trf-localized-finite-module-spread)
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Module

/-- Every finite module over `R[1/f]` is the localization of a finite `R`-module.

Source: Stacks Project, Algebra, Tag 05N5 (`algebra-lemma-construct-fp-module`),
clause (1), specialized to the zero ideal and the powers of `f`.
(blueprint: lem-trf-localized-finite-module-spread)

Proof: Choose finitely many generators of `L` using
`def-weil-finitely-generated-module`, giving a surjection `q : R[1/f]^n → L`.
Using `def-weil-ring-localization-away` and `def-weil-pbc-module-localization`,
let `K` be the inverse image of `ker q` under the localization map `R^n → R[1/f]^n`.
Set `M = R^n / K`. The images of the standard basis generate `M`, so it is finite,
and `q` induces an `R`-linear map `M → L`. Since `f` acts invertibly on `L`, this
map extends to `M[1/f] → L`, sending `(x + K)/f^r` to `q(x/f^r)`.
It is surjective because every vector in the finite power `R[1/f]^n` has a common
power-of-`f` denominator. If the image of `(x + K)/f^r` vanishes, multiplication
by the unit `f^r` shows `q(x/1) = 0`, hence `x ∈ K`. Thus the map is injective
as well and is the required `R[1/f]`-linear equivalence. -/
theorem exists_finite_localizationAway_model
    {R : Type u} [CommRing R] (f : R)
    (L : Type v) [AddCommGroup L] [Module (Localization.Away f) L]
    [Module.Finite (Localization.Away f) L] :
    ∃ M : ModuleCat.{u} R, Module.Finite R M ∧
      Nonempty (LocalizedModule (Submonoid.powers f) M ≃ₗ[Localization.Away f] L) := by
  let A := Localization.Away f
  let S := Submonoid.powers f
  let : Module R L := Module.compHom L (algebraMap R A)
  have : IsScalarTower R A L := IsScalarTower.of_compHom R A L
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := L)
  -- This span is the image of the finite free module in the source proof.
  let N : Submodule R L := Submodule.span R (s : Set L)
  have hN : N.FG := Submodule.fg_span s.finite_toSet
  have : Module.Finite R N := Module.Finite.of_fg hN
  have : Small.{u} N := hN.small N
  have : IsLocalizedModule S (LinearMap.id : L →ₗ[R] L) :=
    isLocalizedModule_id S L A
  have htop : N.localized' A S (LinearMap.id : L →ₗ[R] L) = ⊤ := by
    simpa only [N, Submodule.localized'_span, LinearMap.id_coe, Set.image_id] using hs
  refine ⟨ModuleCat.of R (Shrink.{u} N), inferInstance, ⟨?_⟩⟩
  exact (IsLocalizedModule.mapEquiv S
    (LocalizedModule.mkLinearMap S (Shrink.{u} N))
    (N.toLocalized' A S (LinearMap.id : L →ₗ[R] L)) A
    (Shrink.linearEquiv R N)).trans
      ((LinearEquiv.ofEq _ _ htop).trans (Submodule.topEquiv : (⊤ : Submodule A L) ≃ₗ[A] L))

end Module
