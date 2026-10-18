/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.FinitePresentation

/-!
# Finite type flat module has a finitely presented stalk

Source: Stacks Project, `flat.tex`, Tag 05I7, lemma-finite-type-flat-at-point-local,
affine translation (blueprint: lem-trf-flat-finite-type-flat-point-local).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u v w

namespace Module

/-- If `A → B` is finitely presented, `N` is finite over `B`, and the localization
of `N` at a prime of `B` is flat over `A`, then that localization is finitely
presented over the localized ring `B_q`.

Source: Stacks Project, `flat.tex`, Tag 05I7, lemma-finite-type-flat-at-point-local,
affine translation (blueprint: lem-trf-flat-finite-type-flat-point-local).

Proof: Translate to the affine schemes `Spec B → Spec A`, with the finite type
module represented by `N`. The flatness hypothesis at the prime gives, by Tag
05I6, an étale neighbourhood where the pulled-back module is finitely presented.
The induced map of local rings is flat and local, hence faithfully flat; the
localized stalk is the tensor product of `N_q` with the target local ring and is
finitely presented. Faithfully flat descent of finite presentation (Tag 03C4(2))
then gives finite presentation of `N_q` over `B_q`. -/
theorem finitePresentation_localizedModule_atPrime_of_flat
    {A : Type u} {B : Type v} {N : Type w}
    [CommRing A] [CommRing B] [AddCommGroup N]
    [Algebra A B] [Module B N] [Module.Finite B N]
    [Algebra.FinitePresentation A B]
    (q : Ideal B) [q.IsPrime]
    (hflat : @Module.Flat A (LocalizedModule q.primeCompl N) _ _
      (Module.compHom (LocalizedModule q.primeCompl N) (algebraMap A B))) :
    Module.FinitePresentation (Localization.AtPrime q) (LocalizedModule q.primeCompl N) := by
  sorry

end Module
