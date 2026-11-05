/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.RingTheory.TensorCyclesFlatCokernel
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.CategoryTheory.Linear.FunctorCategory

/-!
# Canonical first Tor action and natural base-change map

Source: Stacks Project, Algebra, Tag 00MM (lemma-surjective-on-tor-one).
The coefficient action is induced by multiplication in the second Tor argument.
The natural map is constructed using the balanced tensor universal property.
(blueprint: lem-weil-pbc-tor-one-surjective-flat-middle).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace CategoryTheory

noncomputable section

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]

variable (S : Type u) [CommRing S] [Algebra R S]

variable (A B : Type u) [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Module R B] [IsScalarTower R A B]

end

end CategoryTheory
