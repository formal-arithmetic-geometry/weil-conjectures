/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.CategoryTheory.OpcyclesTorKernelIso
import WeilConjectures.CategoryTheory.TensorHomologyImageKernelEpi

/-!
# Tor of an opcycle cokernel

Source: Stacks Project, More on Algebra, Lemma 15.59.2 (Tag 0653), Tor argument
(blueprint: lem-pc-module-opcycles-tor-surjection).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory

end CategoryTheory
