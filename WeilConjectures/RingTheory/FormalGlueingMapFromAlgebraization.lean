/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Category.ModuleCat.Basic
import WeilConjectures.RingTheory.FormalGlueingEquivalence
import WeilConjectures.RingTheory.FormalGlueingReplacePrime
import Mathlib.RingTheory.Finiteness.Ideal
import WeilConjectures.RingTheory.FormalGlueingData

/-!
# Algebraization of a map that is an isomorphism away from an ideal

Source: Stacks Project, More on Algebra, Lemma 0ALK, proof of part (2),
using Remark 05EL and Proposition 05ER 
(blueprint: lem-weil-pbc-formal-glueing-map-from-algebraization).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace FormalGlueing

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

end FormalGlueing
