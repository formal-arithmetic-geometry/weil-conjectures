/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Topology.Sheaves.Abelian

/-! # Natural tensor comparison on an open localized site

Source: Stacks Project, Tags 01CD and 03DH.
(blueprint: lem-pc-open-localized-tensor-natural).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SheafOfModules

/-- Tensor product commutes naturally with restriction to the localized open site.
Source: Stacks Project, Tag 01CD (`modules-lemma-tensor-product-pullback`) and Tag 03DH.

Proof: before sheafification both sides have sections M(V) tensor_(R(V)) N(V) at
an object V -> U. Their restrictions are the tensor of the two module restrictions.
A covering sieve on V in the slice consists of exactly a covering sieve on V with
its forced maps to U. Thus sheafification commutes with this restriction: the local
representatives, local equality relation and gluing maps defining sheafification
are identical on both sites. Sheafifying the identity of presheaf tensors produces
the comparison and its inverse. The two composites are identities by the universal
property of sheafification. A pair of module maps acts by f tensor g before
sheafification, so these identities commute with both module maps after sheafification.
This proves the displayed naturality square. The empty open, zero modules and zero
coefficient rings use the same construction without any nonzero assumption.
(blueprint: lem-pc-open-localized-tensor-natural). -/
theorem exists_open_localized_tensor_natural
    {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (U : TopologicalSpace.Opens X) :
    let A := (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R
    let V := overFunctor.{u} A U
    letI := monoidalCategory R
    letI : MonoidalCategory (SheafOfModules.{u} (A.over U)) :=
      monoidalCategory (R.over U)
    ∃ e : ∀ (M N : SheafOfModules.{u} A), V.obj (M ⊗ N) ≅ V.obj M ⊗ V.obj N,
      ∀ (M M' N N' : SheafOfModules.{u} A) (f : M ⟶ M') (g : N ⟶ N'),
        V.map (f ⊗ₘ g) ≫ (e M' N').hom = (e M N).hom ≫ (V.map f ⊗ₘ V.map g) :=
  by sorry

end SheafOfModules
