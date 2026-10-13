/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Descent of the maximal-ideal multiplication kernel

Source: Stacks Project, Algebra, Tag 00R6 (lemma-colimit-eventually-flat),
proof of eventual vanishing of the maximal-ideal multiplication kernel.
(blueprint: lem-weil-pbc-colimit-maximal-kernel-descent)
-/

@[expose] public section

universe u v w z

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RingTheory

/-- The maximal-ideal multiplication kernel at any fixed stage dies after base change
at a later stage. Source: Stacks Project, Algebra, Tag 00R6, proof preceding the
application of Tag 00MO; ideal-tensor description in Remark 00M6.
(blueprint: lem-weil-pbc-colimit-maximal-kernel-descent)

Proof: Restrict to the cofinal directed set above `i`. The maximal ideal of `A_i`
is finite since `A_i` is Noetherian. Its tensor product with `N_i` is finite over
`B_i`, and the multiplication kernel is finite since `B_i` is Noetherian. Choose
finitely many generators. Regard all later rings and modules as `A_i`-modules.
Their colimits remain the given ring and additive-group colimits, by the
representative and eventual-equality criteria for filtered colimits. Tensoring
with the maximal ideal commutes with these colimits. Write `s` for multiplication
from the maximal ideal tensored with the limit ring to the limit ring. Flatness
of the limit module implies that every image of a chosen kernel generator is a
finite sum of elements of `ker s` tensored with limit-module elements, using
exactness of tensoring the sequence `ker s → domain s → codomain s`.
Descend those finitely many elements to a common stage. Descend the equations
`s(k)=0`, and then the expressions for the chosen generators, to one later
stage using eventual vanishing in the ring and module colimits. Mapping to the
extended ideal tensored with the stage module kills each expression: the image
of `k` is `s(k)`, which is zero. The canonical map is semilinear over `B_i`, so
it kills the whole kernel. This gives exactly `θ` and its
pure-tensor formula and kernel vanishing. No localization or tensor base-change
hypothesis, or locality of the transition maps, is used in this descent argument.
-/
theorem exists_stage_maximal_kernel_vanishes
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (A : Λ ⥤ CommRingCat.{v}) (B : Λ ⥤ CommRingCat.{w})
    (N : Λ ⥤ AddCommGrpCat.{z}) [HasColimit A] [HasColimit B] [HasColimit N]
    [∀ i, IsLocalRing (A.obj i)]
    [∀ i, IsNoetherianRing (A.obj i)] [∀ i, IsNoetherianRing (B.obj i)]
    [∀ i, Module (B.obj i) (N.obj i)] [∀ i, Module.Finite (B.obj i) (N.obj i)]
    (φ : ∀ i, A.obj i →+* B.obj i)
    (hcomm : ∀ (i j : Λ) (f : i ⟶ j),
      (B.map f).hom.comp (φ i) = (φ j).comp (A.map f).hom)
    (hscalar : ∀ (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : N.obj i),
      (N.map f).hom (b • x) = (B.map f).hom b • (N.map f).hom x)
    (ψ : (colimit A : CommRingCat.{v}) →+* (colimit B : CommRingCat.{w}))
    (hψ : ∀ i, ψ.comp (colimit.ι A i).hom = (colimit.ι B i).hom.comp (φ i))
    [Module (colimit B : CommRingCat.{w}) (colimit N : AddCommGrpCat.{z})]
    (hlimitScalar : ∀ (i : Λ) (b : B.obj i) (x : N.obj i),
      (colimit.ι N i).hom (b • x) = (colimit.ι B i).hom b • (colimit.ι N i).hom x)
    (hflat : letI := Module.compHom (colimit N : AddCommGrpCat.{z}) ψ
      Module.Flat (colimit A : CommRingCat.{v}) (colimit N : AddCommGrpCat.{z})) (i : Λ) :
    ∃ (j : Λ) (f : i ⟶ j),
      letI := Module.compHom (N.obj i) (φ i)
      letI := Module.compHom (N.obj j) (φ j)
      let I := IsLocalRing.maximalIdeal (A.obj i)
      ∃ θ : I ⊗[A.obj i] N.obj i →+
          (I.map (A.map f).hom) ⊗[A.obj j] N.obj j,
        (∀ (a : I) (x : N.obj i), θ (a ⊗ₜ[A.obj i] x) =
          (⟨(A.map f).hom a, Ideal.mem_map_of_mem (A.map f).hom a.property⟩ :
            I.map (A.map f).hom) ⊗ₜ[A.obj j] (N.map f).hom x) ∧
        (∀ k : I ⊗[A.obj i] N.obj i,
          TensorProduct.lift ((LinearMap.lsmul (A.obj i) (N.obj i)).comp I.subtype) k = 0 →
            θ k = 0) := by
  sorry

end RingTheory
