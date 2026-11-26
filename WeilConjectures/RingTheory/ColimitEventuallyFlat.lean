/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Defs
import WeilConjectures.RingTheory.FlatOfLocalCriterionBaseChange
import WeilConjectures.RingTheory.ColimitMaximalKernelDescent

/-!
# Flatness at a stage of a directed colimit

Let `A → B` be a directed system of local homomorphisms of noetherian local rings and `N` a
compatible system of finite `B`-modules, with transition maps satisfying the localization and
base-change hypotheses of the local flatness criterion. If the colimit module is flat over the
colimit of `A`, then some stage `N i` is flat over `A i` (`RingTheory.exists_flat_stage`).

## Implementation details

Fix a stage `i`. The kernel of the multiplication map `mᵢ ⊗ Nᵢ → Nᵢ` is finite, so it has
finitely many generators. Flatness of the colimit writes their images as finite sums in the
kernel of the multiplication map over the colimit; these finitely many relations descend to a
common later stage `j`, where the generators, and hence the whole kernel, map to zero in
`mᵢ A_j ⊗ N_j`. The local flatness criterion then gives flatness of `N_j`, transported through the
tensor base-change isomorphism. This isomorphism uses the factors in the opposite order to
[Stacks, Tag 00QX]; tensor symmetry identifies it with the canonical map there.

## References

* [Stacks, Tag 00R6]
* [Stacks, Tag 00QX]
* [Stacks, Tag 00MO]
-/

@[expose] public section

universe u v w z

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RingTheory

/-- A flat colimit is flat at some stage: if the colimit of the modules `N i` is flat over the
colimit of the local rings `A i`, then some `N i` is flat over `A i`. -/
theorem exists_flat_stage
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (A : Λ ⥤ CommRingCat.{v}) (B : Λ ⥤ CommRingCat.{w})
    (N : Λ ⥤ AddCommGrpCat.{z}) [HasColimit A] [HasColimit B] [HasColimit N]
    [PreservesColimit A (forget CommRingCat.{v})]
    [∀ i, IsLocalRing (A.obj i)] [∀ i, IsLocalRing (B.obj i)]
    [∀ i, IsNoetherianRing (A.obj i)] [∀ i, IsNoetherianRing (B.obj i)]
    [∀ i, Module (B.obj i) (N.obj i)] [∀ i, Module.Finite (B.obj i) (N.obj i)]
    (φ : ∀ i, A.obj i →+* B.obj i)
    (hφ : ∀ i, IsLocalHom (φ i))
    (hA : ∀ (i j : Λ) (f : i ⟶ j), IsLocalHom (A.map f).hom)
    (hB : ∀ (i j : Λ) (f : i ⟶ j), IsLocalHom (B.map f).hom)
    (hcomm : ∀ (i j : Λ) (f : i ⟶ j),
      (B.map f).hom.comp (φ i) = (φ j).comp (A.map f).hom)
    (hscalar : ∀ (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : N.obj i),
      (N.map f).hom (b • x) = (B.map f).hom b • (N.map f).hom x)
    (ψ : (colimit A : CommRingCat.{v}) →+* (colimit B : CommRingCat.{w}))
    (hψ : ∀ i, ψ.comp (colimit.ι A i).hom = (colimit.ι B i).hom.comp (φ i))
    [Module (colimit B : CommRingCat.{w}) (colimit N : AddCommGrpCat.{z})]
    (hlimitScalar : ∀ (i : Λ) (b : B.obj i) (x : N.obj i),
      (colimit.ι N i).hom (b • x) = (colimit.ι B i).hom b • (colimit.ι N i).hom x)
    (hloc : ∀ (i j : Λ) (f : i ⟶ j),
      letI := (φ i).toAlgebra
      letI := (A.map f).hom.toAlgebra
      ∃ (q : B.obj i ⊗[A.obj i] A.obj j →+* B.obj j)
        (W : Submonoid (B.obj i ⊗[A.obj i] A.obj j)),
        (∀ (b : B.obj i) (a : A.obj j),
          q (TensorProduct.tmul (A.obj i) b a) = (B.map f).hom b * φ j a) ∧
        (letI := q.toAlgebra; IsLocalization W (B.obj j)))
    (hbase : ∀ (i j : Λ) (f : i ⟶ j),
      letI := (B.map f).hom.toAlgebra
      ∃ e : (B.obj j ⊗[B.obj i] N.obj i) ≃ₗ[B.obj j] N.obj j,
        ∀ (b : B.obj j) (x : N.obj i),
          e (TensorProduct.tmul (B.obj i) b x) = b • (N.map f).hom x)
    (hflat : letI := Module.compHom (colimit N : AddCommGrpCat.{z}) ψ
      Module.Flat (colimit A : CommRingCat.{v}) (colimit N : AddCommGrpCat.{z})) :
    ∃ i : Λ, letI := Module.compHom (N.obj i) (φ i)
      Module.Flat (A.obj i) (N.obj i) := by
  classical
  let i : Λ := Classical.choice inferInstance
  obtain ⟨j, f, τ, hτ, hker⟩ := exists_stage_maximal_kernel_vanishes
    A B N φ hcomm hscalar ψ hψ hlimitScalar hflat i
  let := (φ i).toAlgebra
  let := (A.map f).hom.toAlgebra
  let := (B.map f).hom.toAlgebra
  let := (φ j).toAlgebra
  let := ((B.map f).hom.comp (φ i)).toAlgebra
  let := Module.compHom (N.obj i) (φ i)
  let := Module.compHom (N.obj j) (φ j)
  have : IsScalarTower (A.obj i) (B.obj i) (B.obj j) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (A.obj i) (A.obj j) (B.obj j) :=
    IsScalarTower.of_algebraMap_eq' (hcomm i j f)
  have : IsScalarTower (A.obj i) (B.obj i) (N.obj i) :=
    IsScalarTower.of_compHom _ _ _
  have : IsScalarTower (A.obj j) (B.obj j) (N.obj j) :=
    IsScalarTower.of_compHom _ _ _
  have : IsLocalHom (algebraMap (A.obj i) (B.obj i)) := hφ i
  have : IsLocalHom (algebraMap (A.obj i) (A.obj j)) := hA i j f
  have : IsLocalHom (algebraMap (B.obj i) (B.obj j)) := hB i j f
  have : IsLocalHom (algebraMap (A.obj j) (B.obj j)) := hφ j
  let I := IsLocalRing.maximalIdeal (A.obj i)
  let : Field (A.obj i ⧸ I) := Ideal.Quotient.field I
  have hquot : Module.Flat (A.obj i ⧸ I) ((A.obj i ⧸ I) ⊗[A.obj i] N.obj i) :=
    inferInstance
  obtain ⟨e, he⟩ := hbase i j f
  let e' := e.restrictScalars (A.obj j)
  let J := I.map (A.map f).hom
  let E := TensorProduct.congr (LinearEquiv.refl (A.obj j) J) e'.symm
  let θ := E.toAddMonoidHom.comp τ
  have hθ : ∀ (a : I) (x : N.obj i), θ (a ⊗ₜ[A.obj i] x) =
      (⟨(A.map f).hom a, Ideal.mem_map_of_mem (A.map f).hom a.property⟩ : J)
        ⊗ₜ[A.obj j] ((1 : B.obj j) ⊗ₜ[B.obj i] x) := by
    intro a x
    have hx : e'.symm ((N.map f).hom x) = (1 : B.obj j) ⊗ₜ[B.obj i] x := by
      apply e'.injective
      simpa [e'] using (he 1 x).symm
    change E (τ (a ⊗ₜ[A.obj i] x)) = _
    rw [hτ]
    simp only [E, TensorProduct.congr_tmul, LinearEquiv.refl_apply, hx]
  have hstage := Module.flat_of_local_criterion_baseChange I
    (IsLocalRing.maximalIdeal.isMaximal (A.obj i)).ne_top (N.obj i)
    (hloc i j f) hquot θ hθ (fun k hk ↦ by
      change E (τ k) = 0
      rw [hker k hk, map_zero])
  refine ⟨j, ?_⟩
  exact (Module.Flat.equiv_iff e').mp hstage

end RingTheory
