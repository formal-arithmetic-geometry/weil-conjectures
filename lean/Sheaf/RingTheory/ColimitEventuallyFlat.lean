/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Localization.Defs

/-!
# Flatness at a stage of a directed colimit

Source: Stacks Project, Algebra, Tag 00R6 (lemma-colimit-eventually-flat), with the
system of Tag 00QX and the hypotheses used by Tag 00MO.
(blueprint: lem-weil-pbc-colimit-eventually-flat)
-/

universe u v w z

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RingTheory

/-- A flat colimit is flat at some stage. Source: Stacks Project, Algebra, Tag 00R6,
with Noetherian local stages and localization as in Tag 00MO.
(blueprint: lem-weil-pbc-colimit-eventually-flat)

Proof:
1. Fix an index and restrict to the cofinal directed set above it, using
   `lem-weil-pbc-colimit-initial-full-subcategory`.
2. The kernel of the maximal-ideal multiplication map is finite over the stage's
   second ring, by `lem-weil-pbc-noetherian-submodule-finite`; choose generators.
3. Regard the ring and group colimits as modules over the fixed first-stage ring,
   using `lem-weil-pbc-filtered-colimit-modules-criterion`,
   `lem-weil-pbc-filtered-colimit-algebras-elementwise`,
   `lem-weil-pbc-filtered-colimit-rings-zero`, and
   `lem-weil-pbc-filtered-colimit-modules-elementwise`. Tensoring with its maximal
   ideal commutes with these colimits by `lem-weil-pbc-tensor-commutes-with-colimits`.
4. Apply `lem-weil-pbc-flat-tensor-exact` to the kernel of the multiplication map
   from the maximal ideal tensored with the limit ring. Flatness of the limit
   module writes the images of the chosen generators as finite sums of kernel
   elements tensored with module elements.
5. Descend those finitely many elements to a common stage, then descend their
   vanishing and equality using `lem-weil-pbc-filtered-colimit-rings-zero` and
   `lem-weil-pbc-filtered-colimit-modules-elementwise`.
6. The generators, and hence the whole kernel by scalar compatibility, map to
   zero in the extended maximal ideal tensored with the later-stage module.
7. Apply `lem-weil-pbc-flat-another-variant-local-criterion`: the localization
   hypothesis holds, the residue-field module is flat by
   `lem-weil-pbc-module-over-field-flat`, and the kernel map is zero. Transport
   flatness through the specified tensor base-change isomorphism.

The tensor base-change isomorphism uses the factors in the opposite order to
Tag 00QX; tensor symmetry identifies it with that tag's canonical map.
-/
theorem exists_flat_stage
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (A : Λ ⥤ CommRingCat.{v}) (B : Λ ⥤ CommRingCat.{w})
    (N : Λ ⥤ AddCommGrpCat.{z}) [HasColimit A] [HasColimit B] [HasColimit N]
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
  sorry

end RingTheory
