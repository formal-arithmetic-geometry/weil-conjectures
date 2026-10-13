/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Sheaf.Algebra.Homology.ModuleStalkFunctor

/-! # Shrinking a finite free local map with zero germ action

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`).
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

/-- A morphism from a restricted finite free sheaf which is zero on all germs
becomes the zero morphism on a smaller neighborhood.

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`),
second paragraph applied to the finite free relation sheaf in the third paragraph.
(blueprint: lem-weil-pbc-finite-free-local-hom-zero)

Proof: Evaluate ψ on each restricted basis section at V. The hypothesis says
that each of these finitely many image sections has zero germ. The germ equality
criterion supplies, for each basis index, a smaller neighborhood where that
image section vanishes. Intersect these neighborhoods with V. Naturality gives
zero image on the restrictions of every basis section. Restriction preserves
free coproducts and their basis inclusions, so the coproduct universal property,
or freeHomEquiv, implies that the restricted morphism is zero. An empty basis
requires no intersection; the source is already the zero object. -/
theorem exists_finiteFree_local_hom_zero
    (X : RingedSpace.{u}) (G : Modules X) (x : X)
    (U V : Opens X) (hxV : x ∈ V) (i : V ⟶ U) (I : Type u) [Finite I]
    (ψ : (SheafOfModules.overMap ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf) i).obj
      (SheafOfModules.free (R := ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf).over U) I) ⟶ G.over V)
    (hψ : ∀ (W : Opens X) (j : W ⟶ V) (hxW : x ∈ W)
      (s : (SheafOfModules.free (R := ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf).over U) I).val.obj
        (op (Over.mk (j ≫ i)))),
      TopCat.Presheaf.germ G.val.presheaf W x hxW
        (ψ.val.app (op (Over.mk j)) s) = 0) :
    ∃ (W : Opens X) (hxW : x ∈ W) (j : W ⟶ V),
      (SheafOfModules.overMap ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf) j).map ψ = 0 := by sorry

end AlgebraicGeometry.RingedSpace
