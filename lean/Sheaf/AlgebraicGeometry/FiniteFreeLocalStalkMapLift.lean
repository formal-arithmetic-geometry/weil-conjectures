/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Sheaf.Algebra.Homology.ModuleStalkFunctor

/-! # Lifting images of a finite free local source

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`).
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

/-- A stalk-linear map composed with a finite free local-source morphism lifts
on a smaller neighborhood. No relations or descent to the quotient are asserted.

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`),
third paragraph, finite-coordinate lifting.
(blueprint: lem-weil-pbc-finite-free-local-stalk-map-lift)

Proof: Evaluate each of the finitely many free basis sections at U, apply f,
take its germ at x and apply χ. Represent these finitely many resulting germs
by sections of G, intersecting their neighborhoods with U. On this intersection
use freeHomEquiv and preservation of the free coproduct by restriction to obtain
ψ. Its induced germ action agrees with χ after f on the basis germs. Every germ
of a section of the restricted finite free sheaf is a linear combination of
those basis germs: finite coproducts of module sheaves are computed sectionwise,
and restriction and germs preserve these finite sums. Linearity therefore gives
the formula on all sections on all smaller neighborhoods. For an empty basis
use the unique morphism from the zero object and keep U. -/
theorem exists_finiteFree_local_stalkMap_lift
    (X : RingedSpace.{u}) (F G : Modules X) (x : X)
    (U : Opens X) (hxU : x ∈ U) (I : Type u) [Finite I]
    (f : SheafOfModules.free (R := ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf).over U) I ⟶ F.over U)
    (χ : (moduleStalkFunctor X x).obj F →ₗ[X.presheaf.stalk x]
      (moduleStalkFunctor X x).obj G) :
    ∃ (V : Opens X) (hxV : x ∈ V) (i : V ⟶ U)
      (ψ : (SheafOfModules.overMap ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf) i).obj
        (SheafOfModules.free (R := ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf).over U) I) ⟶ G.over V),
      ∀ (W : Opens X) (j : W ⟶ V) (hxW : x ∈ W)
        (s : (SheafOfModules.free (R := ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf).over U) I).val.obj
          (op (Over.mk (j ≫ i)))),
        TopCat.Presheaf.germ G.val.presheaf W x hxW
          (ψ.val.app (op (Over.mk j)) s) =
        χ (TopCat.Presheaf.germ F.val.presheaf W x hxW
          (f.val.app (op (Over.mk (j ≫ i))) s)) := by sorry

end AlgebraicGeometry.RingedSpace
