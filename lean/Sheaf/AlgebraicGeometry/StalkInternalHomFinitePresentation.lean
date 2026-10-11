/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Sheaf.Algebra.Homology.ModuleStalkFunctor

/-!
# Stalk of internal Hom with finitely presented source

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`),
finitely presented case (blueprint: lem-weil-pbc-stalk-internal-hom-finite-presentation).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

/-- The canonical map from the stalk of internal Hom to the linear maps of stalks is
an isomorphism when the source module is finitely presented. The formula on germs
specifies the canonical map, including evaluation on every smaller neighbourhood.

Source: Stacks Project, Modules, Lemma 01CP (`lemma-stalk-internal-hom`).
(blueprint: lem-weil-pbc-stalk-internal-hom-finite-presentation)

The stalks are the module stalks `RingedSpace.moduleStalkFunctor` (def-pc-module-stalk-functor),
whose carriers are the abelian-group stalks in which the germs below live.

Proof:
1. A local morphism induces a stalk map by applying it to representative sections.
   Equality of germs makes this well defined; it is additive and stalk-ring linear
   (`def-weil-pbc-module-stalk`, `def-pur-sheaf-hom`, `def-pur-localized-ringed-site`).
2. Localize at the point to a finite free presentation of F, using
   `def-weil-pbc-module-finite-type-presentation`. Its cokernel presentation is exact
   by `lem-weil-pbc-module-stalk-exact`; restriction preserves the stalks and the map.
3. Apply `lem-weil-pbc-sheaf-hom-finite-presentation-kernel` to obtain the exact sequence
   0 -> Hom(F,G) -> G^n -> G^m of sheaves, with the maps given by evaluation and the
   presentation matrix.
4. Take stalks using `lem-weil-pbc-module-stalk-exact`. Stalks commute with finite sums:
   finitely many representatives, or equalities of germs, share a neighbourhood.
   Thus the internal-Hom stalk is the kernel of G_x^n -> G_x^m.
5. The stalk presentation and `lem-weil-pbc-module-hom-left-exact` identify
   Hom(F_x,G_x) with the same kernel, by evaluation on the finite free basis.
6. The canonical map commutes with these two evaluations by its formula on germs.
   Both evaluations are injective with the same image, so it is bijective. Its
   linearity from step 1 yields the displayed linear equivalence. -/
theorem exists_stalk_internalHom_linearEquiv_of_finitePresentation
    (X : RingedSpace.{u})
    (F G : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf))
    [SheafOfModules.IsFinitePresentation.{u} F] (x : X) :
    ∃ e : (moduleStalkFunctor X x).obj (F.homObj G) ≃ₗ[
        X.presheaf.stalk x]
      ((moduleStalkFunctor X x).obj F →ₗ[X.presheaf.stalk x]
        (moduleStalkFunctor X x).obj G),
      ∀ (U : Opens X) (hxU : x ∈ U)
        (φ : (SheafOfModules.homObj F G).val.obj (op U))
        (V : Opens X) (i : V ⟶ U) (hxV : x ∈ V) (s : F.val.obj (op V)),
        e (TopCat.Presheaf.germ (SheafOfModules.homObj F G).val.presheaf U x hxU φ)
            (TopCat.Presheaf.germ F.val.presheaf V x hxV s) =
          TopCat.Presheaf.germ G.val.presheaf V x hxV
            ((φ.app (op (Over.mk i))) s) := by
  sorry

end AlgebraicGeometry.RingedSpace
