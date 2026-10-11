/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Sheaf.Topology.RingedModuleSkyscraper

/-!
# The module stalk–skyscraper adjunction on a scheme

Source: Stacks Project, Sheaves, Definition 009A (4) and Lemma 009C
(blueprint: lem-weil-pbc-module-skyscraper-stalk-adjunction).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Stacks Project, Sheaves, Tags 009A (4) and 009C
(blueprint: lem-weil-pbc-module-skyscraper-stalk-adjunction).
The concrete skyscraper is an additive functor right adjoint to the module stalk functor.
The inverse of `adj.homEquiv` is Phi in the node; its forward map is the stated inverse Psi.

Proof:
1. The skyscraper has sections `PLift (x ∈ U) → A`, with scalars acting through germs.
On a cover of an open containing x, compatibility makes all values on members containing x
agree, giving the unique gluing; for an open missing x the section group is zero, including
for the empty cover. Restrictions, linear maps, identities, composition and addition are
sectionwise, giving a sheaf of modules and an additive functor
(`def-weil-sheaf-of-modules-category`, `def-weil-pbc-module-stalk`).
2. Define Phi on a germ s_x by evaluating the sheaf morphism on s. Equal germs agree after
restriction to a common neighbourhood. The skyscraper restriction there is the identity,
so evaluation is independent of the representative. Represent a scalar and a section on a
common neighbourhood; sectionwise linearity proves stalk linearity
(`def-weil-pbc-module-stalk`).
3. Define Psi on U containing x by s ↦ psi(s_x), and on the other opens by the zero map.
The germ scalar law proves linearity, and restriction compatibility of germs proves
naturality on opens. Evaluating on germs proves Phi Psi = id; evaluating on sections on
opens containing x, and using the zero target otherwise, proves Psi Phi = id.
4. Precomposing with g sends the germ s_x to the germ of g_U(s), so Phi(phi ∘ g) equals
Phi(phi) ∘ g_x. Postcomposing with the skyscraper of h acts as h on each nonzero section,
so Phi(i_*h ∘ phi) equals h ∘ Phi(phi). These two identities give the adjunction. -/
theorem exists_moduleSkyscraperStalkAdjunction (X : Scheme.{u}) (x : X) :
    (SheafOfModules.ringedModuleSkyscraperFunctor X.toRingedSpace x).Additive ∧
      ∃ adj : RingedSpace.moduleStalkFunctor X.toRingedSpace x ⊣
          SheafOfModules.ringedModuleSkyscraperFunctor X.toRingedSpace x,
        (∀ (G : X.Modules) (A : ModuleCat.{u} (X.presheaf.stalk x))
          (φ : G ⟶
            (SheafOfModules.ringedModuleSkyscraperFunctor X.toRingedSpace x).obj A)
          (U : X.Opens) (hx : x ∈ U) (s : G.val.obj (op U)),
          ((adj.homEquiv G A).symm φ)
              (TopCat.Presheaf.germ G.val.presheaf U x hx s) =
            (φ.val.app (op U) s) ⟨hx⟩) ∧
        (∀ (G : X.Modules) (A : ModuleCat.{u} (X.presheaf.stalk x))
          (ψ : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G ⟶ A)
          (U : X.Opens) (hx : x ∈ U) (s : G.val.obj (op U)),
          ((adj.homEquiv G A ψ).val.app (op U) s) ⟨hx⟩ =
            ψ (TopCat.Presheaf.germ G.val.presheaf U x hx s)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
