/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
import WeilConjectures.Topology.Sheaves.PushforwardCohomology
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Leray comparison for an acyclic abelian sheaf

Source: Stacks Project, Cohomology of Sheaves, Tags 01F2 and 01F4 (1)
(blueprint: lem-sc-leray-closed-pushforward-cohomology).
-/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite

namespace TopCat.Sheaf

/-- The natural Leray edge is an isomorphism on sheaves with vanishing higher direct images.
Source: Stacks Project, Cohomology of Sheaves, Tags 01F2 and 01F4 (1)
(blueprint: lem-sc-leray-closed-pushforward-cohomology).

Here `a` is the canonical map from the free abelian sheaf on the terminal open of `X`
to the direct image of that on `Z`: its value on every free generator is the corresponding
free generator on the inverse-image open. The cocycle equation characterizes the edge:
lift an injective resolution of the direct image to the direct image of an injective
resolution, and use the same global cocycle on `Z`. Quantifying over all such lifts makes
this characterization independent of the resolutions and comparison maps.

Proof:
1. Apply lem-sc-topological-leray-spectral-sequence to obtain the first-quadrant Leray
spectral sequence with E₂^{a,b} = H^a(X,R^b f_*F), its finite abutment filtration and the
natural bottom edge H^p(X,f_*F) → H^p(Z,F). The injective-resolution construction of this
edge gives the displayed cocycle characterization and naturality.
2. If all positive higher direct images vanish, only row zero remains. Every differential
on each page r ≥ 2 has source or target outside that row, and hence vanishes. Thus E∞ = E₂.
For total degree p all graded pieces except the p-th vanish. The finite filtration therefore
identifies its p-th piece with the whole abutment H^p(Z,F). Consequently the same edge map
is an isomorphism, whose inverse gives the comparison in the direction stated in the node. -/
theorem exists_lerayEdge_isIso_of_acyclic {Z X : TopCat.{u}} (f : Z ⟶ X) :
    ∃ a : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶
      (pushforwardAb f).obj
        ((presheafToSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).obj
          (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)),
      (∀ (U : Opens X) (g : U ⟶ (⊤ : Opens X)),
        a.hom.app (op U)
            ((toSheafify (Opens.grothendieckTopology X)
              (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free)).app (op U)
                (FreeAbelianGroup.of g)) =
          (toSheafify (Opens.grothendieckTopology Z)
            (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)).app
              (op ((Opens.map f).obj U))
                (FreeAbelianGroup.of
                  ((Opens.map f).map g ≫ eqToHom (Opens.map_top f)))) ∧
      ∃ ε : ∀ p : ℕ,
        pushforwardAb f ⋙ Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) p ⋙
            (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤) ⟶
          Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Z) p ⋙
            (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤),
        (∀ (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
          (I : InjectiveResolution F) (J : InjectiveResolution ((pushforwardAb f).obj F))
          (φ : J.cocomplex ⟶ ((pushforwardAb f).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex)
          (_hφ : J.ι.f 0 ≫ φ.f 0 = (pushforwardAb f).map (I.ι.f 0))
          (p : ℕ)
          (s : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
            (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶ J.cocomplex.X p)
          (hs : s ≫ J.cocomplex.d p (p + 1) = 0)
          (t : (presheafToSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).obj
            (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free) ⟶ I.cocomplex.X p)
          (ht : t ≫ I.cocomplex.d p (p + 1) = 0)
          (_hst : a ≫ (pushforwardAb f).map t = s ≫ φ.f p),
          (ε p).app F (J.extMk s (p + 1) rfl hs) = I.extMk t (p + 1) rfl ht) ∧
        (∀ (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}),
          (∀ q : ℕ, 0 < q → IsZero
            ((@Functor.rightDerived _ _ _ _ _ _ _ (pushforwardAb f)
              (@Functor.additive_of_comp_faithful _ _ _ _ _ _ _ _ _ (pushforwardAb f)
                (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
                inferInstance
                (Functor.additive_of_iso
                  (F := sheafToPresheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⋙
                    (Functor.whiskeringLeft (Opens X)ᵒᵖ (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj
                      (Opens.map f).op) (Iso.refl _)) inferInstance) q).obj F)) →
            ∀ p : ℕ, IsIso ((ε p).app F)) := by
  sorry

end TopCat.Sheaf
