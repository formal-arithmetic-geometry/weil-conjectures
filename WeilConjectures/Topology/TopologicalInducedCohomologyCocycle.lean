/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.Sheaves.PushforwardCohomology
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
import WeilConjectures.Topology.TopologicalInducedEdgeAndMap
import WeilConjectures.Topology.TopologicalInducedCocycleFormula

/-! # The induced topological cohomology map on cocycles

The map induced by a continuous map on the cohomology of its direct image, described on
injective-resolution cocycles.

## Implementation details

The terminal free abelian sheaf map `a : KX → f_*KZ` is the adjunction unit under the
identification of the inverse image of `KX` with `KZ`. The cohomology map is obtained from the
exact inverse-image functor on `Ext`, and is computed on injective resolutions by any comparison
`J → f_*I`; comparisons are unique up to homotopy.

## References

* [Stacks Project, Tags 01DZ and 01F2](https://stacks.math.columbia.edu/tag/01F2)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace CategoryTheory

/-- The map induced by a continuous map on cohomology of its direct image, described on
arbitrary injective-resolution cocycles. This statement involves no spectral sequence. -/
theorem exists_topological_induced_cohomology_cocycle
    {Z X : TopCat.{u}} (f : Z ⟶ X) [(TopCat.Sheaf.pushforwardAb f).Additive]
    (HX : ℕ → (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}))
    (HZ : ℕ → (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}))
    (hX : ∀ n, HX n = Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤))
    (hZ : ∀ n, HZ n = Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Z) n ⋙
      (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) :
    ∃ edge : ∀ p : ℕ, TopCat.Sheaf.pushforwardAb f ⋙ HX p ⟶ HZ p,
      ∃ a : (presheafToSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).obj
        (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶
      (TopCat.Sheaf.pushforwardAb f).obj
        ((presheafToSheaf (Opens.grothendieckTopology Z)
          AddCommGrpCat.{u}).obj
          (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)),
      (∀ (U : Opens X) (h : U ⟶ (⊤ : Opens X)),
        a.hom.app (op U)
          ((toSheafify (Opens.grothendieckTopology X)
            (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free)).app
              (op U) (FreeAbelianGroup.of h)) =
          (toSheafify (Opens.grothendieckTopology Z)
            (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)).app
              (op ((Opens.map f).obj U))
              (FreeAbelianGroup.of ((Opens.map f).map h ≫
                eqToHom (Opens.map_top f)))) ∧
      (∀ (F : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
        (I : InjectiveResolution F)
        (J : InjectiveResolution ((TopCat.Sheaf.pushforwardAb f).obj F))
        (φ : J.cocomplex ⟶
          ((TopCat.Sheaf.pushforwardAb f).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex)
        (_hφ : J.ι.f 0 ≫ φ.f 0 =
          (TopCat.Sheaf.pushforwardAb f).map (I.ι.f 0)) (p : ℕ)
        (s : (presheafToSheaf (Opens.grothendieckTopology X)
          AddCommGrpCat.{u}).obj
          (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶
            J.cocomplex.X p)
        (hs : s ≫ J.cocomplex.d p (p + 1) = 0)
        (z : (presheafToSheaf (Opens.grothendieckTopology Z)
          AddCommGrpCat.{u}).obj
          (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free) ⟶
            I.cocomplex.X p)
        (hz : z ≫ I.cocomplex.d p (p + 1) = 0)
        (_hsz : a ≫ (TopCat.Sheaf.pushforwardAb f).map z = s ≫ φ.f p),
        (eqToHom (congrArg (fun Q ↦ Q.obj F) (hZ p)))
          ((edge p).app F
            ((eqToHom (congrArg (fun Q ↦ Q.obj
              ((TopCat.Sheaf.pushforwardAb f).obj F)) (hX p)).symm)
              (J.extMk s (p + 1) rfl hs))) =
            I.extMk z (p + 1) rfl hz) := by
  obtain ⟨_, a, ha⟩ :=
    exists_topological_induced_edge_and_map f HX HZ hX hZ
  obtain ⟨edge, hedge⟩ := topological_induced_cocycle_formula f HX HZ hX hZ a ha
  exact ⟨edge, a, ha, hedge⟩

end CategoryTheory
