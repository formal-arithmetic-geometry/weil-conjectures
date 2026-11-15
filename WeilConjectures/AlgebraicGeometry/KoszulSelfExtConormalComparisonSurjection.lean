/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

public import WeilConjectures.AlgebraicGeometry.Modules.Dual

public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

import WeilConjectures.AlgebraicGeometry.KoszulSelfExtConormalLocalComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing

/-! # A surjective Koszul comparison from the dual exterior conormal

## References

* Stacks Project, Tag 0BQY (zero-differential Hom and generator comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem local_surjectivity_on_stalk
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (x : X) (U : X.Opens) (hx : x ∈ U)
    (h : ∀ (W : X.Opens), W ≤ U → Function.Surjective (f.val.app (op W))) :
    Function.Surjective (f.stalkLinearMap x) := by
  intro t
  obtain ⟨W, hWU, hxW, t, rfl⟩ := N.presheaf.exists_le_germ_eq t hx
  obtain ⟨s, hs⟩ := h W hWU t
  refine ⟨M.presheaf.germ W x hxW s, ?_⟩
  rw [Scheme.Modules.Hom.stalkLinearMap_germ]
  exact congrArg (N.presheaf.germ W x hxW) hs

set_option backward.isDefEq.respectTransparency false in
private theorem global_surjective_of_local_maps
    (X : Scheme.{u}) (F T : X.Modules) (W : X → X.Opens)
    (φ : ∀ z : X, F.over (W z) ⟶ T.over (W z))
    (hmem : ∀ z : X, z ∈ W z)
    (hcompat : ∀ (x y : X) (U : X.Opens) (hx : U ≤ W x) (hy : U ≤ W y),
      (φ x).val.app (op (Over.mk (homOfLE hx))) =
        (φ y).val.app (op (Over.mk (homOfLE hy))))
    (hsurj : ∀ (x : X) (U : X.Opens) (hx : U ≤ W x),
      Function.Surjective ((φ x).val.app (op (Over.mk (homOfLE hx))))) :
    ∃ q : F ⟶ T, ∀ z : X, Function.Surjective (q.stalkLinearMap z) := by
  classical
  let f (x : X) : W x ⟶ (⊤ : X.Opens) := homOfLE le_top
  have hcover : Sieve.ofArrows W f ∈ Opens.grothendieckTopology X ⊤ := by
    intro x hx
    exact ⟨W x, f x, Sieve.ofArrows_mk _ _ x, hmem x⟩
  obtain ⟨ψ, hψ, _⟩ := SheafOfModules.existsUnique_hom_of_cover
    X.presheaf X.ringCatSheaf.property F T ⊤ X W f hcover φ (by
      intro x y U a
      exact hcompat x y U (a ≫ pullback.fst (f x) (f y)).le
        (a ≫ pullback.snd (f x) (f y)).le)
  let q : F ⟶ T :=
    { val :=
      { app := fun U ↦ ψ.val.app (op (Over.mk
          (homOfLE le_top : U.unop ⟶ (⊤ : X.Opens))))
        naturality := by
          intro U U' a
          let a' : Over.mk (homOfLE le_top : U'.unop ⟶ (⊤ : X.Opens)) ⟶
              Over.mk (homOfLE le_top : U.unop ⟶ (⊤ : X.Opens)) := Over.homMk a.unop
          exact ψ.val.naturality a'.op } }
  refine ⟨q, ?_⟩
  intro z
  apply local_surjectivity_on_stalk q z (W z) (hmem z)
  intro U hU
  have he := hψ z U (homOfLE hU)
  have hf : homOfLE hU ≫ f z = (homOfLE le_top : U ⟶ (⊤ : X.Opens)) :=
    Subsingleton.elim _ _
  rw [hf] at he
  change Function.Surjective (ψ.val.app
    (op (Over.mk (homOfLE le_top : U ⟶ (⊤ : X.Opens)))))
  rw [he]
  exact hsurj z U hU


set_option backward.isDefEq.respectTransparency false in
/-- Compatible local Koszul comparison maps glue to a stalk-surjective comparison
(Stacks, Tag 0BQY). -/
theorem koszulRegularImmersion_self_ext_conormal_comparison_surjection
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (V : Z.Opens) (n : ℕ)
    (hregular : ∀ z : Z, z ∈ V → ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let T := (Scheme.Modules.restrictFunctor V.ι).obj
      ((Scheme.Modules.tensorPullback i).obj G)
    let F := (Scheme.Modules.restrictFunctor V.ι).obj
      (Scheme.Modules.dual (Scheme.Modules.exteriorPower
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n))
    ∃ φ : F ⟶ T, ∀ z : V.toScheme, Function.Surjective (φ.stalkLinearMap z) := by
  dsimp only
  obtain ⟨W, φ, hmem, hcompat, hsurj⟩ :=
    koszulRegularImmersion_self_ext_conormal_local_comparison i V n hregular
  exact global_surjective_of_local_maps V.toScheme _ _ W φ hmem hcompat hsurj

end AlgebraicGeometry
