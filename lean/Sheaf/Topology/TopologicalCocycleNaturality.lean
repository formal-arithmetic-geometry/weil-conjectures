/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import WeilConjectures.Topology.Sheaves.PushforwardCohomology
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.Injective.Ext

/-! # Naturality of topological cocycle comparisons -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace CategoryTheory
/-- The objectwise comparison maps are natural in the coefficient sheaf.
Source: Stacks Project, Cohomology, Section 20.2 (Tag 01DZ); Derived Categories,
Section 13.18, Lemmas 13.18.6 and 13.18.7, applied to the coefficient-map square.
(blueprint: lem-sc-topological-cocycle-naturality)

Proof: Represent a class by a cocycle in a resolution J of f_*F. Lift any coefficient
map g:F -> G to a map between injective resolutions I and I' and lift f_*g between
J and J'. Choose comparisons J -> f_*I and J' -> f_*I'. The two composites from J
into f_*I' extend the same augmentation map and are homotopic, because f_*I' is
termwise injective. Their global-section maps therefore agree on cohomology.
As a sends the generators to terminal-section generators, precomposition
z maps to a >> f_*z is a bijection Hom(KZ,T) -> Hom(KX,f_*T), natural in T.
Thus for each comparison and source cycle there exists a unique matching z;
the bijection commutes with differentials, so z is a cycle. Apply the formula
for tau to these matching cycles. The Ext functor maps a cycle class by composing
with a resolution lift of the coefficient map (InjectiveResolution.extMk_comp_mk₀).
This identifies the two paths around the naturality square with the composites. Every Ext class
has a cocycle representative, so the
square commutes on every element; extensionality of additive homomorphisms gives
the displayed equality. This also covers degree zero and zero coefficient maps.
-/
theorem topological_cocycle_naturality
    {Z X : TopCat.{u}} (f : Z ⟶ X) [(TopCat.Sheaf.pushforwardAb f).Additive]
    (a : (presheafToSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).obj
        (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶
      (TopCat.Sheaf.pushforwardAb f).obj
        ((presheafToSheaf (Opens.grothendieckTopology Z)
          AddCommGrpCat.{u}).obj
          (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)))
    (ha : ∀ (U : Opens X) (h : U ⟶ (⊤ : Opens X)),
        a.hom.app (op U)
          ((toSheafify (Opens.grothendieckTopology X)
            (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free)).app
              (op U) (FreeAbelianGroup.of h)) =
          (toSheafify (Opens.grothendieckTopology Z)
            (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)).app
              (op ((Opens.map f).obj U))
              (FreeAbelianGroup.of ((Opens.map f).map h ≫
                eqToHom (Opens.map_top f))))
    (τ : ∀ (p : ℕ) (F : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}),
      (Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) p ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).obj
        ((TopCat.Sheaf.pushforwardAb f).obj F) ⟶
      (Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Z) p ⋙
      (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).obj F)
    (hτ : ∀ (F : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
        (I : InjectiveResolution F)
        (J : InjectiveResolution ((TopCat.Sheaf.pushforwardAb f).obj F))
        (φ : J.cocomplex ⟶
          ((TopCat.Sheaf.pushforwardAb f).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex)
        (hφ : J.ι.f 0 ≫ φ.f 0 =
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
        (hsz : a ≫ (TopCat.Sheaf.pushforwardAb f).map z = s ≫ φ.f p),
        τ p F (J.extMk s (p + 1) rfl hs) = I.extMk z (p + 1) rfl hz) :
    ∀ (p : ℕ) {F G : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}}
      (g : F ⟶ G),
      (Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) p ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).map
        ((TopCat.Sheaf.pushforwardAb f).map g) ≫ τ p G =
        τ p F ≫ (Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Z) p ⋙
      (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).map g := by sorry

end CategoryTheory
