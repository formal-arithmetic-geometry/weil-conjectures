/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import WeilConjectures.Topology.Sheaves.PushforwardCohomology
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution


/-! # Comparing topological resolution cocycles -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace CategoryTheory

/-- A cocycle on a resolution of f_*F can be compared with a resolution of F
and lifted uniquely as a terminal-section cocycle on the latter.

Source: Stacks Project, Tag 01F2 and the injective-resolution comparison construction,
with terminal sections represented by the free abelian terminal sheaf (Tag 01DZ).
(blueprint: lem-sc-topological-resolution-cocycle-lift)

Proof: Every term of f_*I is injective, since inverse image is exact and left adjoint
to direct image. Extend f_*(I.ι) across the monomorphism J.ι in degree zero using
injectivity. Inductively factor the preceding differential through the cokernel of
the preceding source differential, using exactness of the augmented resolution J;
extend across its monomorphism into the next term of J using injectivity of the
corresponding term of f_*I. This constructs phi and its augmentation equation.
The terminal-section representation gives a bijection between maps KZ -> I^p
and maps KX -> f_*I^p, realized by z mapping to a composed with f_*z: ha specifies
this bijection on the sheafification generators, which determine the morphism.
Apply its inverse to s composed with phi^p to obtain z and the stated equality.
The chain-map identity and hs make s composed with phi^p a cocycle. Apply the
same terminal-section bijection in degree p+1 to deduce hz. This argument uses
no exactness of f_* and works in degree zero and for the zero sheaf.
-/
theorem exists_topological_resolution_cocycle_lift
    {Z X : TopCat.{u}} (f : Z ⟶ X) [(TopCat.Sheaf.pushforwardAb f).Additive]
    (a : (presheafToSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).obj
        (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶
      (TopCat.Sheaf.pushforwardAb f).obj
        ((presheafToSheaf (Opens.grothendieckTopology Z)
          AddCommGrpCat.{u}).obj
          (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)))
    (ha : (∀ (U : Opens X) (h : U ⟶ (⊤ : Opens X)),
        a.hom.app (op U)
          ((toSheafify (Opens.grothendieckTopology X)
            (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free)).app
              (op U) (FreeAbelianGroup.of h)) =
          (toSheafify (Opens.grothendieckTopology Z)
            (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)).app
              (op ((Opens.map f).obj U))
              (FreeAbelianGroup.of ((Opens.map f).map h ≫
                eqToHom (Opens.map_top f)))))
    (F : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((TopCat.Sheaf.pushforwardAb f).obj F))
    (p : ℕ)
    (s : (presheafToSheaf (Opens.grothendieckTopology X)
          AddCommGrpCat.{u}).obj
          (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶
            J.cocomplex.X p)
    (hs : s ≫ J.cocomplex.d p (p + 1) = 0) :
    ∃ (φ : J.cocomplex ⟶
          ((TopCat.Sheaf.pushforwardAb f).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex),
      J.ι.f 0 ≫ φ.f 0 = (TopCat.Sheaf.pushforwardAb f).map (I.ι.f 0) ∧
      ∃ (z : (presheafToSheaf (Opens.grothendieckTopology Z)
          AddCommGrpCat.{u}).obj
          (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free) ⟶
            I.cocomplex.X p),
        z ≫ I.cocomplex.d p (p + 1) = 0 ∧
        a ≫ (TopCat.Sheaf.pushforwardAb f).map z = s ≫ φ.f p := by sorry

end CategoryTheory
