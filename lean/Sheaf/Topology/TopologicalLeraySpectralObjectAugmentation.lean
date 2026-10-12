/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import WeilConjectures.Topology.Sheaves.PushforwardCohomology
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import Sheaf.CategoryTheory.GrothendieckSpectralSequence
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB

/-! # The topological Leray spectral object and its augmentation

Source: Stacks Project, Tags 015N, 015J and 01F2.
(blueprint: lem-sc-topological-leray-spectral-object-augmentation)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite ComposableArrows

namespace CategoryTheory

/-- The spectral object before extracting pages or a filtration, with its canonical
abutment and single-interval comparisons and the bottom augmentation on cocycles.

Source: Stacks Project, Tags 015N, 015J and 01F2.
(blueprint: lem-sc-topological-leray-spectral-object-augmentation)

Proof: Apply the Grothendieck construction to direct image and terminal sections.
Direct image preserves injectives; terminal sections is left exact. Mathlib
supplies the Grothendieck abelian and enough-injectives instances for abelian
sheaves on the small opens sites; no unbounded K-injective resolution is needed. The truncations
of the derived direct image give a first-quadrant spectral object, with interval
cohomology R^p Gamma_X(R^q f_* F). Use the Cartan--Eilenberg total augmentation
and its acyclic first filtration to compare the total cohomology with Gamma_Z(I).
These comparisons are natural: lifts of sheaf maps to resolutions and their
Cartan--Eilenberg resolutions are homotopic, and hence act identically on the
spectral object and on total cohomology. Identify the interval and abutment functors
with HX and HZ using hX and hZ. The bottom spectral-object map comes from the
resolution-degree-zero augmentation. On a resolution cocycle s its comparison
into f_*I is s followed by phi. The formula for a identifies global sections of
f_*I with those of I, so a followed by f_*z = s followed by phi identifies the
resulting cocycle with z. The canonical injective-resolution cohomology comparison
then gives I.extMk z. Comparison homotopies prove this for every I,J,phi, not just
the chosen resolutions. No pages, transitions, or filtration factorization are
asserted here; these belong to the separate generic spectral-object argument.
-/
theorem exists_topological_leray_spectral_object_augmentation
    {Z X : TopCat.{u}} (f : Z ⟶ X) [(TopCat.Sheaf.pushforwardAb f).Additive]
    (HX : ℕ → (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}))
    (HZ : ℕ → (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}))
    (hX : ∀ n, HX n = Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤))
    (hZ : ∀ n, HZ n = Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Z) n ⋙
      (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤))
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
                eqToHom (Opens.map_top f))))) :
    ∃ Y : Abelian.SpectralObject
        (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}) EInt,
      ∃ hY : Y.IsFirstQuadrant,
        ∃ h : ∀ n : ℕ, (Y.H n).obj
            (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≅ HZ n,
          ∃ e : ∀ p q : ℕ, (Y.H (p + q : ℕ)).obj
              (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q + 1 : ℤ) : EInt) by simp))) ≅
                (TopCat.Sheaf.pushforwardAb f).rightDerived q ⋙ HX p,
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
          ((Functor.whiskerRight (TopCat.Sheaf.pushforwardAb f).toRightDerivedZero
              (HX p) ≫ (e p 0).inv ≫
            (@Abelian.SpectralObject.bottomEdge _ _ _ Y hY p) ≫ (h p).hom).app F
            ((eqToHom (congrArg (fun Q ↦ Q.obj
              ((TopCat.Sheaf.pushforwardAb f).obj F)) (hX p)).symm)
              (J.extMk s (p + 1) rfl hs))) =
            I.extMk z (p + 1) rfl hz) := by sorry

end CategoryTheory
