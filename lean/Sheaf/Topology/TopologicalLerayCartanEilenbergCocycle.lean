/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import WeilConjectures.Topology.Sheaves.PushforwardCohomology
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic

public import Sheaf.CategoryTheory.Filtration
import Sheaf.CategoryTheory.GrothendieckSpectralSequence
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions

/-! # Cartan--Eilenberg Leray construction on cocycles -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace CategoryTheory

/-- Construct the Leray pages and finite filtration, computing their bottom composite
on injective-resolution cocycles, without any prescribed cohomology map.

Source: Stacks Project, Tags 015N, 015J and 01F2, the second Cartan--Eilenberg
spectral sequence and its resolution-degree-zero augmentation.
(blueprint: lem-sc-topological-leray-cartan-eilenberg-cocycle)

Proof: Use direct image followed by terminal sections. Both functors are additive and
left exact; direct image preserves injectives, which are sections-acyclic. Apply the
Cartan--Eilenberg Grothendieck construction. Its E2 comparison identifies the terms
with R^b f_* followed by HX a. The equality of terminal sections of f_*F and F,
and the canonical injective-resolution cohomology computation, identify its abutment
with HZ. Transport these comparisons along hX and hZ. Resolution comparisons induce
page maps independent of the lifts from page two onward and preserve the total
comparison and image filtration, so pages, comparisons and filtration assemble in
the functor category. Use the second filtration on the total complex for T and g.
The first-quadrant bounds give top in step zero and bottom in step n+1. Differentials
vanish once r > max(p,q+1), so the stated pageInfinity convention stabilizes.
The bottom outgoing differential is zero; invert iCycles and compose with homology
projection and the next-page comparison to form t. Iterate from the identity for b.
The bottom filtration quotient has zero denominator, yielding k and its quotient
identity. The canonical derived-zero comparison gives e0. The total augmentation
in resolution degree zero computes this bottom composite on a cocycle s by the
comparison phi into f_*I. Terminal-section representation, with its generator map
specified by ha, identifies its image with z when a composed with f_*z equals
s composed with phi. The canonical abutment comparison identifies this class with
I.extMk z; this proves the displayed equation for every comparison and every cocycle.
No conclusion equating a prescribed edge with this composite is asserted here.
-/
theorem exists_topological_leray_cartan_eilenberg_cocycle
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
                eqToHom (Opens.map_top f)))))
 :
    ∃ E : E₂CohomologicalSpectralSequenceNat
        (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}),
      ∃ e₂ : ∀ a b : ℕ, (E.page 2).X (a, b) ≅
          (TopCat.Sheaf.pushforwardAb f).rightDerived b ⋙ HX a,
        (∀ a b : ℕ, ∃ (R : ℤ) (_hR : 2 ≤ R), ∀ (r : ℤ) (hr : R ≤ r),
          Nonempty ((E.page r (by omega)).X (a, b) ≅ E.pageInfinity (a, b))) ∧
        ∃ T : ∀ n : ℕ, DecreasingFiltration (HZ n),
          (∀ n, (T n).step 0 = ⊤) ∧
          (∀ n, (T n).step (n + 1) = ⊥) ∧
          ∃ g : ∀ p q : ℕ, (T (p + q)).gradedPiece p ≅ E.pageInfinity (p, q),
            ∃ e₀ : ∀ p : ℕ,
                TopCat.Sheaf.pushforwardAb f ⋙ HX p ≅ (E.page 2).X (p, 0),
              (∀ p, (e₀ p).hom =
                Functor.whiskerRight (TopCat.Sheaf.pushforwardAb f).toRightDerivedZero
                  (HX p) ≫ (e₂ p 0).inv) ∧
              ∃ t : ∀ (p : ℕ) (r : ℤ) (hr : 2 ≤ r),
                  (E.page r hr).X (p, 0) ⟶ (E.page (r + 1) (by omega)).X (p, 0),
                (∀ (p : ℕ) (r : ℤ) (hr : 2 ≤ r),
                  (E.page r hr).iCycles (p, 0) ≫ t p r hr =
                    (E.page r hr).homologyπ (p, 0) ≫ (E.iso r (r + 1) (p, 0) rfl hr).hom) ∧
                ∃ b : ∀ (p : ℕ) (r : ℤ) (hr : 2 ≤ r),
                    (E.page 2).X (p, 0) ⟶ (E.page r hr).X (p, 0),
                  (∀ p, b p 2 (by omega) = 𝟙 _) ∧
                  (∀ (p : ℕ) (r : ℤ) (hr : 2 ≤ r),
                    b p (r + 1) (by omega) = b p r hr ≫ t p r hr) ∧
                  ∃ k : ∀ p : ℕ, E.pageInfinity (p, 0) ≅ ((T p).step p :
                      Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⥤
                        AddCommGrpCat.{u}),
                    (∀ p, cokernel.π (Subobject.ofLE ((T p).step (p + 1))
                      ((T p).step p) ((T p).antitone_step (by omega))) ≫
                        (g p 0).hom = (k p).inv) ∧
                    ∃ bottom : ∀ p : ℕ, TopCat.Sheaf.pushforwardAb f ⋙ HX p ⟶ HZ p,
                      (∀ p, bottom p = (e₀ p).hom ≫ b p (p + 2) (by omega) ≫
                        (k p).hom ≫ ((T p).step p).arrow) ∧
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
          ((bottom p).app F
            ((eqToHom (congrArg (fun Q ↦ Q.obj
              ((TopCat.Sheaf.pushforwardAb f).obj F)) (hX p)).symm)
              (J.extMk s (p + 1) rfl hs))) =
            I.extMk z (p + 1) rfl hz) := by sorry

end CategoryTheory
