/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import WeilConjectures.Topology.Sheaves.PushforwardCohomology
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB

/-! # Terminal-section resolution computations and Ext cocycles

Source: Stacks Project, Tags 01FT, 06XR and 01F2, injective-resolution cohomology computation.
(blueprint: lem-sc-topological-terminal-resolution-ext-comparison)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace CategoryTheory

/-- Terminal sections and terminal Ext cohomology admit comparisons compatible
with the homology map of any augmented resolution comparison. No spectral object
or edge map occurs in this statement.

Source: Stacks Project, Tags 01FT, 06XR and 01F2, cohomology of an injective resolution.
(blueprint: lem-sc-topological-terminal-resolution-ext-comparison)

Proof: Sheafification adjunction, the free abelian adjunction, and Yoneda identify
Hom from the free terminal sheaf with sections at the terminal open, additively
and naturally. Apply this identification degreewise to the chosen injective
resolution, then take homology. Ext computed from that resolution gives x in
every degree, natural in the sheaf by resolution comparison and homotopy
independence. The same construction on Z gives the comparison for Z sections.
The generator identity ha identifies sections of f_*M on X with sections of M
on Z; the inverse is restriction along the equality f^{-1}(top)=top. This is an
isomorphism of additive functors. Derive it and compose with the Z comparison to
obtain zc for the composite f_* followed by X sections. The degreewise Hom/section
identifications take s composed with phi to z, because a composed with f_*z is
s composed with phi. Thus the induced homology map sends the represented Ext
class to I.extMk z. The canonical right-derived resolution comparisons in the
formula are precisely the endpoint identifications in this computation.
Naturality of the Hom/section isomorphism and homotopy independence extend the
calculation from chosen resolutions to every I,J and augmented phi.
Empty spaces and degree zero require no separate assumption: Yoneda and the
sheafification adjunction apply there too, and negative resolution degrees are zero.
-/
theorem exists_topological_terminal_resolution_ext_comparison
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
                eqToHom (Opens.map_top f))))) :
    let G := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
    ∃ x : ∀ n : ℕ, G.rightDerived n ≅
        Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n ⋙
          (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤),
      ∃ zc : ∀ n : ℕ, (TopCat.Sheaf.pushforwardAb f ⋙ G).rightDerived n ≅
          Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Z) n ⋙
            (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤),
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
        (zc p).hom.app F
          ((I.isoRightDerivedObj (TopCat.Sheaf.pushforwardAb f ⋙ G) p).inv
            (HomologicalComplex.homologyMap
              ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) p
              ((J.isoRightDerivedObj G p).hom
                ((x p).inv.app ((TopCat.Sheaf.pushforwardAb f).obj F)
                  (J.extMk s (p + 1) rfl hs))))) =
            I.extMk z (p + 1) rfl hz) := by sorry

end CategoryTheory
