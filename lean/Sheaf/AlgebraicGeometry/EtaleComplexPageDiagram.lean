/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Colimits
public import Sheaf.Paper.EtaleTermwiseHypercohomology
/-! # Coordinate-swapped diagram of functorial hypercohomology pages

Source: Stacks Project, Tags 015J and 0EZM.
(blueprint: lem-weil-pbc-etale-complex-page-diagram).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
-- Elaborate the dependent page and presentation families.
set_option linter.unusedVariables false in
/-- Assemble functorial pullback presentations into a spectral diagram, with coordinates swapped.
Source: Stacks Project, Tags 015J, 015K and 0EZM.

Proof: Send op i to the presentation T₀ of F i, and f.op to its pullback map M.
The identities and composition laws for M, transported through the displayed
canonical inverse-image isomorphisms, give the functor laws. The maps induced by
(c.π.app i, (eG i).inv followed by the cocone leg) form a compatible cocone: use
hG and the cocone equation, and then the composition law. Reindex every page
complex through the coordinate-swap equivalence (x,y) ↦ (y,x); the differential
vector becomes (1-r,r). Transport the successive homology isomorphisms through
this equivalence. Evaluation in a swapped bidegree gives pageIso and pageIsoLimit,
and transport of page morphisms gives their two naturality equations. The global
first-page equation hfirst supplies the ordinary cohomology dictionaries and their
naturality; the presentation's negative-degree vanishing supplies the two negative
resolution-degree statements. No stabilization or filtration comparison is used.
(blueprint: lem-weil-pbc-etale-complex-page-diagram). -/
theorem exists_etaleComplex_page_diagram
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, CochainComplex (Sheaf (D.obj i).smallEtaleTopology
      AddCommGrpCat.{u + 1}) ℤ)
    (φ : ∀ {i j : I} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{u + 1} (D.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id i)))
        (ComplexShape.up ℤ)).hom.app (F i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} (D.obj i))
        (ComplexShape.up ℤ)).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : j ⟶ i) (g : k ⟶ j),
      φ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f)
            (D.map (g ≫ f)) (D.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (D.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ φ g)
    (G : Iᵒᵖ ⥤ CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (eG : ∀ i : I, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{u + 1} (c.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i))
    (hG : ∀ (i j : I) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm) (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (c.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ (eG j).inv)
    (L : Cocone G)
    (hFK : ∀ i : I, CochainComplex.plus
      (Sheaf (D.obj i).smallEtaleTopology AddCommGrpCat.{u + 1}) (F i))
    (hLK : CochainComplex.plus
      (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) L.pt)
    (p q : ℤ)
    (T₀ : ∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
        EtaleTermwiseHypercohomology X K)
      (M : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj),
        (T₀ X K).sequence ⟶ (T₀ Y L).sequence)
    (hfirst : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj) (p : ℕ) (q : ℤ),
        ((M f K L v).hom 1).f (q, (p : ℤ)) ≫ ((T₀ Y L).firstPageIso p q).hom =
          ((T₀ X K).firstPageIso p q).hom ≫
            AddCommGrpCat.ofHom ((Sheaf.H.map (v.f q) p).comp
              (cohomologyMap f (K.obj.X q) p)))
    (hid : ∀ (X : Scheme.{u})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
        M (𝟙 X) K K
            ((NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} X)
              (ComplexShape.up ℤ) ≪≫ Functor.mapHomologicalComplexIdIso
                (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
                  (ComplexShape.up ℤ)).hom.app K.obj) = 𝟙 (T₀ X K).sequence)
    (hcomp : ∀ {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (N : CochainComplex.Plus (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}))
        (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj)
        (w : ((upperStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L.obj ⟶ N.obj),
        M (g ≫ f) K N
            ((Functor.mapHomologicalComplexCompIso
              (upperStarComp AddCommGrpCat.{u + 1} g f).symm
                (ComplexShape.up ℤ)).inv.app K.obj ≫
              ((upperStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
                (ComplexShape.up ℤ)).map v ≫ w) = M f K L v ≫ M g L N w) :
    ∃ (E : Iᵒᵖ ⥤ SpectralSequence AddCommGrpCat.{u + 1}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
      (E' : SpectralSequence AddCommGrpCat.{u + 1}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
      (v : ∀ i : Iᵒᵖ, E.obj i ⟶ E')
      (compatible : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), E.map f ≫ v j = v i)
      (firstIso : ∀ (i : I) (r : ℕ) (s : ℤ),
      ((E.obj (op i)).page 1 (le_refl 1)).X ⟨(r : ℤ), s⟩ ≅ AddCommGrpCat.of (Sheaf.H ((F i).X s) r))
      (firstIsoLimit : ∀ (r : ℕ) (s : ℤ),
      (E'.page 1 (le_refl 1)).X ⟨(r : ℤ), s⟩ ≅ AddCommGrpCat.of (Sheaf.H (L.pt.X s) r))
      (first_transition : ∀ (i j : I) (f : j ⟶ i) (r : ℕ) (s : ℤ),
      ((E.map f.op).hom 1 (le_refl 1)).f ⟨(r : ℤ), s⟩ ≫ (firstIso j r s).hom =
        (firstIso i r s).hom ≫ AddCommGrpCat.ofHom
          ((Sheaf.H.map ((φ f).f s) r).comp (cohomologyMap (D.map f) ((F i).X s) r)))
      (first_comparison : ∀ (i : I) (r : ℕ) (s : ℤ),
      ((v (op i)).hom 1 (le_refl 1)).f ⟨(r : ℤ), s⟩ ≫ (firstIsoLimit r s).hom =
        (firstIso i r s).hom ≫ AddCommGrpCat.ofHom
          ((Sheaf.H.map (((eG i).inv ≫ L.ι.app (op i)).f s) r).comp
            (cohomologyMap (c.π.app i) ((F i).X s) r)))
      (negative : ∀ (i : Iᵒᵖ) (r s : ℤ), r < 0 → IsZero (((E.obj i).page 1 (le_refl 1)).X ⟨r, s⟩))
      (negativeLimit : ∀ r s : ℤ, r < 0 → IsZero ((E'.page 1 (le_refl 1)).X ⟨r, s⟩))
      (pageIso : ∀ (i : I) (r : ℤ) (hr : 1 ≤ r),
        ((E.obj (op i)).page r hr).X ⟨p - q, q⟩ ≅
          ((T₀ (D.obj i) ⟨F i, hFK i⟩).sequence.page r hr).X ⟨q, p - q⟩)
      (pageIsoLimit : ∀ (r : ℤ) (hr : 1 ≤ r),
        (E'.page r hr).X ⟨p - q, q⟩ ≅
          ((T₀ c.pt ⟨L.pt, hLK⟩).sequence.page r hr).X ⟨q, p - q⟩),
      (∀ (i j : I) (f : j ⟶ i) (r : ℤ) (hr : 1 ≤ r),
        ((E.map f.op).hom r hr).f ⟨p - q, q⟩ ≫ (pageIso j r hr).hom =
          (pageIso i r hr).hom ≫
            ((M (D.map f) ⟨F i, hFK i⟩ ⟨F j, hFK j⟩ (φ f)).hom r hr).f ⟨q, p - q⟩) ∧
      (∀ (i : I) (r : ℤ) (hr : 1 ≤ r),
        ((v (op i)).hom r hr).f ⟨p - q, q⟩ ≫ (pageIsoLimit r hr).hom =
          (pageIso i r hr).hom ≫
            ((M (c.π.app i) ⟨F i, hFK i⟩ ⟨L.pt, hLK⟩
              ((eG i).inv ≫ L.ι.app (op i))).hom r hr).f ⟨q, p - q⟩) := by sorry

end AlgebraicGeometry.Etale
