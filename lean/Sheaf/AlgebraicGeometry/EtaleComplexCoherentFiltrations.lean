/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleComplexFiltrationPageData
public import Sheaf.CategoryTheory.Filtration
import Sheaf.CategoryTheory.HypercohomologyFirstPage
import Sheaf.CategoryTheory.KInjectiveBridge
import Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence
import Sheaf.AlgebraicGeometry.EtalePresentationImageFiltration
import Sheaf.AlgebraicGeometry.EtaleHypercohomologyFiltration
import Sheaf.Paper.EtaleHypercohomologyPullbackFunctorial

/-! # Coherent categorical filtrations for an etale complex diagram

Source: Stacks Project, Tags 015J, 015K and 0EZM.
(blueprint: lem-weil-pbc-etale-complex-coherent-filtrations).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option maxHeartbeats 1000000 in
-- Elaborate the dependent page isomorphisms and all filtration-degree witnesses.
set_option linter.unusedVariables false in
/-- One diagram of pages with categorical abutment filtrations at every degree.
This statement constructs no reindexing, subgroup presentation, or quotient homomorphism.
Source: Stacks Project, Tags 015J and 015K; the finite-support argument of Tag 0EZM.

Proof:
1. Apply the functorial Cartan--Eilenberg construction to the stage complexes and
   the degreewise colimit of their inverse images. Exact inverse image and degreewise
   colimits preserve the lower bound a. Identity and composition for the coefficient
   maps assemble the spectral-sequence functor and its compatible maps to the target.
   Swap coordinates to resolution degree first. The natural first-page isomorphisms
   give the two displayed equations; negative resolution degrees vanish.
2. Use the canonical image filtrations on degree-p hypercohomology. The step at a
   is the whole object, since the complex is supported above a. Steps above p vanish
   since the truncated complex and its derived global sections are supported above p.
   If p<a, hypercohomology itself vanishes, so the step at a is also zero. This gives
   the upper bound at max a (p+1) without excluding the zero-length case.
3. For each q, choose r>max(p-q+1,q-a) with r>=1. Both incident differentials at
   (p-q,q) vanish, at all stages and the target. Subquotient convergence identifies
   this common page with each categorical graded piece. All q use the same pages and
   filtrations chosen in step 1; only r and the convergence isomorphisms depend on q.
4. Pullback preserves each canonical image-filtration step. Restrict the abutment
   map to these steps; monicity proves the square for their inclusions. Naturality
   of the convergence isomorphisms identifies its graded map with cokernel.map.
   The specified formula hP fixes its underlying abutment map. No continuity or
   surjectivity of any page comparison is used.
(blueprint: lem-weil-pbc-etale-complex-coherent-filtrations). -/
theorem exists_etale_complex_coherent_filtrations
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
    (a : ℤ) (hbelow : ∀ (i : I) (n : ℤ), n < a → IsZero ((F i).X n))
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
    (p : ℤ)
    (P : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      (cohomology AddCommGrpCat.{u + 1} Y p).obj (DerivedCategory.Q.obj K) ⟶
      (cohomology AddCommGrpCat.{u + 1} X p).obj
        (DerivedCategory.Q.obj
          (((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)))
    (hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      P f K = (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} p).map
        ((rightDerivedGlobalSections AddCommGrpCat.{u + 1} Y).map
          ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
            (DerivedCategory.Q.obj K)) ≫
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar AddCommGrpCat.{u + 1} f)
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1})
          (Functor.isoWhiskerLeft (lowerStar AddCommGrpCat.{u + 1} f)
              (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
                terminalIsTerminal) ≪≫
            lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f ≪≫
            (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
              terminalIsTerminal).symm)).hom.app
                ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory.obj
                  (DerivedCategory.Q.obj K)) ≫
        (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
          ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryFactors.hom.app K)))
    (L : Cocone G) (hL : IsColimit L) :
    ∃ (E0 : Iᵒᵖ ⥤ SpectralSequence AddCommGrpCat.{u + 1}
        (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
      (E' : SpectralSequence AddCommGrpCat.{u + 1}
        (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
      (v0 : ∀ i : Iᵒᵖ, E0.obj i ⟶ E')
      (compatible : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), E0.map f ≫ v0 j = v0 i)
      (firstIso : ∀ (i : I) (r : ℕ) (s : ℤ),
      ((E0.obj (op i)).page 1).X ⟨(r : ℤ), s⟩ ≅ AddCommGrpCat.of (Sheaf.H ((F i).X s) r))
      (firstIsoLimit : ∀ (r : ℕ) (s : ℤ),
      (E'.page 1).X ⟨(r : ℤ), s⟩ ≅ AddCommGrpCat.of (Sheaf.H (L.pt.X s) r))
      (first_transition : ∀ (i j : I) (f : j ⟶ i) (r : ℕ) (s : ℤ),
      ((E0.map f.op).hom 1).f ⟨(r : ℤ), s⟩ ≫ (firstIso j r s).hom =
        (firstIso i r s).hom ≫ complexTermCohomologyMap (D.map f) (F i) (F j) (φ f) r s)
      (first_comparison : ∀ (i : I) (r : ℕ) (s : ℤ),
      ((v0 (op i)).hom 1).f ⟨(r : ℤ), s⟩ ≫ (firstIsoLimit r s).hom =
        (firstIso i r s).hom ≫ complexTermCohomologyMap (c.π.app i) (F i) L.pt
          ((eG i).inv ≫ L.ι.app (op i)) r s)
      (negative : ∀ (i : Iᵒᵖ) (r s : ℤ), r < 0 → IsZero (((E0.obj i).page 1).X ⟨r, s⟩))
      (negativeLimit : ∀ r s : ℤ, r < 0 → IsZero ((E'.page 1).X ⟨r, s⟩))
      (V : ∀ i : I, DecreasingFiltration
        ((cohomology AddCommGrpCat.{u + 1} (D.obj i) p).obj (DerivedCategory.Q.obj (F i))))
      (W : DecreasingFiltration
        ((cohomology AddCommGrpCat.{u + 1} c.pt p).obj (DerivedCategory.Q.obj L.pt))),
      W.step a = ⊤ ∧ W.step (max a (p + 1)) = ⊥ ∧
      ∀ q : ℤ, ∃ (r : ℤ) (hr : 1 ≤ r)
        (e : ∀ i : I, ((E0.obj (op i)).page r hr).X ⟨p - q, q⟩ ≅ (V i).gradedPiece q)
        (e' : (E'.page r hr).X ⟨p - q, q⟩ ≅ W.gradedPiece q),
        ∀ i : I,
          ∃ (t : ∀ z : ℤ, ((V i).step z : AddCommGrpCat.{u + 1}) ⟶
              (W.step z : AddCommGrpCat.{u + 1}))
            (ht : ∀ z : ℤ, t z ≫ (W.step z).arrow =
              ((V i).step z).arrow ≫ P (c.π.app i) (F i) ≫
                (cohomology AddCommGrpCat.{u + 1} c.pt p).map
                  (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i))))
            (hc : ∀ z : ℤ,
              Subobject.ofLE ((V i).step (z + 1)) ((V i).step z)
                  ((V i).antitone_step (Int.le_add_one (le_refl z))) ≫ t z =
                t (z + 1) ≫ Subobject.ofLE (W.step (z + 1)) (W.step z)
                  (W.antitone_step (Int.le_add_one (le_refl z)))),
            ((v0 (op i)).hom r hr).f ⟨p - q, q⟩ ≫ e'.hom =
              (e i).hom ≫ cokernel.map _ _ (t (q + 1)) (t q) (hc q) := by sorry

end AlgebraicGeometry.Etale
