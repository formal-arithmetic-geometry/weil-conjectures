/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleComplexFiltrationPageData
public import Mathlib.CategoryTheory.Limits.Final

/-! # Functorial hypercohomology quotient presentations

Source: Stacks Project, Tags 015J, 015K and 0EZM.
(blueprint: lem-weil-pbc-etale-complex-abutment-presentations).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Transport a first-page colimit comparison across a final reindexing.
Source: Stacks Project, Tag 0032, final reindexing of filtered systems.
(blueprint: lem-weil-pbc-etale-complex-first-page-reindexing).

The proof uses the canonical isomorphism between a colimit and the colimit of its
whiskering by a final functor, and the first-page comparison equations. -/
theorem reindex_first_page_comparison
    {I : Type u} [SmallCategory I] {J : Type (u + 1)} [SmallCategory J]
    (R : J ⥤ I) (hR : R.Final)
    (E : I ⥤ SpectralSequence AddCommGrpCat.{u + 1}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
    (E' : SpectralSequence AddCommGrpCat.{u + 1}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
    (v : ∀ i, E.obj i ⟶ E')
    (hcomp : ∀ {i j : I} (f : i ⟶ j), E.map f ≫ v j = v i)
    (hfirst : ∀ (s t : ℤ)
      (ψ : colimit (E ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u + 1}
        (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1 1 ⋙
        HomologicalComplex.eval _ _ ⟨s, t⟩) ⟶ (E'.page 1).X ⟨s, t⟩),
      (∀ i, colimit.ι _ i ≫ ψ = ((v i).hom 1 (by omega)).f ⟨s, t⟩) → IsIso ψ) :
    ∀ (s t : ℤ)
      (ψ : colimit ((R ⋙ E) ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u + 1}
        (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1 1 ⋙
        HomologicalComplex.eval _ _ ⟨s, t⟩) ⟶ (E'.page 1).X ⟨s, t⟩),
      (∀ j, colimit.ι _ j ≫ ψ = ((v (R.obj j)).hom 1 (by omega)).f ⟨s, t⟩) → IsIso ψ := by
  let := hR
  intro s t ψ hψ
  let A := E ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u + 1}
    (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1 1 ⋙
    HomologicalComplex.eval _ _ ⟨s, t⟩
  let Q : Cocone A :=
    { pt := (E'.page 1).X ⟨s, t⟩
      ι :=
        { app := fun i ↦ ((v i).hom 1).f ⟨s, t⟩
          naturality := by
            intro i j f
            let U := SpectralSequence.pageFunctor AddCommGrpCat.{u + 1}
              (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1 1 ⋙
              HomologicalComplex.eval _ _ ⟨s, t⟩
            change U.map (E.map f) ≫ U.map (v j) = U.map (v i) ≫ 𝟙 _
            rw [Category.comp_id, ← U.map_comp, hcomp f] } }
  let : IsIso (colimit.desc A Q) := hfirst s t _ (by
    intro i
    exact colimit.ι_desc Q i)
  have heq : ψ = colimit.pre A R ≫ colimit.desc A Q := by
    apply colimit.hom_ext
    intro j
    change colimit.ι (R ⋙ A) j ≫ ψ =
      colimit.ι (R ⋙ A) j ≫ (colimit.pre A R ≫ colimit.desc A Q)
    rw [← Category.assoc, colimit.ι_pre, colimit.ι_desc]
    exact hψ j
  rw [heq]
  infer_instance

set_option maxHeartbeats 1000000 in
-- The dependent page and quotient witnesses require elaboration together.
/-- Construct the functorial pages and abutment quotient projections, without continuity.
Source: Stacks Project, Tags 015J and 015K; Tag 0EZM, proof of
lemma-colimit-variant-complexes.
(blueprint: lem-weil-pbc-etale-complex-abutment-presentations).

Proof:
1. Choose functorial Cartan--Eilenberg presentations for the bounded-below stage
complexes and the colimit complex. Exact inverse image and degreewise colimits
preserve the bound. The identity and composition equations assemble E0 and v0.
Swap the coordinates to resolution degree first. The first-page identifications
are ordinary term cohomology, and their naturality gives first_transition and
first_comparison. Negative resolution degrees vanish.
2. Choose a small directed final reindexing of I.op. Lift its preorder to universe
u+1 and compose its equivalence with the reindexing to obtain R. Finality is
preserved. This construction uses no geometric limit or continuity hypothesis.
3. The support region is resolution degree >=0 and complex degree >=a. Homology
preserves this vanishing. In bidegree (p-a-n,a+n), both incident differentials
vanish for r>max(p-a-n+1,n), uniformly at every stage and the target.
Functorial convergence identifies that common page with the graded abutment.
4. Transport the limit abutment filtration along eB. Its steps at a+n give S;
the bounds give S 0=top and S (p+1-a).toNat=bottom and it is antitone. If p<a,
the abutment is zero, so both bounds coincide. Transport the stage steps along
eH to give T. Compose the quotient projections with the inverse convergence
isomorphisms to define q and t. Quotient exactness gives the kernel formula and
surjectivity of t. Filtered functoriality and hP,hH,hB identify the underlying
maps with the legs of B, giving membership and the last equation. -/
theorem exists_etale_complex_abutment_presentations
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
    (H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj (op i) ≅
      (cohomology AddCommGrpCat.{u + 1} (D.obj i) p).obj (DerivedCategory.Q.obj (F i)))
    (hH : ∀ (i j : I) (f : j ⟶ i), H.map f.op =
      (eH i).hom ≫ P (D.map f) (F i) ≫
        (cohomology AddCommGrpCat.{u + 1} (D.obj j) p).map
          (DerivedCategory.Q.map (φ f)) ≫ (eH j).inv)
    (L : Cocone G) (hL : IsColimit L)
    (B : Cocone H)
    (eB : B.pt ≅ (cohomology AddCommGrpCat.{u + 1} c.pt p).obj
      (DerivedCategory.Q.obj L.pt))
    (hB : ∀ i : I, B.ι.app (op i) ≫ eB.hom =
      (eH i).hom ≫ P (c.π.app i) (F i) ≫
        (cohomology AddCommGrpCat.{u + 1} c.pt p).map
          (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i)))) :
    ∃ (J : Type (u + 1)) (_ : Preorder J) (_ : IsDirected J (· ≤ ·))
      (_ : Nonempty J) (R : J ⥤ Iᵒᵖ) (_ : R.Final)
      (E0 : Iᵒᵖ ⥤ SpectralSequence AddCommGrpCat.{u + 1}
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
      (S : ℕ → AddSubgroup B.pt),
      S 0 = ⊤ ∧ S (p + 1 - a).toNat = ⊥ ∧ Antitone S ∧
      ∀ n : ℕ, n < (p + 1 - a).toNat →
        ∃ (r : ℤ) (hr : 1 ≤ r) (T : ∀ j : J, AddSubgroup (H.obj (R.obj j)))
          (q : S n →+ (E'.page r hr).X ⟨p - a - n, a + n⟩)
          (t : ∀ j : J, T j →+ ((E0.obj (R.obj j)).page r hr).X ⟨p - a - n, a + n⟩),
          (∀ x : S n, q x = 0 ↔ (x : B.pt) ∈ S (n + 1)) ∧
          (∀ j : J, Function.Surjective (t j)) ∧
          ∀ (j : J) (y : T j),
            ∃ hy : B.ι.app (R.obj j) (y : H.obj (R.obj j)) ∈ S n,
              q ⟨B.ι.app (R.obj j) (y : H.obj (R.obj j)), hy⟩ =
                ((v0 (R.obj j)).hom r hr).f ⟨p - a - n, a + n⟩ (t j y) := by sorry

end AlgebraicGeometry.Etale
