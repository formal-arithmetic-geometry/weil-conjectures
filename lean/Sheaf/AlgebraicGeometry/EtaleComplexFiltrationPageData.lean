/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Sheaf.AlgebraicGeometry.EtaleHypercohomologyFiltration
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Colimits
import Sheaf.Paper.EtaleHypercohomologyPullbackFunctorial
import Sheaf.CategoryTheory.HypercohomologyFirstPage
import Sheaf.CategoryTheory.KInjectiveBridge
import Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Stable-page representatives of the etale image filtration

Source: Stacks Project, Tags 015J and 0EZM.
(blueprint: lem-weil-pbc-etale-complex-filtration-page-data).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The map on ordinary sheaf cohomology in one complex degree, with fixed endpoints.
Source: Stacks Project, Tag 0EZM, the first-page comparison maps.
(blueprint: lem-weil-pbc-etale-complex-filtration-page-data). -/
noncomputable def complexTermCohomologyMap
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (v : ((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ⟶ L) (r : ℕ) (s : ℤ) :
    AddCommGrpCat.of (Sheaf.H (K.X s) r) ⟶ AddCommGrpCat.of (Sheaf.H (L.X s) r) :=
  AddCommGrpCat.ofHom ((Sheaf.H.map (v.f s) r).comp (cohomologyMap f (K.X s) r))

set_option maxHeartbeats 1000000 in
-- The dependent first-page and graded-class witnesses are elaborated together.
set_option linter.unusedVariables false in
/-- Functorial hypercohomology pages identify image-filtration classes with stable pages.
This constructs the pages and their graded-class dictionary; it does not assert
continuity or that a kernel class eventually lies in a deeper step.
Source: Stacks Project, Tag 015J, and Tag 0EZM, proof of Lemma 59.52.1.

Proof: Apply the functorial Cartan--Eilenberg hypercohomology presentation to each
bounded-below complex, every transition pair, and each cocone pair at the limit.
The identity and composition laws give E and the compatible maps v. Swap the two
bidegree coordinates so that resolution degree comes first. The first-page
identifications are ordinary sheaf cohomology; functoriality gives exactly the two
first-page equations. Negative resolution degrees are zero. The limit complex
vanishes below a because inverse image preserves zero objects and complex colimits
are degreewise. The support region r >= 0, s >= a gives a single stable page N in
bidegree (p-q,q), simultaneously for all stages and the limit. Identify that page
with the q-th graded piece of the abutment filtration. This filtration equals the
predicate in the statement: a map T -> F with T zero below q factors through the
stupid truncation F^{>=q}, and its inclusion gives the converse. Define classMap
by the quotient projection and the inverse convergence isomorphism, transporting
along eH. Its kernel is the (q+1)-st step. Naturality gives transition_mem and
class_transition, using hH and hP to identify abutment maps. A class whose canonical
limit image is zero has zero limit graded projection, giving class_limit_zero.
These assertions use no sheaf-continuity or colimit-injectivity assertion.
(blueprint: lem-weil-pbc-etale-complex-filtration-page-data). -/
theorem exists_etaleComplexFiltrationPageData
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
    (q : ℤ) :
    ∃ (E : Iᵒᵖ ⥤ SpectralSequence AddCommGrpCat.{u + 1}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
      (E' : SpectralSequence AddCommGrpCat.{u + 1}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
      (v : ∀ i : Iᵒᵖ, E.obj i ⟶ E')
      (compatible : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), E.map f ≫ v j = v i)
      (firstIso : ∀ (i : I) (r : ℕ) (s : ℤ),
      ((E.obj (op i)).page 1).X ⟨(r : ℤ), s⟩ ≅ AddCommGrpCat.of (Sheaf.H ((F i).X s) r))
      (firstIsoLimit : ∀ (r : ℕ) (s : ℤ),
      (E'.page 1).X ⟨(r : ℤ), s⟩ ≅ AddCommGrpCat.of (Sheaf.H (L.pt.X s) r))
      (first_transition : ∀ (i j : I) (f : j ⟶ i) (r : ℕ) (s : ℤ),
      ((E.map f.op).hom 1).f ⟨(r : ℤ), s⟩ ≫ (firstIso j r s).hom =
        (firstIso i r s).hom ≫ complexTermCohomologyMap (D.map f) (F i) (F j) (φ f) r s)
      (first_comparison : ∀ (i : I) (r : ℕ) (s : ℤ),
      ((v (op i)).hom 1).f ⟨(r : ℤ), s⟩ ≫ (firstIsoLimit r s).hom =
        (firstIso i r s).hom ≫ complexTermCohomologyMap (c.π.app i) (F i) L.pt
          ((eG i).inv ≫ L.ι.app (op i)) r s)
      (negative : ∀ (i : Iᵒᵖ) (r s : ℤ), r < 0 → IsZero (((E.obj i).page 1).X ⟨r, s⟩))
      (negativeLimit : ∀ r s : ℤ, r < 0 → IsZero ((E'.page 1).X ⟨r, s⟩))
      (N : ℤ)
      (one_le : 1 ≤ N)
      (classMap : ∀ (i : I) (x : H.obj (op i)),
      InEtaleHypercohomologyFiltration (D.obj i) (F i) p q ((eH i).hom x) →
        ((E.obj (op i)).page N one_le).X ⟨p - q, q⟩)
      (transition_mem : ∀ (i j : I) (f : j ⟶ i) (x : H.obj (op i)),
      InEtaleHypercohomologyFiltration (D.obj i) (F i) p q ((eH i).hom x) →
        InEtaleHypercohomologyFiltration (D.obj j) (F j) p q
          ((eH j).hom (H.map f.op x)))
      (class_transition : ∀ (i j : I) (f : j ⟶ i) (x : H.obj (op i))
      (hx : InEtaleHypercohomologyFiltration (D.obj i) (F i) p q ((eH i).hom x)),
      (((E.map f.op).hom N one_le).f ⟨p - q, q⟩) (classMap i x hx) =
        classMap j (H.map f.op x) (transition_mem i j f x hx))
      (class_eq_zero_iff : ∀ (i : I) (x : H.obj (op i))
      (hx : InEtaleHypercohomologyFiltration (D.obj i) (F i) p q ((eH i).hom x)),
      classMap i x hx = 0 ↔
        InEtaleHypercohomologyFiltration (D.obj i) (F i) p (q + 1) ((eH i).hom x))
      ,
      ∀ (i : I) (x : H.obj (op i))
    (hx : InEtaleHypercohomologyFiltration (D.obj i) (F i) p q ((eH i).hom x)),
    ((eH i).hom ≫ P (c.π.app i) (F i) ≫
      (cohomology AddCommGrpCat.{u + 1} c.pt p).map
        (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i)))) x = 0 →
    (((v (op i)).hom N one_le).f ⟨p - q, q⟩) (classMap i x hx) = 0 := by sorry


end AlgebraicGeometry.Etale
