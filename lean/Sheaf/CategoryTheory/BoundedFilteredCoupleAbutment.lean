/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Sheaf.CategoryTheory.ExactCoupleConvergence
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.CategoryTheory.FilteredCohomologyDiagonalColimit
import Sheaf.CategoryTheory.FiniteCoconeExactCouple

/-!
# Finite abutment of a filtered-complex exact couple

Source: Stacks Project, Homology, Lemma 12.24.11.
(blueprint: lem-sp-bounded-filtered-couple-abutment).
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

private theorem finite_separated_exhaustive {C : Type u} [Category.{v} C] [Abelian C]
    {T : C} (F : DecreasingFiltration T) (hF : F.IsFinite) :
    F.IsSeparated ∧ F.IsExhaustive := by
  obtain ⟨a, b, ha, hb⟩ := hF
  constructor
  · intro V hV
    exact le_bot_iff.mp (hb ▸ hV b)
  · intro V hV
    exact top_le_iff.mp (ha ▸ hV a)

private theorem finite_inverseLimit {C : Type u} [Category.{v} C] [Abelian C]
    {T : C} (F : DecreasingFiltration T) (hF : F.IsFinite) :
    BigradedExactCouple.IsInverseLimit F := by
  obtain ⟨a, b, ha, hb⟩ := hF
  have hz (p : ℤ) (hp : b ≤ p) : (F.step p).arrow = 0 := by
    have he : F.step p = ⊥ := le_bot_iff.mp (hb ▸ F.antitone_step hp)
    rw [he, Subobject.bot_arrow]
  have hπ (p : ℤ) (hp : b ≤ p) : IsIso (cokernel.π (F.step p).arrow) := by
    rw [hz p hp]
    infer_instance
  intro S f hf
  let := hπ b le_rfl
  let h : S ⟶ T := f b ≫ inv (cokernel.π (F.step b).arrow)
  have hcomm (p : ℤ) : h ≫ cokernel.π (F.step p).arrow = f p := by
    refine Int.inductionOn' (motive := fun p ↦
      h ≫ cokernel.π (F.step p).arrow = f p) p b ?_ ?_ ?_
    · simp [h]
    · intro p hp ih
      have hw : cokernel.π (F.step (p + 1)).arrow ≫
          BigradedExactCouple.quotientTransition F p = cokernel.π (F.step p).arrow := by
        simp [BigradedExactCouple.quotientTransition]
      let := hπ p hp
      let := hπ (p + 1) (by omega)
      have hc : IsIso (cokernel.π (F.step (p + 1)).arrow ≫
          BigradedExactCouple.quotientTransition F p) := hw ▸ inferInstance
      let := (isIso_comp_left_iff (cokernel.π (F.step (p + 1)).arrow)
        (BigradedExactCouple.quotientTransition F p)).mp hc
      apply (cancel_mono (BigradedExactCouple.quotientTransition F p)).mp
      rw [Category.assoc, hw, hf p, ih]
    · intro p _ ih
      have ih' : h ≫ cokernel.π (F.step (p - 1 + 1)).arrow = f (p - 1 + 1) := by
        rw [show p - 1 + 1 = p by omega]
        exact ih
      calc
        h ≫ cokernel.π (F.step (p - 1)).arrow =
            h ≫ cokernel.π (F.step (p - 1 + 1)).arrow ≫
              BigradedExactCouple.quotientTransition F (p - 1) := by
          simp [BigradedExactCouple.quotientTransition]
        _ = f (p - 1 + 1) ≫ BigradedExactCouple.quotientTransition F (p - 1) := by
          rw [← Category.assoc, ih']
        _ = f (p - 1) := hf (p - 1)
  refine ⟨h, hcomm, ?_⟩
  intro k hk
  apply (cancel_mono (cokernel.π (F.step b).arrow)).mp
  exact (hk b).trans (hcomm b).symm

private theorem homology_image_top {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (V : Subobject K) (hV : V = ⊤) (n : ℤ) :
    imageSubobject (HomologicalComplex.homologyMap V.arrow n) = ⊤ := by
  let : IsIso V.arrow := (Subobject.isIso_arrow_iff_eq_top V).mpr hV
  let : IsIso (HomologicalComplex.homologyMap V.arrow n) :=
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).map_isIso V.arrow
  rw [imageSubobject_mono]
  exact Subobject.mk_eq_top_of_isIso _

private theorem homology_image_bot {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (V : Subobject K) (hV : V = ⊥) (n : ℤ) :
    imageSubobject (HomologicalComplex.homologyMap V.arrow n) = ⊥ := by
  have hz : V.arrow = 0 := by rw [hV, Subobject.bot_arrow]
  simp [hz]

/-- A couple with the filtration inclusion and quotient maps has the finite cohomology
image filtration as abutment. Source: Stacks Project, Homology, Lemma 12.24.11;
blueprint thm-sp-spectral-object-yields, step 5
(blueprint: lem-sp-bounded-filtered-couple-abutment).

Proof: Put G^p H^n=image(H^n(F^p) to H^n(K)). Inclusion of successive filtration
steps makes these images decreasing. If F^a=K and F^b=0, G^a is the whole
cohomology and G^b is zero, giving finiteness and separation. The D diagonal
identified by eD has a constant bottom tail H^n(K), with identity transition maps
under hAlpha. The maps from each D term induced by inclusion therefore define its
colimit A with comparison aH and the stated cocone equation. Exact-couple
recursion identifies limiting cycles with the inverse image under f of the
eventual incoming alpha image, and limiting boundaries with gamma of the kernel
of a sufficiently long outgoing alpha iterate. The finite tails make these
subobjects stationary and give L and regularity. Using hGamma, the resulting
quotient of stationary cycles by stationary boundaries is the quotient of
image(H^n(F^p) to H^n(K)) by image(H^n(F^(p+1)) to H^n(K)). The canonical maps
from D to this quotient and to its image-filtration graded piece are epi with
the same kernel, giving weak convergence and the displayed infinite-page
isomorphism. The finite image filtration is separated and exhaustive. Its
quotient inverse system is constant at the whole object in the zero-step tail,
so its canonical cone is a limit. This proves ConvergesTo in all total degrees.
No first-quadrant assumption is used; the finite tails suffice. -/
theorem boundedFilteredComplex_coupleAbutment
    (C : Type u) [Category.{v} C] [Abelian C]
    (S : ObjectProperty.FullSubcategory
          (fun U : FilteredObject (CochainComplex C ℤ) ↦ U.filtration.IsFinite) ⥤
        CohomologicalSpectralSequence C 1)
      (e₁ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
          (p q : ℤ),
        ((S.obj U).page 1).X (p, q) ≅
        (U.obj.filtration.gradedPiece p).homology (p + q))
    (U : ObjectProperty.FullSubcategory
      (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
    (X : BigradedExactCouple C 0)
          (eD : ∀ P Q : ℤ, X.D P Q ≅
            (U.obj.filtration.step (-Q) : CochainComplex C ℤ).homology (P + Q))
          (eC : ∀ (s : ℕ) (p q : ℤ),
            (X.pageCouple s).E (2 * p + q) (-p) ≅
              ((S.obj U).page (s + 1) (by omega)).X (p, q))
    (hα : ∀ P Q : ℤ,
            X.alpha P Q ≫ (eD (P - 1) (Q + 1)).hom =
              (eD P Q).hom ≫ HomologicalComplex.homologyMap
                (Subobject.ofLE (U.obj.filtration.step (-Q))
                  (U.obj.filtration.step (-(Q + 1)))
                  (U.obj.filtration.antitone_step (by omega))) (P + Q) ≫
                eqToHom (by rw [show P - 1 + (Q + 1) = P + Q by omega]))
    (hγ : ∀ P Q : ℤ,
            X.initialG P Q ≫ eqToHom (by congr 1 <;> omega) ≫
                (eC 0 (-Q) (P + 2 * Q)).hom ≫ (e₁ U (-Q) (P + 2 * Q)).hom ≫
                eqToHom (by
                  rw [show -Q + (P + 2 * Q) = P + Q by omega]
                  rfl) =
              (eD P Q).hom ≫ HomologicalComplex.homologyMap
                (U.obj.filtration.complexQuotientπ (-Q) (-Q + 1) (by omega)) (P + Q))
 :
    ∃ (G : ∀ n : ℤ, DecreasingFiltration (U.obj.obj.homology n))
      (L : X.LimitSubobjects) (A : ∀ n : ℤ, X.AlphaColimit n)
      (aH : ∀ n : ℤ, (A n).obj ≅ U.obj.obj.homology n),
          (∀ n p : ℤ, (G n).step p =
            imageSubobject (HomologicalComplex.homologyMap
              (U.obj.filtration.step p).arrow n)) ∧
          (∀ n : ℤ, (G n).IsFinite ∧ (G n).IsSeparated) ∧
          (∀ n P : ℤ,
            (A n).ι P ≫ (aH n).hom =
              (eD P (n - P)).hom ≫ eqToHom (by
                rw [show -(n - P) = P - n by omega, show P + (n - P) = n by omega]) ≫
                HomologicalComplex.homologyMap
                  (U.obj.filtration.step (P - n)).arrow n) ∧
          X.ConvergesTo L A ∧
          (∀ p q : ℤ, Nonempty
            (X.pageInfinity L (2 * p + q) (-p) ≅ (G (p + q)).gradedPiece p)) := by
  classical
  have _ := hγ
  obtain ⟨hcomm, hcolim⟩ := filteredCohomologyDiagonal_isColimit U.obj U.property X eD hα
  let A : ∀ n : ℤ, X.AlphaColimit n := fun n ↦
    { obj := U.obj.obj.homology n
      ι := filteredCohomologyDiagonalMap U.obj X eD n
      comm := hcomm n
      isColimit := hcolim n }
  have hi (n P : ℤ) : imageSubobject ((A n).ι P) =
      imageSubobject (HomologicalComplex.homologyMap
        (U.obj.filtration.step (P - n)).arrow n) := by
    dsimp [A, filteredCohomologyDiagonalMap]
    rw [imageSubobject_iso_comp, imageSubobject_iso_comp]
  obtain ⟨a, b, ha, hb⟩ := U.property
  have htop (p : ℤ) (hp : p ≤ a) : U.obj.filtration.step p = ⊤ :=
    top_le_iff.mp (ha ▸ U.obj.filtration.antitone_step hp)
  have hbot (p : ℤ) (hp : b ≤ p) : U.obj.filtration.step p = ⊥ :=
    le_bot_iff.mp (hb ▸ U.obj.filtration.antitone_step hp)
  have hfinite (n : ℤ) : (X.imageFiltration n (A n)).IsFinite := by
    refine ⟨a + n, b + n, ?_, ?_⟩
    · change imageSubobject ((A n).ι (a + n)) = ⊤
      rw [hi]
      exact homology_image_top _ (htop _ (by omega)) n
    · change imageSubobject ((A n).ι (b + n)) = ⊥
      rw [hi]
      exact homology_image_bot _ (hbot _ (by omega)) n
  have htails : ∀ n : ℤ, ∃ a b : ℤ,
      (∀ P : ℤ, P ≤ a → IsIso ((A n).ι P)) ∧
      (∀ P : ℤ, b ≤ P → IsZero (X.D P (n - P))) := by
    intro n
    refine ⟨a + n, b + n, ?_, ?_⟩
    · intro P hP
      have he := htop (P - n) (by omega)
      let : IsIso (U.obj.filtration.step (P - n)).arrow :=
        (Subobject.isIso_arrow_iff_eq_top _).mpr he
      let : IsIso (HomologicalComplex.homologyMap
          (U.obj.filtration.step (P - n)).arrow n) :=
        (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).map_isIso _
      dsimp [A, filteredCohomologyDiagonalMap]
      infer_instance
    · intro P hP
      have he : U.obj.filtration.step (-(n - P)) = ⊥ := hbot _ (by omega)
      have hz : IsZero (U.obj.filtration.step (-(n - P)) : CochainComplex C ℤ) := by
        rw [he]
        exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
      exact ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ)
        (P + (n - P))).map_isZero hz).of_iso (eD P (n - P))
  obtain ⟨L, hregular, hweak⟩ := X.finiteCocone_weakConvergence A htails
  let G : ∀ n : ℤ, DecreasingFiltration (U.obj.obj.homology n) := fun n ↦
    { step := fun p ↦ (X.imageFiltration n (A n)).step (p + n)
      antitone_step := fun p q hpq ↦
        (X.imageFiltration n (A n)).antitone_step (by omega) }
  have hG (n p : ℤ) : (G n).step p =
      imageSubobject (HomologicalComplex.homologyMap (U.obj.filtration.step p).arrow n) := by
    change imageSubobject ((A n).ι (p + n)) = _
    rw [hi, show p + n - n = p by omega]
  have hGfinite (n : ℤ) : (G n).IsFinite := by
    refine ⟨a, b, ?_, ?_⟩
    · rw [hG]
      exact homology_image_top _ ha n
    · rw [hG]
      exact homology_image_bot _ hb n
  refine ⟨G, L, A, fun n ↦ Iso.refl _, hG, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ⟨hGfinite n, (finite_separated_exhaustive (G n) (hGfinite n)).1⟩
  · intro n P
    simp [A, filteredCohomologyDiagonalMap]
  · refine ⟨hregular, ⟨hweak, ?_⟩, ?_⟩
    · intro n
      exact finite_separated_exhaustive _ (hfinite n)
    · intro n
      exact finite_inverseLimit _ (hfinite n)
  · intro p q
    obtain ⟨e, he, hu⟩ := X.weakConvergence_comparison L A hweak (2 * p + q) (-p)
    refine ⟨e ≪≫ eqToIso ?_⟩
    have hn : 2 * p + q + -p = p + q := by omega
    rw [hn]
    simp only [DecreasingFiltration.gradedPiece, G,
      BigradedExactCouple.imageFiltration]
    have hP : 2 * p + q = p + (p + q) := by omega
    have hPs : 2 * p + q + 1 = p + 1 + (p + q) := by omega
    congr! 6

end CategoryTheory
