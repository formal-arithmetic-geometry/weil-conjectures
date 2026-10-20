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

-- Adapted from the private finite_inverse_limit proof in HalfPlaneConvergence.
private theorem finite_inverse_limit {C : Type u} [Category.{v} C] [Abelian C]
    {T : C} (F : PBCDecreasingFiltration T)
    (m : ℤ) (hm : F.step m = ⊥) : BigradedExactCouple.IsInverseLimit F := by
  have hz (p : ℤ) (hp : m ≤ p) : F.step p = ⊥ :=
    le_antisymm (hm ▸ F.antitone_step hp) bot_le
  have hπ (p : ℤ) (hp : m ≤ p) : IsIso (cokernel.π (F.step p).arrow) := by
    apply CokernelCofork.IsColimit.isIso_π
      (CokernelCofork.ofπ _ (cokernel.condition _)) (cokernelIsCokernel _)
    apply Subobject.mk_eq_bot_iff_zero.mp
    simpa only [Subobject.mk_arrow] using hz p hp
  have hcomm (p : ℤ) :
      cokernel.π (F.step (p + 1)).arrow ≫ BigradedExactCouple.quotientTransition F p =
        cokernel.π (F.step p).arrow := by
    exact cokernel.π_desc _ _ _
  intro S f hf
  have := hπ m le_rfl
  let h : S ⟶ T := f m ≫ inv (cokernel.π (F.step m).arrow)
  have hbase : h ≫ cokernel.π (F.step m).arrow = f m := by simp [h]
  refine ⟨h, ?_, ?_⟩
  · intro p
    induction p using Int.inductionOn' with
    | b => exact m
    | zero => exact hbase
    | succ p hp ih =>
      have := hπ p hp
      have := hπ (p + 1) (by omega)
      have : IsIso (BigradedExactCouple.quotientTransition F p) := by
        have heq : BigradedExactCouple.quotientTransition F p =
            inv (cokernel.π (F.step (p + 1)).arrow) ≫ cokernel.π (F.step p).arrow := by
          apply (cancel_epi (cokernel.π (F.step (p + 1)).arrow)).1
          simp [hcomm]
        rw [heq]
        infer_instance
      apply (cancel_mono (BigradedExactCouple.quotientTransition F p)).1
      rw [Category.assoc, hcomm, hf, ih]
    | pred p hp ih =>
      have ih' : h ≫ cokernel.π (F.step (p - 1 + 1)).arrow = f (p - 1 + 1) := by
        exact Eq.mp (congrArg (fun j : ℤ ↦ h ≫ cokernel.π (F.step j).arrow = f j)
          (show p = p - 1 + 1 by omega)) ih
      calc
        h ≫ cokernel.π (F.step (p - 1)).arrow =
            h ≫ (cokernel.π (F.step (p - 1 + 1)).arrow ≫
              BigradedExactCouple.quotientTransition F (p - 1)) := by rw [hcomm]
        _ = f (p - 1 + 1) ≫ BigradedExactCouple.quotientTransition F (p - 1) := by
          rw [← Category.assoc, ih']
        _ = f (p - 1) := hf (p - 1)
  · intro h' hh'
    apply (cancel_mono (cokernel.π (F.step m).arrow)).1
    exact (hh' m).trans hbase.symm

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
  -- The finite-cocone criterion only needs the alpha comparison.
  have _hγ := hγ
  obtain ⟨hc, hu⟩ := filteredCohomologyDiagonal_isColimit U.obj U.property X eD hα
  let A : ∀ n : ℤ, X.AlphaColimit n := fun n ↦
    { obj := U.obj.obj.homology n
      ι := filteredCohomologyDiagonalMap U.obj X eD n
      comm := hc n
      isColimit := hu n }
  have himage (n P : ℤ) : (X.imageFiltration n (A n)).step P =
      imageSubobject (HomologicalComplex.homologyMap
        (U.obj.filtration.step (P - n)).arrow n) := by
    dsimp [BigradedExactCouple.imageFiltration, A, filteredCohomologyDiagonalMap]
    rw [imageSubobject_comp_eq_of_epi, imageSubobject_comp_eq_of_epi]
  let G : ∀ n : ℤ, DecreasingFiltration (U.obj.obj.homology n) := fun n ↦
    { F := fun p ↦ (X.imageFiltration n (A n)).step (p + n)
      F_succ_le := fun p ↦ (X.imageFiltration n (A n)).antitone_step (by omega) }
  have hG (n p : ℤ) : (G n).step p =
      imageSubobject (HomologicalComplex.homologyMap
        (U.obj.filtration.step p).arrow n) := by
    dsimp [G]
    rw [himage, add_sub_cancel_right]
  obtain ⟨a, b, ha, hb⟩ := U.property
  have hGfinite (n : ℤ) : (G n).IsFinite := by
    refine ⟨a, b, ?_, ?_⟩
    · change (G n).step a = ⊤
      rw [hG]
      exact homology_image_top _ ha n
    · change (G n).step b = ⊥
      rw [hG]
      exact homology_image_bot _ hb n
  have hfinite (n : ℤ) : (X.imageFiltration n (A n)).IsFinite := by
    refine ⟨a + n, b + n, ?_, ?_⟩
    · rw [himage, add_sub_cancel_right]
      exact homology_image_top _ ha n
    · rw [himage, add_sub_cancel_right]
      exact homology_image_bot _ hb n
  have hA : ∀ n : ℤ, ∃ a b : ℤ,
      (∀ P : ℤ, P ≤ a → IsIso ((A n).ι P)) ∧
      (∀ P : ℤ, b ≤ P → IsZero (X.D P (n - P))) := by
    intro n
    refine ⟨a + n, b + n, ?_, ?_⟩
    · intro P hP
      have ht : U.obj.filtration.step (P - n) = ⊤ :=
        top_le_iff.mp (ha ▸ U.obj.filtration.antitone_step (by omega))
      let : IsIso (U.obj.filtration.step (P - n)).arrow :=
        (Subobject.isIso_arrow_iff_eq_top _).mpr ht
      let : IsIso (HomologicalComplex.homologyMap
          (U.obj.filtration.step (P - n)).arrow n) :=
        (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).map_isIso _
      dsimp [A, filteredCohomologyDiagonalMap]
      infer_instance
    · intro P hP
      have ht : U.obj.filtration.step (-(n - P)) = ⊥ :=
        le_bot_iff.mp (hb ▸ U.obj.filtration.antitone_step (by omega))
      have hz : (U.obj.filtration.step (-(n - P))).arrow = 0 := by
        rw [ht, Subobject.bot_arrow]
      exact IsZero.of_iso
        ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ)
          (P + (n - P))).map_isZero (IsZero.of_mono_eq_zero _ hz)) (eD P (n - P))
  obtain ⟨L, hreg, hweak⟩ := X.finiteCocone_weakConvergence A hA
  refine ⟨G, L, A, fun n ↦ Iso.refl _, hG, ?_, ?_, ?_, ?_⟩
  · exact fun n ↦ ⟨hGfinite n, (finite_separated_exhaustive (G n) (hGfinite n)).1⟩
  · intro n P
    exact Category.comp_id _
  · refine ⟨hreg, ⟨hweak, ?_⟩, ?_⟩
    · intro n
      obtain ⟨c, d, hc, hd⟩ := hfinite n
      constructor
      · intro V hV
        exact le_bot_iff.mp (hd ▸ hV d)
      · intro V hV
        exact top_le_iff.mp (hc ▸ hV c)
    · intro n
      obtain ⟨c, d, hc, hd⟩ := hfinite n
      exact finite_inverse_limit _ d hd
  · intro p q
    obtain ⟨e, _, _⟩ := X.weakConvergence_comparison L A hweak (2 * p + q) (-p)
    refine ⟨e ≪≫ eqToIso ?_⟩
    dsimp only [PBCDecreasingFiltration.gradedPiece, DecreasingFiltration.gradedPiece,
      DecreasingFiltration.gr, G]
    have hn : 2 * p + q + -p = p + q := by omega
    rw [hn]
    congr 3 <;> first | omega | exact proof_irrel_heq _ _

end CategoryTheory
