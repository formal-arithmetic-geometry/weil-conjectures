/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProjectionRefinementDescent.ProjectionRefinementData

/-! # ProjectionRefinementComparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.ProjectionRefinementDescent

private theorem conjugated_component
    {A : Type*} [Category A] {B : Type*} [Category B] {C : Type*} [Category C]
    (F : A ⥤ B) [F.Full] (G H : B ⥤ C) (a : F ⋙ G ≅ F ⋙ H)
    {X Y : A} {Z : B} (e : F.obj X ≅ Z) (e' : F.obj Y ≅ Z) :
    G.mapIso e.symm ≪≫ a.app X ≪≫ H.mapIso e =
      G.mapIso e'.symm ≪≫ a.app Y ≪≫ H.mapIso e' := by
  apply Iso.ext
  apply (cancel_epi (G.map e.hom)).mp
  have h := a.hom.naturality (F.preimage (e.hom ≫ e'.inv))
  simp only [Functor.comp_map, Functor.map_preimage] at h
  simpa [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, Functor.map_comp] using
    congrArg (fun z ↦ z ≫ H.map e'.hom) h.symm

/-- The natural common-refinement comparison on the bounded constructible category.
Source: lem-sf-projection-refinement-descent, step 8, and
prop-compactification-coherence-detailed, steps 5--9; Stacks 0F7G.
(blueprint: lem-sf-projection-refinement-comparisons).

Proof: apply compactification_coherence over D.k at coefficient level n+1. Its
comparisons are natural on the category retaining an etale-origin witness, and are
normalized by the two legs of every common refinement. The fixed-object forgetful
functor from that category is fully faithful: it is the induced-category forgetful
functor followed by the full bounded-below inclusion and the inverse coefficient
realization equivalence. For each bounded constructible K use origins to choose a
presentation e from this functor. For a morphism K to K', full faithfulness lifts
e followed by that morphism followed by e' inverse. Conjugate the coherent comparison
by image(c).mapIso e.symm and image(d).mapIso e. Naturality of the witnessed
comparison proves naturality of the resulting family. Any second presentation is
related by the unique lift of its change-of-presentation isomorphism; naturality
therefore makes the resulting comparison independent of the chosen presentation.
This proves normalization for every O and e, rather than just the chosen ones.
Conjugating the witnessed cocycle cancels the intermediate presentation and proves
the displayed natural-isomorphism cocycle. No tensor or projection map is involved;
this statement also applies if the input full subcategory is empty. -/
theorem comparison_cocycle
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra ℚ_[C.l] E] [FiniteDimensional ℚ_[C.l] E]
    (n : ℕ) {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (origins : ∀ K : (boundedConstructible C.l E n X).FullSubcategory,
      ∃ O : RefinementFiniteLevelOrigin C.l E (n + 1) (Nat.succ_pos n) X,
        Nonempty (refinementFiniteLevelFixedObject C.l E (n + 1) (Nat.succ_pos n) X O ≅
          K.obj)) :
    ∃ rho : ∀ c d : Compactification f,
        (boundedConstructible C.l E n X).ι ⋙ image C.l E n c ≅
          (boundedConstructible C.l E n X).ι ⋙ image C.l E n d,
      (∀ (c d b : Compactification f) (r : b.Refinement c) (s : b.Refinement d)
        (K : (boundedConstructible C.l E n X).FullSubcategory)
        (O : RefinementFiniteLevelOrigin C.l E (n + 1) (Nat.succ_pos n) X)
        (e : refinementFiniteLevelFixedObject C.l E (n + 1) (Nat.succ_pos n) X O ≅ K.obj),
        (rho c d).app K = (theta C.l E n r K.obj O e).symm ≪≫
          theta C.l E n s K.obj O e) ∧
      (∀ c d b : Compactification f, rho c d ≪≫ rho d b = rho c b) := by
  classical
  let : Finite (Padic.coefficientExtensionRing C.l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing C.l E (n + 1) (Nat.succ_pos n)
  let : TopologicalSpace (Coefficient C.l E n) := ⊥
  let : DiscreteTopology (Coefficient C.l E n) := discreteTopology_bot _
  let := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
      (D.card_base.trans D.cardinality_eq))
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have hl : IsUnit (C.l : D.k) :=
    (CharP.isUnit_natCast_iff (R := D.k) D.prime).2 fun h ↦
      C.different ((Nat.prime_dvd_prime_iff_eq D.prime
        (Fact.out : C.l.Prime)).1 h).symm
  obtain ⟨q, hq, _, _, _, comparison, hcomparison, hcomp⟩ :=
    compactification_coherence D.k C.l hl E (n + 1) (Nat.succ_pos n) f
  let F := etaleOriginForgetful X (Coefficient C.l E n) ⋙
    (refinementCoefficientEquivalence X (Coefficient C.l E n)).inverse
  have : (etaleOriginForgetfulPlus X (Coefficient C.l E n)).Full :=
    (etaleOriginForgetfulPlusFullyFaithful X (Coefficient C.l E n)).full
  have : (etaleOriginForgetfulPlus X (Coefficient C.l E n)).Faithful :=
    (etaleOriginForgetfulPlusFullyFaithful X (Coefficient C.l E n)).faithful
  have : F.Full := by
    dsimp [F, etaleOriginForgetful]
    infer_instance
  have : F.Faithful := by
    dsimp [F, etaleOriginForgetful]
    infer_instance
  let U := (boundedConstructible C.l E n X).ι
  have hU : ∀ K, F.essImage (U.obj K) := origins
  let V := Functor.essImage.liftFunctor U F hU
  let v : V ⋙ F ≅ U := Functor.essImage.liftFunctorCompIso U F hU
  let a (c d : Compactification f) : F ⋙ image C.l E n c ≅ F ⋙ image C.l E n d :=
    comparison c d
  let rho (c d : Compactification f) : U ⋙ image C.l E n c ≅ U ⋙ image C.l E n d :=
    Functor.isoWhiskerRight v.symm (image C.l E n c) ≪≫
      Functor.associator V F (image C.l E n c) ≪≫
      Functor.isoWhiskerLeft V (a c d) ≪≫
      (Functor.associator V F (image C.l E n d)).symm ≪≫
      Functor.isoWhiskerRight v (image C.l E n d)
  have happ (c d : Compactification f) (K : (boundedConstructible C.l E n X).FullSubcategory) :
      (rho c d).app K = (image C.l E n c).mapIso (v.app K).symm ≪≫
        (a c d).app (V.obj K) ≪≫ (image C.l E n d).mapIso (v.app K) := by
    apply Iso.ext
    simp [rho]
  refine ⟨rho, ?_, ?_⟩
  · intro c d b r s K O e
    rw [happ]
    rw [conjugated_component F (image C.l E n c) (image C.l E n d)
      (a c d) (v.app K) e]
    have ha : (a c d).app O = ((q b c r).app O).symm ≪≫ (q b d s).app O := by
      exact congrArg (fun z ↦ z.app O) (hcomparison c d b r s)
    rw [ha, hq b c r O, hq b d s O]
    apply Iso.ext
    simp [theta, refinementComparisonIsomorphism]
  · intro c d b
    apply Iso.ext
    ext K
    have h : (a c d).app (V.obj K) ≪≫ (a d b).app (V.obj K) =
        (a c b).app (V.obj K) := congrArg (fun z ↦ z.app (V.obj K)) (hcomp c d b)
    have hh : (rho c d).app K ≪≫ (rho d b).app K = (rho c b).app K := by
      rw [happ, happ, happ]
      simp only [Functor.mapIso_symm, Iso.trans_assoc, Iso.self_symm_id_assoc]
      rw [← Iso.trans_assoc ((a c d).app (V.obj K)) ((a d b).app (V.obj K)), h]
    exact congrArg Iso.hom hh

end WeilConjectures.ProjectionRefinementDescent
