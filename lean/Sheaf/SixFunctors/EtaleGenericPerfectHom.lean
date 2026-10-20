/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
public import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHom
import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided

/-!
Finite-projective internal-Hom exchange on an étale stratum.

Source: literature/stacks-project/cohomology.tex, Tags 08DM and 08DQ, and Tag 0GM7(1).
The proof is the chartwise strictly-perfect Hom calculation, the finite truncation interval
argument, and descent of the evaluation-induced comparison. This Q79 delivery revalidates
the landed statement without changing its signature. -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Evaluation with the internal Hom as the first tensor factor.
Source: Stacks Project, Tags 08DM and 08DQ
(blueprint: lem-sf-etale-generic-perfect-hom).
This is the canonical symmetry followed by the tensor–Hom counit. Naming the composite
keeps its specialization to module coefficients shared between the statement and proof. -/
noncomputable def derivedHomRightEvaluation
    (C : Type*) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (S : Scheme.{u}) (P N : _root_.DerivedCategory (Sheaf S.smallEtaleTopology C)) :
    ((derivedTensor C S).obj (((RHom(S)[C]).obj (op P)).obj N)).obj P ⟶ N :=
  ((derivedTensorSymmetry C S).hom.app (((RHom(S)[C]).obj (op P)).obj N)).app P ≫
    (derivedTensorHomAdjunction C P).counit.app N

attribute [-instance] CategoryTheory.catToReflQuiver in
private abbrev torAmplitudeEtale
    (C : Type*) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (S : Scheme.{u}) (a b : ℤ) :
    ObjectProperty (_root_.DerivedCategory (Sheaf S.smallEtaleTopology C)) :=
  _root_.DerivedCategory.torAmplitudeIn (Sheaf S.smallEtaleTopology C) a b

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma torAmplitudeEtale_of_model
    (C : Type*) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (S : Scheme.{u}) (E : CochainComplex (Sheaf S.smallEtaleTopology C) ℤ)
    (a b : ℤ) [E.IsStrictlyGE a] [E.IsStrictlyLE b]
    (hE : ∀ n, IsDualizableSheaf (E.X n))
    (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology C))
    (e : _root_.DerivedCategory.Q.obj E ≅ K) : torAmplitudeEtale C S a b K :=
  (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e
    (_root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat E a b (fun n ↦ (hE n).flat))

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma perfectHomInterval
    (C : Type*) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (S : Scheme.{u}) (P D N : _root_.DerivedCategory (Sheaf S.smallEtaleTopology C))
    [ExactPairing D P] [ExactPairing P D] (a b c d : ℤ)
    (hP : torAmplitudeEtale C S a b P)
    (hN : _root_.DerivedCategory.homologyConcentratedIn c d N) :
    _root_.DerivedCategory.homologyConcentratedIn (c - b) (d - a)
      (((RHom(S)[C]).obj (op P)).obj N) := by
  have hD := _root_.DerivedCategory.torAmplitudeIn_of_exactPairing (L := D) hP
  have ht := _root_.DerivedCategory.homologyConcentratedIn_tensor_of_torAmplitudeIn_left
    hD hN
  have e := derivedHomIsoDerivedTensorOfExactPairing C D P N
  have h := (_root_.DerivedCategory.homologyConcentratedIn (-b + c) (-a + d)).prop_of_iso
    e.symm ht
  simpa only [sub_eq_add_neg, add_comm] using h

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma perfectHomFacts
    (C : Type*) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] [UpperStarPreservesFlat C]
    {S T : Scheme.{u}} (g : T ⟶ S)
    (P N : _root_.DerivedCategory (Sheaf S.smallEtaleTopology C)) (a b c d : ℤ)
    (hd : DerivedCategory.IsDualizableEtale P)
    (hP : torAmplitudeEtale C S a b P)
    (hN : _root_.DerivedCategory.homologyConcentratedIn c d N) :
    _root_.DerivedCategory.homologyConcentratedIn (c - b) (d - a)
      (((RHom(S)[C]).obj (op P)).obj N) ∧
      IsIso (derivedHomUpperStarComparison C g P N) := by
  obtain ⟨_⟩ := hd
  obtain ⟨_⟩ := DerivedCategory.nonempty_exactPairing_swap P Pᘁ
  exact ⟨perfectHomInterval C S P Pᘁ N a b c d hP hN,
    isIso_derivedHomUpperStarComparison_of_exactPairing C g Pᘁ P N⟩

section Helpers

open MonoidalCategory Functor.LaxMonoidal in
attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma braided_evaluation
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    (F : C ⥤ D) [F.Monoidal]
    (hbr : ∀ X Y : C, μ F X Y ≫ F.map (β_ X Y).hom =
      (β_ (F.obj X) (F.obj Y)).hom ≫ μ F Y X)
    (P V N : C) (W : D) (ρ : F.obj V ⟶ W)
    (ev : P ⊗ V ⟶ N) (ev' : F.obj P ⊗ W ⟶ F.obj N)
    (e : F.obj (V ⊗ P) ≅ F.obj V ⊗ F.obj P)
    (he : e.hom = Functor.OplaxMonoidal.δ F V P)
    (hev : F.obj P ◁ ρ ≫ ev' = μ F P V ≫ F.map ev) :
    e.inv ≫ F.map ((β_ V P).hom ≫ ev) =
      ρ ▷ F.obj P ≫ (β_ W (F.obj P)).hom ≫ ev' := by
  have hi : e.inv = μ F V P := by
    apply (cancel_epi e.hom).mp
    rw [Iso.hom_inv_id, he, Functor.Monoidal.δ_μ]
  rw [hi, Functor.map_comp, ← Category.assoc, hbr, Category.assoc, ← hev]
  exact (BraidedCategory.braiding_naturality_left_assoc ρ (F.obj P) ev').symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma symmetry_generic
    (C : Type*) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [HasDerivedCategory.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (K M : _root_.DerivedCategory C) :
    ((_root_.DerivedCategory.canonicalTensorSymmetry C).hom.app K).app M =
      (@BraidedCategory.braiding _ _ _ (_root_.DerivedCategory.braidedCategory' C) K M).hom := by
  rfl

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
attribute [local instance] derivedBraidedCategory

attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma perfectHomComparison_eval
    (C : Type*) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] [UpperStarPreservesFlat C]
    {S T : Scheme.{u}} (g : T ⟶ S)
    (P N : _root_.DerivedCategory (Sheaf S.smallEtaleTopology C)) :
    (leftDerivedUpperStarTensorIso C g (((RHom(S)[C]).obj (op P)).obj N) P).inv ≫
        (Functor.leftDerivedFunctor ((g)^*[C])).map (derivedHomRightEvaluation C S P N) =
      ((derivedTensor C T).map (derivedHomUpperStarComparison C g P N)).app
          ((Functor.leftDerivedFunctor ((g)^*[C])).obj P) ≫
        derivedHomRightEvaluation C T
          ((Functor.leftDerivedFunctor ((g)^*[C])).obj P)
          ((Functor.leftDerivedFunctor ((g)^*[C])).obj N) := by
  simp only [derivedHomRightEvaluation, derivedTensorSymmetry, symmetry_generic]
  let := leftDerivedUpperStarMonoidal C g
  let := derivedBraidedCategory C S
  let := derivedBraidedCategory C T
  exact braided_evaluation _ (leftDerivedUpperStar_μ_map_braiding_hom C g)
    P _ N _ (derivedHomUpperStarComparison C g P N)
    ((derivedTensorHomAdjunction C P).counit.app N)
    ((derivedTensorHomAdjunction C
      ((Functor.leftDerivedFunctor ((g)^*[C])).obj P)).counit.app
      ((Functor.leftDerivedFunctor ((g)^*[C])).obj N))
    (leftDerivedUpperStarTensorIso C g _ P)
    ((leftDerivedUpperStarTensorIso_hom C g _ P).trans
      (leftDerivedUpperStar_δ_eq C g _ P).symm)
    (derivedHomUpperStarComparison_ev C g P N)



end Helpers

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem isZero_of_etale_cover
    (A : Type (u + 1)) [CommRing A] {S : Scheme.{u}}
    (U : Scheme.Cover.{u} Scheme.etalePrecoverage S)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
    (h : ∀ i, IsZero ((upperStar (ModuleCat.{u + 1} A) (U.f i)).obj F)) :
    IsZero F := by
  have : IsIso (0 : F ⟶ F) :=
    isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} A)
      U.f U.exists_eq _ (fun i ↦ (h i).isIso (h i) _)
  exact (isIsoZero_iff_source_target_isZero F F).1 this |>.1

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem concentrated_of_etale_cover
    (A : Type (u + 1)) [CommRing A] {S : Scheme.{u}}
    (U : Scheme.Cover.{u} Scheme.etalePrecoverage S)
    (K : DerivedCategoryModule A S) (a b : ℤ)
    (h : ∀ i, _root_.DerivedCategory.homologyConcentratedIn a b
      ((Functor.leftDerivedFunctor ((U.f i)^*[ModuleCat.{u + 1} A])).obj K)) :
    _root_.DerivedCategory.homologyConcentratedIn a b K := by
  have hz (n : ℤ) (hn : n < a ∨ b < n) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj K) := by
    apply isZero_of_etale_cover A U
    intro i
    have hi : IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
        ((Functor.leftDerivedFunctor ((U.f i)^*[ModuleCat.{u + 1} A])).obj K)) := by
      rcases hn with hn | hn
      · exact (_root_.DerivedCategory.isGE_iff _ a).1 (h i).1 n hn
      · exact (_root_.DerivedCategory.isLE_iff _ b).1 (h i).2 n hn
    exact hi.of_iso ((leftDerivedUpperStarHomologyFunctorIso
      (ModuleCat.{u + 1} A) (U.f i) n).app K)
  exact ⟨(_root_.DerivedCategory.isGE_iff _ a).2 (fun n hn ↦ hz n (Or.inl hn)),
    (_root_.DerivedCategory.isLE_iff _ b).2 (fun n hn ↦ hz n (Or.inr hn))⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem torAmplitude_of_etale_cover
    (A : Type (u + 1)) [CommRing A] {S : Scheme.{u}}
    (U : Scheme.Cover.{u} Scheme.etalePrecoverage S)
    (K : DerivedCategoryModule A S) (a b : ℤ)
    (h : ∀ i, torAmplitudeEtale (ModuleCat.{u + 1} A) (U.X i) a b
      ((Functor.leftDerivedFunctor ((U.f i)^*[ModuleCat.{u + 1} A])).obj K)) :
    torAmplitudeEtale (ModuleCat.{u + 1} A) S a b K := by
  intro F
  apply concentrated_of_etale_cover A U
  intro i
  let e := leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) (U.f i) K
    ((_root_.DerivedCategory.singleFunctor _ 0).obj F) ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) (U.X i)).obj
      ((Functor.leftDerivedFunctor ((U.f i)^*[ModuleCat.{u + 1} A])).obj K)).mapIso
      ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) (U.f i)).app F)
  exact (_root_.DerivedCategory.homologyConcentratedIn a b).prop_of_iso e.symm
    (h i ((upperStar (ModuleCat.{u + 1} A) (U.f i)).obj F))


attribute [-instance] CategoryTheory.catToReflQuiver in
private lemma perfectHomConclusion
    (C : Type*) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] [UpperStarPreservesFlat C]
    {S S' : Scheme.{u}} (g : S' ⟶ S) (a b c d : ℤ)
    (P N : _root_.DerivedCategory (Sheaf S.smallEtaleTopology C))
    (hdual : DerivedCategory.IsDualizableEtale P)
    (htor : torAmplitudeEtale C S a b P)
    (hNc : _root_.DerivedCategory.homologyConcentratedIn c d N) :
    let H : _root_.DerivedCategory (Sheaf S.smallEtaleTopology C) :=
      ((RHom(S)[C]).obj (op P)).obj N
    let P' : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology C) :=
      (Functor.leftDerivedFunctor ((g)^*[C])).obj P
    let N' : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology C) :=
      (Functor.leftDerivedFunctor ((g)^*[C])).obj N
    let H' : _root_.DerivedCategory (Sheaf S'.smallEtaleTopology C) :=
      ((RHom(S')[C]).obj (op P')).obj N'
    let ev := derivedHomRightEvaluation C S P N
    let ev' := derivedHomRightEvaluation C S' P' N'
    ((∀ n : ℤ, n < c - b ∨ d - a < n →
        IsZero ((DerivedCategory.homologyFunctor
          (Sheaf S.smallEtaleTopology C) n).obj H)) ∧
      (∀ n : ℤ, n < c - b ∨ d - a < n →
        IsZero ((DerivedCategory.homologyFunctor
          (Sheaf S'.smallEtaleTopology C) n).obj H')) ∧
      ∃ β : (Functor.leftDerivedFunctor ((g)^*[C])).obj
          (((RHom(S)[C]).obj (op P)).obj N) ≅
          ((RHom(S')[C]).obj (op P')).obj N',
        ((leftDerivedUpperStarTensorIso C g
            (((RHom(S)[C]).obj (op P)).obj N) P).inv ≫
            (Functor.leftDerivedFunctor ((g)^*[C])).map ev) =
          ((derivedTensor C S').map β.hom).app
            ((Functor.leftDerivedFunctor ((g)^*[C])).obj P) ≫ ev') := by
  classical
  obtain ⟨hHc, hi⟩ := perfectHomFacts C g P N a b c d hdual htor hNc
  let β := asIso (derivedHomUpperStarComparison C g P N)
  have hHz (n : ℤ) (hn : n < c - b ∨ d - a < n) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
        (((RHom(S)[C]).obj (op P)).obj N)) := by
    rcases hn with hn | hn
    · exact (_root_.DerivedCategory.isGE_iff _ _).1 hHc.1 n hn
    · exact (_root_.DerivedCategory.isLE_iff _ _).1 hHc.2 n hn
  refine ⟨hHz, ?_, β, ?_⟩
  · intro n hn
    exact ((upperStar C g).map_isZero (hHz n hn)).of_iso
      (((_root_.DerivedCategory.homologyFunctor _ n).mapIso β).symm ≪≫
        ((leftDerivedUpperStarHomologyFunctorIso C g n).app _).symm)
  · exact perfectHomComparison_eval C g P N

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- On a finite-coefficient étale site, pullback of internal Hom from a locally bounded
finite-projective constant model is an isomorphism, with the indicated cohomological bound.
Source: literature/stacks-project/cohomology.tex, Tags 08DM and 08DQ and Tag 0GM7(1)
(blueprint: lem-sf-etale-generic-perfect-hom).

Proof (deferred): refine the given étale cover and represent `P` on each chart by the
bounded complex `E` in the hypothesis.  The chart pullbacks represent `P'` by exactness of
constant-coefficient inverse image, and the derived tensor pullback comparison is the
canonical comparison from `leftDerivedUpperStarTensorIso`.  The bounded-free Hom model
and the termwise finite-projective pullback-Hom identity identify the chart map with the
map induced by the displayed evaluation formula.  The finite truncation filtration of
`N`, together with the dual interval `[-b,-a]`, gives the two cohomological intervals
`[c-b,d-a]`; exact inverse image gives the same interval after pullback.  These local
isomorphisms agree on refinements by naturality of evaluation and transpose, so the
cover-local isomorphism criterion gives the global `β` and its displayed equation. -/
theorem etaleGenericPerfectHom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S S' : Scheme.{u}} (g : S' ⟶ S)
    (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d)
    (P N : DerivedCategoryModule A S)
    (hP : ∃ U : Scheme.Cover.{u} Scheme.etalePrecoverage S,
      ∀ i : U.I₀,
        ∃ E : CochainComplex
            (Sheaf (U.X i).smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
          Nonempty
            (DerivedCategory.Q.obj E ≅
              (Etale.upperStar (ModuleCat.{u + 1} A) (U.f i)).mapDerivedCategory.obj P) ∧
          (∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) ∧
          (∀ n : ℤ, ∃ r : ℕ,
            ∃ ι : E.X n ⟶
                (constantSheaf (U.X i).smallEtaleTopology
                  (ModuleCat.{u + 1} A)).obj
                  (ModuleCat.of A (Fin r → A)),
            ∃ π :
                (constantSheaf (U.X i).smallEtaleTopology
                  (ModuleCat.{u + 1} A)).obj
                  (ModuleCat.of A (Fin r → A)) ⟶ E.X n,
              ι ≫ π = 𝟙 (E.X n)))
    (hN : ∀ n : ℤ, n < c ∨ d < n →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) n).obj N)) :
    let H : DerivedCategoryModule A S :=
      ((RHom(S)[ModuleCat.{u + 1} A]).obj (op P)).obj N
    let P' : DerivedCategoryModule A S' :=
      (Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).obj P
    let N' : DerivedCategoryModule A S' :=
      (Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).obj N
    let H' : DerivedCategoryModule A S' :=
      ((RHom(S')[ModuleCat.{u + 1} A]).obj (op P')).obj N'
    let ev := derivedHomRightEvaluation (ModuleCat.{u + 1} A) S P N
    let ev' := derivedHomRightEvaluation (ModuleCat.{u + 1} A) S' P' N'
    ((∀ n : ℤ, n < c - b ∨ d - a < n →
        IsZero ((DerivedCategory.homologyFunctor
          (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) n).obj H)) ∧
      (∀ n : ℤ, n < c - b ∨ d - a < n →
        IsZero ((DerivedCategory.homologyFunctor
          (Sheaf S'.smallEtaleTopology (ModuleCat.{u + 1} A)) n).obj H')) ∧
      ∃ β : (Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).obj
          (((RHom(S)[ModuleCat.{u + 1} A]).obj (op P)).obj N) ≅
          ((RHom(S')[ModuleCat.{u + 1} A]).obj (op P')).obj N',
        ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g
            (((RHom(S)[ModuleCat.{u + 1} A]).obj (op P)).obj N) P).inv ≫
            (Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).map ev) =
          ((derivedTensor (ModuleCat.{u + 1} A) S').map β.hom).app
            ((Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).obj P) ≫ ev') := by
  classical
  have hsite : DerivedCategory.IsSitePerfect P := by
    obtain ⟨U, hU⟩ := hP
    refine ⟨U, fun i ↦ ?_⟩
    obtain ⟨E, ⟨e⟩, hz, hr⟩ := hU i
    have ha : E.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff E a).2
      (fun n hn ↦ hz n (Or.inl hn))
    have hb : E.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff E b).2
      (fun n hn ↦ hz n (Or.inr hn))
    refine ⟨E, a, b, ha, hb, ?_, ?_⟩
    · intro n
      obtain ⟨r, ι, π, hιπ⟩ := hr n
      exact ⟨r, ⟨⟨ι, π, hιπ⟩⟩⟩
    · exact ⟨((leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) (U.f i)).app P) ≪≫ e.symm⟩
  have hdual := hsite.isDualizable
  have htor : torAmplitudeEtale (ModuleCat.{u + 1} A) S a b P := by
    obtain ⟨U, hU⟩ := hP
    apply torAmplitude_of_etale_cover A U
    intro i
    obtain ⟨E, ⟨e⟩, hz, hr⟩ := hU i
    have : E.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff E a).2
      (fun n hn ↦ hz n (Or.inl hn))
    have : E.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff E b).2
      (fun n hn ↦ hz n (Or.inr hn))
    have hf (n : ℤ) : IsDualizableSheaf (E.X n) := by
      obtain ⟨r, ι, π, hιπ⟩ := hr n
      exact IsDualizableSheaf.of_retract ⟨ι, π, hιπ⟩
        (isDualizableSheaf_constantSheaf_pi r)
    exact torAmplitudeEtale_of_model (ModuleCat.{u + 1} A) (U.X i) E a b hf _
      (e ≪≫ ((leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) (U.f i)).app P).symm)
  have hNc : _root_.DerivedCategory.homologyConcentratedIn c d N :=
    ⟨(_root_.DerivedCategory.isGE_iff _ c).2 (fun n hn ↦ hN n (Or.inl hn)),
      (_root_.DerivedCategory.isLE_iff _ d).2 (fun n hn ↦ hN n (Or.inr hn))⟩
  exact (And.intro hab hcd).elim (fun _ _ ↦
    perfectHomConclusion (ModuleCat.{u + 1} A) g a b c d P N hdual htor hNc)

end AlgebraicGeometry.Etale
