/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.CumulativeUniversalBaseChangeProperty
public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum
import Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection
import Sheaf.AlgebraicGeometry.FieldFailureOfCumulativeBaseChange

/-!
# A universal base-change failure over a geometric generic point

Source: Stacks Project, Tag 0F08, Lemma 59.88.7; blueprint sec-smooth-base-change,
sk-lem-universal-datum (blueprint: sbc-lem-bc-universal-test).

The conclusion uses abelian sheaves with constant value the additive group of `ZMod d`.
Its higher direct image is written as the homology of the bounded-below derived direct
image on a sheaf in degree zero. This avoids replacing the cyclic group by `Λ/dΛ` for
an arbitrary coefficient ring. The `ULift` only implements the small-site size convention.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- A failure of universal base change in the first possible positive degree has a
geometric generic-point witness with nonzero cyclic abelian higher direct image.
Source: Stacks Project, Tag 0F08, Lemma 59.88.7; blueprint sec-smooth-base-change,
sk-lem-universal-datum (blueprint: sbc-lem-bc-universal-test).

Proof:
1. By `sbc-lem-bc-failure-field`, choose an affine base change, a field point and an
   `n`-annihilated sheaf witnessing failure. The horizontal map is qcqs because both
   its source and target are affine (`lem-weil-pbc-affine-scheme-qcqs` and
   `lem-weil-pbc-qcqs-morphism-permanence`).
2. Pass to an algebraic closure of the field. Its spectrum map is integral and surjective;
   `sbc-lem-bc-integral-surjective` and the universal degree-`q-1` hypothesis preserve failure.
3. Apply `lem-sbc-normalization-algclosed-field` to obtain the affine integral normal base
   with algebraically closed function field and the displayed field embedding. Pull back
   the total space. By `lem-sbc-integral-pushforward-base-change-arrow`, an isomorphism
   after normalization would imply the old isomorphism; thus failure persists.
4. Universality gives the lower-degree property on this base change. By
   `sbc-lem-bc-injectivity` the failing arrow is mono, so its target is nonzero. Its
   horizontal projection is qcqs by base-change permanence.
5. Regard the sheaf as a `ZMod n`-module. Apply
   `lem-sbc-coefficient-higher-direct-image-zero` and `lem-sbc-prime-cyclic-detection`:
   there is a prime `r` dividing `n` with nonzero higher direct image of the constant
   module `P_r/(r)`, where `P_r = ULift (ZMod r)`.
6. Multiplication by `r` in `P_r` vanishes, so this quotient has underlying additive
   group `ZMod r`. Restriction of scalars and the canonical equivalence of integer
   modules with abelian groups identify its higher direct image with the one below;
   constant sheafification preserves the coefficient isomorphism. Take `d = r`.
Normality is written as integral closedness of every stalk; integrality already makes
these stalks domains. The morphism induced by `i` is dominant since its image is the
generic point, and every map from a field to a field is injective. -/
theorem exists_universalBaseChangeFailure_cyclic_datum
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(S, ⊤))) (q : ℕ) (hq : 1 ≤ q)
    (hprev : CumulativeUniversalBaseChangeProperty f n hn hinv (q - 1))
    (hfail : ¬ UniversalBaseChangeProperty (ULift.{u + 1} (ZMod n)) f (q : ℤ)) :
    ∃ (S' X' : Scheme.{u}) (a : S' ⟶ S) (b : X' ⟶ X) (f' : X' ⟶ S')
      (_ : ChosenCartesianSquare b f' f a) (_ : IsAffine S') (_ : IsIntegral S')
      (_ : ∀ x : S', IsIntegrallyClosed (S'.presheaf.stalk x))
      (_ : IsAlgClosed S'.functionField) (K : Type u) (_ : Field K) (_ : IsAlgClosed K)
      (i : S'.functionField ⟶ CommRingCat.of K) (Y : Scheme.{u})
      (e : Y ⟶ Spec (.of K)) (h : Y ⟶ X')
      (_ : ChosenCartesianSquare h e f'
        (Spec.map i ≫ S'.fromSpecStalk (genericPoint S'))) (d : ℕ),
      d ∣ n ∧ ¬ IsZero
        ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
                (AddCommGrpCat.of (ULift.{u + 1} (ZMod d))))))) := by
  classical
  let Λ := ULift.{u + 1} (ZMod n)
  have hqZ : (1 : ℤ) ≤ (q : ℤ) := by omega
  have hdegree : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
  obtain ⟨F, _⟩ :=
    exists_fieldFailure_of_cumulativeUniversalBaseChangeProperty f n hn hinv q hq hprev hfail
  have := F.isAffine
  let := F.field
  let K := AlgebraicClosure F.K
  let πK : Spec (.of K) ⟶ Spec (.of F.K) :=
    Spec.map (CommRingCat.ofHom (algebraMap F.K K))
  have : IsIntegralHom πK :=
    IsIntegralHom.SpecMap_iff.2 fun x ↦ Algebra.IsIntegral.isIntegral (R := F.K) x
  have hπK : Function.Surjective πK.base := fun x ↦
    ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩
  obtain ⟨S'', _, _, hnorm, _, π, _, i, hi⟩ :=
    exists_normalization_of_isAlgClosed (πK ≫ F.g)
  let g'' := Spec.map i ≫ S''.fromSpecStalk (genericPoint S'')
  have hπ : IsPullback (pullback.fst F.p' π) (pullback.snd F.p' π) F.p' π :=
    IsPullback.of_hasPullback _ _
  have sq'' : IsPullback (pullback.fst g'' (pullback.snd F.p' π))
      (pullback.snd g'' (pullback.snd F.p' π)) g'' (pullback.snd F.p' π) :=
    IsPullback.of_hasPullback _ _
  have sq := (sq''.flip.paste_horiz hπ).flip
  have hpb := hπ.paste_horiz F.isPullback
  have hprev' : BaseChangeProperty Λ F.p' ((q : ℤ) - 1) := by
    rw [← hdegree]
    exact hprev (q - 1) le_rfl F.a F.b F.p' F.isPullback
  have h₁ : ¬ IsIso (baseChangeHomologyMap Λ sq (q : ℤ)
      ((πK)^*[ModuleCat.{u + 1} Λ].obj F.F)) := by
    rw [isIso_baseChangeHomologyMap_congr Λ F.p' hi sq (hi ▸ sq)]
    exact fun hiso ↦ F.not_isIso
      (isIso_baseChangeHomologyMap_of_isIntegralHom_of_surjective Λ (q : ℤ) hqZ hprev'
        F.isPullback_fibre πK hπK (hi ▸ sq) F.F hiso)
  have h₂ : ¬ IsIso (baseChangeHomologyMap Λ sq'' (q : ℤ)
      ((πK)^*[ModuleCat.{u + 1} Λ].obj F.F)) :=
    fun hiso ↦ h₁ ((isIso_baseChangeHomologyMap_iff_of_isIntegralHom Λ π hπ sq'' sq
      (q : ℤ) _).2 hiso)
  have hprev'' : BaseChangeProperty Λ (pullback.snd F.p' π) ((q : ℤ) - 1) := by
    rw [← hdegree]
    exact hprev (q - 1) le_rfl _ _ _ hpb
  have := mono_baseChangeHomologyMap Λ (q : ℤ) hqZ hprev'' sq''
    ((πK)^*[ModuleCat.{u + 1} Λ].obj F.F)
  have h₃ : ¬ IsZero ((baseChangeTargetFunctor Λ (pullback.fst g'' (pullback.snd F.p' π))
      (pullback.snd g'' (pullback.snd F.p' π)) (q : ℤ)).obj
        ((πK)^*[ModuleCat.{u + 1} Λ].obj F.F)) :=
    fun hz ↦ h₂ ((IsZero.of_mono (baseChangeHomologyMap Λ sq'' (q : ℤ)
      ((πK)^*[ModuleCat.{u + 1} Λ].obj F.F)) hz).isIso hz _)
  have : IsAffineHom (pullback.snd g'' (pullback.snd F.p' π)) :=
    MorphismProperty.of_isPullback sq'' inferInstance
  have hΛ : (n : Λ) = 0 := by
    apply ULift.ext
    exact ZMod.natCast_self n
  obtain ⟨r, _, hrn, _, hnonzero⟩ := exists_prime_cyclic_higherDirectImage Λ
    (pullback.fst g'' (pullback.snd F.p' π)) (pullback.snd g'' (pullback.snd F.p' π))
    n (by omega) hΛ (q : ℤ) _ h₃
  refine ⟨S'', pullback F.p' π, π ≫ F.a, pullback.fst F.p' π ≫ F.b,
    pullback.snd F.p' π, ?_, inferInstance, inferInstance, hnorm,
    inferInstance, K, inferInstance, inferInstance, i,
    pullback g'' (pullback.snd F.p' π), pullback.fst g'' (pullback.snd F.p' π),
    pullback.snd g'' (pullback.snd F.p' π), ?_, r, hrn, ?_⟩
  · exact ⟨hpb.toCommSq, hpb.isoPullback, hpb.isoPullback_hom_fst, hpb.isoPullback_hom_snd⟩
  · exact ⟨sq''.flip.toCommSq, sq''.flip.isoPullback,
      sq''.flip.isoPullback_hom_fst, sq''.flip.isoPullback_hom_snd⟩
  · let P := ULift.{u + 1} (ZMod r)
    let Y := pullback g'' (pullback.snd F.p' π)
    let h := pullback.snd g'' (pullback.snd F.p' π)
    let U := sheafCompose (pullback F.p' π).smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} P) AddCommGrpCat.{u + 1})
    let H := DerivedCategory.Plus.singleFunctor
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
        (lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor _ (q : ℤ)
    let C := constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}
    let R := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom P)
    have : R.IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1} (Int.castRingHom P)).isLeftAdjoint
    let er : R ⋙ forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1} ≅
        forget₂ (ModuleCat.{u + 1} P) AddCommGrpCat.{u + 1} := Iso.refl _
    have : (forget₂ (ModuleCat.{u + 1} P) AddCommGrpCat.{u + 1}).IsLeftAdjoint :=
      Functor.isLeftAdjoint_of_iso er
    obtain ⟨ec⟩ := nonempty_higherDirectImage_forget_iso P h (q : ℤ)
      (constantModSheaf P Y r)
    let cc := (constantCommuteCompose Y.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} P) AddCommGrpCat.{u + 1})).app
        (ModuleCat.of P (P ⧸ (Ideal.span {(r : P)} : Ideal P)))
    have hrP : (r : P) = 0 := by
      apply ULift.ext
      exact ZMod.natCast_self r
    have hspan : (Ideal.span {(r : P)} : Ideal P) = ⊥ := by simp [hrP]
    let l : ModuleCat.of.{u + 1} P (P ⧸ (Ideal.span {(r : P)} : Ideal P)) ≅
        ModuleCat.of.{u + 1} P P :=
      (Submodule.quotEquivOfEqBot _ hspan).toModuleIso
    let lc := (forget₂ (ModuleCat.{u + 1} P) AddCommGrpCat.{u + 1}).mapIso l
    intro hz
    have hU : IsZero (U.obj
        (higherDirectImage P h (q : ℤ) (constantModSheaf P Y r))) :=
      IsZero.of_iso hz (ec ≪≫ H.mapIso (cc ≪≫ C.mapIso lc))
    apply hnonzero
    apply (IsZero.iff_id_eq_zero _).mpr
    apply U.zero_of_map_zero
    change U.map (𝟙 (higherDirectImage P h (q : ℤ) (constantModSheaf P Y r))) = 0
    rw [U.map_id]
    exact (IsZero.iff_id_eq_zero _).mp hU

end AlgebraicGeometry.Etale
