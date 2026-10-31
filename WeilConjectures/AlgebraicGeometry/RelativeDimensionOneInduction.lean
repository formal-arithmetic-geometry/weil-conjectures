/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CumulativeUniversalBaseChangeProperty
import WeilConjectures.AlgebraicGeometry.UniversalBaseChangeFailureDatum
import WeilConjectures.AlgebraicGeometry.UniversalCurveTestVanishing

/-!
# The induction step in relative dimension one

Source: blueprint, sec-smooth-base-change/sk-lem-induction,
node sbc-lem-rel-dim-one-induction; Stacks Project, Tag 0EYU, second proof
(blueprint: sbc-lem-rel-dim-one-induction).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Apply the ring-based curve test after identifying an affine base with its spectrum. -/
private theorem isZero_curveTest_affine
    {S X Y : Scheme.{u}} [IsAffine S] [IsIntegral S] [IsAffine X]
    (hnorm : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    [IsAlgClosed S.functionField] (K : Type u) [Field K] [IsAlgClosed K]
    (i : S.functionField ⟶ CommRingCat.of K)
    (f : X ⟶ S) [IsAffineHom f] [SmoothOfRelativeDimension 1 f]
    (h : Y ⟶ X) (e : Y ⟶ Spec (.of K))
    (sq : ChosenCartesianSquare h e f
      (Spec.map i ≫ S.fromSpecStalk (genericPoint S)))
    (d : ℕ) (hd : IsUnit (d : Γ(S, ⊤))) (q : ℕ) (hq : 1 ≤ q) :
    Limits.IsZero ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((Etale.lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (Y.constantZMod d)))) := by
  have : Nonempty (⊤ : S.Opens) := ⟨⟨Classical.arbitrary S, trivial⟩⟩
  let A := Γ(S, ⊤)
  let L := S.functionField
  let : Algebra L K := i.hom.toAlgebra
  have : IsFractionRing A L :=
    functionField_isFractionRing_of_isAffineOpen S ⊤ (isAffineOpen_top S)
  have hA : IsNormalScheme (Spec (.of A)) := by
    refine ⟨inferInstance, fun x ↦ ⟨inferInstance, ?_⟩⟩
    have := hnorm (S.isoSpec.inv x)
    exact IsIntegrallyClosed.of_equiv
      (asIso (S.isoSpec.inv.stalkMap x)).commRingCatIsoToRingEquiv
  have hp : IsPullback h e f (Spec.map i ≫ S.fromSpecStalk (genericPoint S)) :=
    .of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  have hg : (Spec.map i ≫ S.fromSpecStalk (genericPoint S)) ≫ S.isoSpec.hom =
      Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A L)) := by
    change _ = Spec.map i ≫ Spec.map (S.germToFunctionField ⊤)
    rw [Category.assoc]
    congr 1
    exact Scheme.fromSpecStalk_toSpecΓ S (genericPoint S)
  have hp' : IsPullback h e (f ≫ S.isoSpec.hom)
      (Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A L))) :=
    hp.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) S.isoSpec
      (by simp) (by simp) (by simp) (by simpa using hg)
  have sq' : ChosenCartesianSquare h e (f ≫ S.isoSpec.hom)
      (Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A L))) :=
    { hp'.toCommSq with
      isoPullback := hp'.isoPullback
      hom_fst := by simp
      hom_snd := by simp }
  have : SmoothOfRelativeDimension 1 (f ≫ S.isoSpec.hom) := by
    simpa using
      (inferInstance : SmoothOfRelativeDimension (1 + 0) (f ≫ S.isoSpec.hom))
  simpa only [Int.natAbs_natCast, rightDerivedLowerStarPlus] using
    (isZero_universalCurveTest_higherDirectImage A L K hA (f ≫ S.isoSpec.hom)
      h e sq' (d : ℤ) (by simpa using hd) (q : ℤ) (by omega))

/-- An affine smooth relative curve with affine source satisfies universal base change
in degree `q` if it does in all nonnegative degrees through `q - 1`; consequently it
satisfies the cumulative universal property through `q`.
Source: blueprint, sec-smooth-base-change/sk-lem-induction,
node sbc-lem-rel-dim-one-induction; Stacks Project, Tag 0EYU, second proof
(blueprint: sbc-lem-rel-dim-one-induction).

Proof plan: Suppose universal base change in degree `q` fails. By
`sbc-lem-bc-universal-test`, the cumulative universal lower-degree assumption gives two
Cartesian squares over an affine integral normal base with algebraically closed function
field `L`, and a dominant geometric generic map from `Spec K`, together with a divisor
`d` of `n` whose constant cyclic sheaf has nonzero degree-`q` higher direct image along
the horizontal map. Dominance extends the injection from the normal domain to `K` to
an inclusion of its fraction field `L` into `K`. By
`lem-weil-pbc-affine-morphism-permanence` and
`lem-sbc-smooth-relative-dimension-permanence`, the base-changed curve remains affine
smooth of relative dimension one, with affine source. Pulling back the inverse of `n`
shows it is a unit on this base; writing `n = d * a` shows that `d` is a unit there too.
Now `sbc-thm-universal-test-vanishing` makes that higher direct image zero since `q ≥ 1`,
a contradiction. Finally, a nonnegative degree at most `q` either equals `q` or is at
most `q - 1`, giving the cumulative conclusion. -/
theorem universalBaseChangeProperty_relativeDimensionOne_induction
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]
    [SmoothOfRelativeDimension 1 f] [IsAffine X]
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(S, ⊤)))
    (q : ℕ) (hq : 1 ≤ q)
    (hprev : CumulativeUniversalBaseChangeProperty f n hn hinv (q - 1)) :
    UniversalBaseChangeProperty (ULift.{u + 1} (ZMod n)) f (q : ℤ) ∧
      CumulativeUniversalBaseChangeProperty f n hn hinv q := by
  classical
  have hnew : UniversalBaseChangeProperty (ULift.{u + 1} (ZMod n)) f (q : ℤ) := by
    by_contra hfail
    obtain ⟨S', X', a, b, f', sq, haff, hint, hnorm, halg, K, hK, hKalg,
      i, Y, e, h, sq', d, hd, hne⟩ :=
      exists_universalBaseChangeFailure_cyclic_datum f n hn hinv q hq hprev hfail
    have hp : IsPullback b f' f a :=
      .of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
    have : IsAffineHom f' := MorphismProperty.of_isPullback hp inferInstance
    have : SmoothOfRelativeDimension 1 f' :=
      (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback hp inferInstance
    have : IsAffine X' := isAffine_of_isAffineHom f'
    have hd' : IsUnit (d : Γ(S', ⊤)) :=
      isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) (by simpa using hinv.map a.appTop.hom)
    exact hne (isZero_curveTest_affine hnorm K i f' h e sq' d hd' q hq)
  refine ⟨hnew, ?_⟩
  intro r hr
  by_cases heq : r = q
  · simpa only [heq] using hnew
  · exact hprev r (by omega)

end AlgebraicGeometry.Etale
