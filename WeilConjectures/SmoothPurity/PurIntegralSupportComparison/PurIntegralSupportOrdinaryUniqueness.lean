/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurIntegralSupportComparison.PurIntegralSupportComparisonData

/-! Uniqueness of normalized ordinary quotient-coordinate comparisons.

Source: Zheng Construction 4.1 and Lemma 4.10; blueprint
lem-route-ordinary-exists-unique, uniqueness step.
(blueprint: lem-route-ordinary-uniqueness)

The two normalized direct-image fields are determined sectionwise by cancellation
of the right-underlying comparison. The transpose equations and injectivity of the
four adjunction hom bijections then determine the inverse and extension fields;
proof irrelevance identifies the remaining normalization proofs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModules Opposite
open WeilConjectures AlgebraicGeometry.Scheme
namespace WeilConjectures.PurIntegralSupportComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  (S : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) c)
  (G : EtaleTowerBrownAdjunction S) (H : BrownTowerComparison.FiniteEvaluation S G)
  (D : BrownTowerComparison.TransportData S G H)

private theorem normalized_push_unique {T U : Scheme.{u}} (g : T ⟶ U)
    (I : CoefficientSystemOrdinaryImage
      (J := Scheme.ProEt.topology U) (K := Scheme.ProEt.topology T)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)
      (Scheme.proEtaleSheafInverseImage g (Type (u + 1)))
      (Scheme.proEtaleSheafDirectImage g (Type (u + 1)))
      (Scheme.proEtaleSheafAdjunction g (Type (u + 1))))
    (a a' : SemilinearProperOpen.push (quotientRings l E) (quotientMaps l E) g ⋙
        integralExceptionalCoordinates l E U ≅
      integralExceptionalCoordinates l E T ⋙ I.rightSystem)
    (ha : PushNormalized l E g I a) (ha' : PushNormalized l E g I a') : a = a' := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  suffices h : (a.hom.app M).app = (a'.hom.app M).app by
    have extensionality {P Q : CoefficientSystem
        (J := Scheme.ProEt.topology U)
        (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)}
        (s t : P ⟶ Q) (hst : s.app = t.app) : s = t := by
      change CoefficientSystem.Hom.{u + 1, u, u + 1} P Q at s t
      cases s
      cases t
      cases hst
      rfl
    exact extensionality _ _ h
  funext n
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  have h := eq_of_heq ((ha M n V x).trans (ha' M n V x).symm)
  have hu : Function.Injective
      (((I.rightUnderlying n).hom.app
        (((integralExceptionalCoordinates l E T).obj M).level n)).hom.app V) := by
    apply ConcreteCategory.bijective_of_isIso _ |>.injective
  let e := (SheafOfModules.evaluation _ V).mapIso
    ((I.rightEvaluation n).app ((integralExceptionalCoordinates l E T).obj M))
  exact (ConcreteCategory.bijective_of_isIso e.hom).injective (hu h)

/-- Any two normalized ordinary comparison records are equal.
Source: Zheng Construction 4.1 and the paragraph before Lemma 4.10;
uniqueness steps of lem-route-ordinary-exists-unique.
(blueprint: lem-pur-integral-support-ordinary-uniqueness)

Proof: the normalization equations for openPush and properPush identify their
section functions after postcomposition with rightEvaluation and rightUnderlying.
Both postcomposed maps are isomorphisms, hence injective on sections. Cancel them
and apply extensionality successively to module-sheaf maps, strict-system maps,
natural transformations and isomorphisms. The push fields agree.

In openPull_transpose take N to be the sequence inverse-image object of M and h
to be its identity. Both right sides now agree. Injectivity of the ordinary Hom
adjunction, followed by natural-isomorphism extensionality, identifies openPull.
In openExtension_transpose take N to be the sequence extension object of M and h
to be its identity. Cancel the already identified openPull component, and apply
injectivity of the extension Hom adjunction to identify openExtension. All
remaining record fields are propositions, so proof irrelevance identifies the
records. No existence of a record or nonempty-scheme hypothesis is used. -/
theorem ordinary_unique (B B' : Ordinary l E S G H D) : B = B' := by
  have hopen : B.openPush = B'.openPush :=
    normalized_push_unique l E c.i D.compact.openImage _ _
      B.openPush_normalized B'.openPush_normalized
  have hproper : B.properPush = B'.properPush :=
    normalized_push_unique l E c.g D.compact.properImage _ _
      B.properPush_normalized B'.properPush_normalized
  have hpull : B.openPull = B'.openPull := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply (D.compact.openImage.systemAdj.homEquiv _ _).injective
    have h := B.openPull_transpose M _ (𝟙 _)
    have h' := B'.openPull_transpose M _ (𝟙 _)
    erw [CategoryTheory.Functor.map_id, Category.comp_id, hopen] at h
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at h'
    exact h.trans h'.symm
  have hext : B.openExtension = B'.openExtension := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply (D.compact.openAdjunction.homEquiv _ _).injective
    apply (cancel_mono (B'.openPull.hom.app _)).1
    have h := B.openExtension_transpose M _ (𝟙 _)
    have h' := B'.openExtension_transpose M _ (𝟙 _)
    erw [CategoryTheory.Functor.map_id, Category.comp_id, hpull] at h
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at h'
    exact h.trans h'.symm
  cases B
  cases B'
  cases hopen
  cases hproper
  cases hpull
  cases hext
  rfl

end WeilConjectures.PurIntegralSupportComparison
