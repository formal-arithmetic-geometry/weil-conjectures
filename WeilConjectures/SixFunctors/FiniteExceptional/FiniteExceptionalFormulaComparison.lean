/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalDualComparison
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorConstruction
import WeilConjectures.SixFunctors.Supporting.PullbackTorAmplitude
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated

/-! # The finite exceptional comparison constructed from Verdier duality

Source: current blueprint lem-coef-finite-exceptional.proof.md, paragraph 2.
(blueprint: lem-sf-finite-exceptional-formula-comparison).

Transport the ordinary K-flat quotient/pullback associator to the actual quotient
presentation by adjoint uniqueness. Ordinary pullback preserves constructibility and
finite Tor amplitude; the unit-normalized finite realization identifies its two
presentations. The Y dual comparison followed by pullback gives the inner isomorphism.
Apply the X dual comparison, then the contravariant X dual of the inverse inner
isomorphism. Finally conjugate by the prescribed evaluation-normalized formula
isomorphisms. This constructs the comparison from fixed maps, independently of the
assertion that the exceptional adjunction mate is invertible.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteExceptional
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  [Xsep : IsSeparated (X ↘ Spec (.of D.k))]
  [Ysep : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fsep : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]

omit Xsep Ysep in
include D hl Xbase Ybase Xft Xqc Yft Yqc fbase fsep fft fqc in
/-- Ordinary pullback preserves the actual finite-Tor constructible domain. -/
theorem pull_mem (n : ℕ) (K : (domain l E Y n).FullSubcategory) :
    domain l E X n ((finiteDerivedPullback l E n f).obj K.obj) := by
  let XO : Over (Spec (.of D.k)) := Over.mk (X ↘ Spec (.of D.k))
  let YO : Over (Spec (.of D.k)) := Over.mk (Y ↘ Spec (.of D.k))
  let fo : XO ⟶ YO := Over.homMk f (CategoryTheory.comp_over f (Spec (.of D.k)))
  let : LocallyOfFiniteType XO.hom := Xft
  let : QuasiCompact XO.hom := Xqc
  let : LocallyOfFiniteType YO.hom := Yft
  let : QuasiCompact YO.hom := Yqc
  let : IsSeparated fo.left := fsep
  let : LocallyOfFiniteType fo.left := fft
  let : QuasiCompact fo.left := fqc
  have ht := sf_pullback_finiteTorConstructible D l hl E (n + 1) (Nat.succ_pos n)
    XO YO fo K.obj K.property
  have : (domain l E X n).IsClosedUnderIsomorphisms :=
    (finite_ctf_isTriangulated l E (n + 1) (Nat.succ_pos n) X).1
  let r : sfFiniteDerivedPullback l E (n + 1) (Nat.succ_pos n) f ≅ finiteDerivedPullback l E n f :=
    @Functor.mapDerivedCategoryNatIso
      (normalizedDVRModules l E Y n) (normalizedDVRModules l E X n) _ _
      (SheafOfModules.instAbelian (integralCoefficientSheaf l E Y n))
      (SheafOfModules.instAbelian (integralCoefficientSheaf l E X n)) _ _
      (proEtaleRingModulePullback f
        (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n))
      (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
      (proEtaleRingModulePullback_additive f
        (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n))
      (sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f)
      (proEtaleRingModulePullback_preservesFiniteLimits f
        (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n))
      (proEtaleRingModulePullback_preservesFiniteColimits f
        (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n))
      (sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f)
      (sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f)
      (pullbackTensorFiniteRealization l E f n)
  dsimp [XO, YO, fo] at ht
  exact (domain l E X n).prop_of_iso (r.app K.obj) ht

variable (c : Compactification f)

end WeilConjectures.FiniteExceptional
