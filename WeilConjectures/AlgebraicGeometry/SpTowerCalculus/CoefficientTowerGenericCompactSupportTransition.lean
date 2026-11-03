/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerGenericTransitions
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerGenericCompactSupportFiniteMateSquare
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerGenericCompactSupportTransitionMate

/-! # Strict transitions in intrinsic coefficient coordinates

Source: Zheng, Construction 4.1; Stacks 07A6; the first step of the
coefficient-tower transition compatibility argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.SpTowerCalculus
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

private theorem coefficientSquare_converse
    {XA XB YA YB : Type*} [Category XA] [Category XB] [Category YA] [Category YB]
    {TX : XA ⥤ XB} {RX : XB ⥤ XA} {TY : YA ⥤ YB} {RY : YB ⥤ YA}
    (ax : TX ⊣ RX) (ay : TY ⊣ RY) (FA : XA ⥤ YA) (FB : XB ⥤ YB)
    (d : RX ⋙ FA ≅ FB ⋙ RY) (b : FA ⋙ TY ⟶ TX ⋙ FB)
    (hc : ∀ L, TY.map (d.hom.app L) ≫ ay.counit.app (FB.obj L) =
      b.app (RX.obj L) ≫ FB.map (ax.counit.app L))
    {Pn : XA} {Pm : XB} {Qn : YA} {Qm : YB}
    (tP : Pn ⟶ RX.obj Pm) (tQ : Qn ⟶ RY.obj Qm)
    (θn : Qn ⟶ FA.obj Pn) (θm : Qm ⟶ FB.obj Pm)
    (rx : TX.obj Pn ⟶ Pm) (ry : TY.obj Qn ⟶ Qm)
    (hx : ax.homEquiv _ _ rx = tP) (hy : ay.homEquiv _ _ ry = tQ)
    (ht : TY.map θn ≫ b.app _ ≫ FB.map rx = ry ≫ θm) :
    tQ ≫ RY.map θm = θn ≫ FA.map tP ≫ d.hom.app Pm := by
  have hrx : TX.map tP ≫ ax.counit.app Pm = rx := by
    calc
      _ = (ax.homEquiv Pn Pm).symm tP := (ax.homEquiv_counit _ _ _).symm
      _ = rx := by rw [← hx]; exact (ax.homEquiv _ _).symm_apply_apply rx
  have hry : TY.map tQ ≫ ay.counit.app Qm = ry := by
    calc
      _ = (ay.homEquiv Qn Qm).symm tQ := (ay.homEquiv_counit _ _ _).symm
      _ = ry := by rw [← hy]; exact (ay.homEquiv _ _).symm_apply_apply ry
  apply (ay.homEquiv _ _).symm.injective
  rw [ay.homEquiv_counit, ay.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  have hc' := congrArg (fun z ↦ TY.map (FA.map tP) ≫ z) (hc Pm)
  rw [hc']
  rw [reassoc_of% (b.naturality tP)]
  rw [← FB.map_comp, hrx]
  have hn : TY.map (RY.map θm) ≫ ay.counit.app (FB.obj Pm) =
      ay.counit.app Qm ≫ θm := by
    simpa only [Functor.comp_map, Functor.id_map] using ay.counit.naturality θm
  have hn' := congrArg (fun z ↦ TY.map tQ ≫ z) hn
  rw [hn']
  rw [← Category.assoc, hry]
  rw [ht]

/-- The normalized generic compact-support evaluation preserves the actual strict
transition before transport to original tower coordinates.
Source: Zheng 4.10; Stacks 0D6D and 0D6E; blueprint Levels paragraph.
Proof: for the proper factor apply Geometry.transitionFormula and take its scalar
adjunction transpose. The coefficient mate is normalized by the geometric counit,
so its restriction comparison is the prescribed inverse direct-image restriction
comparison. For the open factor, apply its ordinary adjunction to the transition
square. Its unit_evaluation and counit_evaluation reduce this to the pullback
transition square: both maps place the horizontal transition into the same open
structural summand. Localize the resulting ordinary open square termwise. Paste
with the proper square, cancel the middle evaluation comparisons, and unfold
Fcomparison. The pasted restriction comparison is intrinsicCompactSupportRestriction.
The argument applies to all ambient derived systems and uses no finite-Tor premise.
(blueprint: lem-sp-tower-generic-compact-support-transition). -/
theorem generic_compactSupport_intrinsicTransition
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : SpTowerShriek.D l E X) {m n : ℕ} (v : m ≤ n) :
    (genericIntrinsicTransitions l E Y v).app ((SpTowerShriek.F l E b o c).obj K) ≫
      (scalarRestriction (quotient l E v) Y).map
        ((SpTowerShriek.Fcomparison l E b o c m).hom.app K) =
    (SpTowerShriek.Fcomparison l E b o c n).hom.app K ≫
      (reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).map
        ((genericIntrinsicTransitions l E X v).app K) ≫
      (intrinsicCompactSupportRestriction (quotient l E v) c.i c.g).hom.app
        ((SpTowerShriek.Ev l E X m).obj K) := by
  let adjX := proEtaleRingDerivedExtensionAdjunction
    (proEtaleConstantRingMap (T := X) (quotient l E v))
  let adjY := proEtaleRingDerivedExtensionAdjunction
    (proEtaleConstantRingMap (T := Y) (quotient l E v))
  let rX := genericCompactSupportRho l E X K v
  let rY := genericCompactSupportRho l E Y ((SpTowerShriek.F l E b o c).obj K) v
  have hfinite := generic_compactSupport_finiteMateSquare l E b o c K v
  have hword := hfinite
  have hc := generic_compactSupport_counitSquare l E c v
  have hx : adjX.homEquiv _ _ rX =
      (genericIntrinsicTransitions l E X v).app K := by
    simpa only [rX, adjX, genericCompactSupportRho] using
      (adjX.homEquiv _ _).apply_symm_apply
        ((genericIntrinsicTransitions l E X v).app K)
  have hy : adjY.homEquiv _ _ rY =
      (genericIntrinsicTransitions l E Y v).app
        ((SpTowerShriek.F l E b o c).obj K) := by
    simpa only [rY, adjY, genericCompactSupportRho] using
      (adjY.homEquiv _ _).apply_symm_apply
        ((genericIntrinsicTransitions l E Y v).app
          ((SpTowerShriek.F l E b o c).obj K))
  have hsquare := coefficientSquare_converse
    adjX adjY
    (reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g)
    (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g)
    (intrinsicCompactSupportRestriction (quotient l E v) c.i c.g)
    (reductionDirectImageComparison (quotient l E v) c.i c.g)
    hc
    ((genericIntrinsicTransitions l E X v).app K)
    ((genericIntrinsicTransitions l E Y v).app
      ((SpTowerShriek.F l E b o c).obj K))
    ((SpTowerShriek.Fcomparison l E b o c n).hom.app K)
    ((SpTowerShriek.Fcomparison l E b o c m).hom.app K)
    rX rY hx hy hword.symm
  simpa only [rX, rY] using hsquare

end AlgebraicGeometry.ProEtale.SpTowerCalculus
