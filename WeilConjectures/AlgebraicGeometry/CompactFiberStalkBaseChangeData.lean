/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactFiberStalk
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange

/-!
# Data for compact-support stalk base change

The fibre identification and the three categorical comparison propositions used by
`WeilConjectures.AlgebraicGeometry.CompactFiberStalkBaseChange` are collected here so their coherence
obligations can be stated independently.
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- The canonical identification of the iterated geometric fibre with the direct
fibre. Source: latest blueprint, thm-pur-rank-one-thom.proof.md, Step 3
(blueprint: lem-pur-cfiber-stalk-base-change). This is the universal-property
isomorphism of the horizontally pasted pullback square. -/
noncomputable def compactFiberStalkFibreIso
    {X Y Y' T : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (b' : T ⟶ Y') :
    pullback (pullback.snd f g) b' ≅ pullback f (b' ≫ g) :=
  ((IsPullback.of_hasPullback (pullback.snd f g) b').paste_horiz
    (IsPullback.of_hasPullback f g)).isoPullback

/-- The unbounded compactification exchange square, evaluated by derived sections
on `T`. Source: latest blueprint, thm-pur-rank-one-thom.proof.md, Step 3
(blueprint: lem-pur-cfiber-stalk-base-change). For `T = Spec Ω` these are the
stalk and compact-fibre comparisons of lem-pur-cfiber-stalk. The outer square
uses the iterated fibre as its pullback object; its `isoPullback` is precisely
`compactFiberStalkFibreIso`. The final comparison transports the iterated
compactification to the compactification of that outer square. -/
def compactFiberStalkBaseChangeSquare
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' T : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ T}
    {g : Y' ⟶ Y} {gE : X' ⟶ X} {b' : T ⟶ Y'} {bE : X'' ⟶ X'}
    [QuasiCompact f'']
    (sq : IsPullback gE f' f g) (sq' : IsPullback bE f'' f' b')
    (sqd : IsPullback (bE ≫ gE) f'' f (b' ≫ g))
    (c : Compactification f)
    (K : DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) : Prop := by
  let B := ModuleCat.{u + 1} A
  let cp := c.ofIsPullback sq
  let cpp := cp.ofIsPullback sq'
  let cd := c.ofIsPullback sqd
  exact (Etale.rightDerivedGlobalSections B T).map
    ((Etale.leftDerivedUpperStarComp B b' g).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification B c).obj K) ≫
      ((Etale.upperStar B b').leftDerivedFunctor).map
        ((Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap B sq c).app K) ≫
      (Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap B sq' cp).app
        (((Etale.upperStar B gE).leftDerivedFunctor).obj K) ≫
      (Etale.rightDerivedLowerShriekOfCompactification B cpp).map
        ((Etale.leftDerivedUpperStarComp B bE gE).inv.app K) ≫
      (Etale.rightDerivedLowerShriekOfCompactificationIso A cpp cd).hom.app
        (((Etale.upperStar B (bE ≫ gE)).leftDerivedFunctor).obj K)) =
    (Etale.rightDerivedGlobalSections B T).map
      ((Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap B
        sqd c).app K)

/-- Three-square compatibility after a further base change. Source: latest
blueprint, thm-pur-rank-one-thom.proof.md, Step 3
(blueprint: lem-pur-cfiber-stalk-base-change). The three exchange components
are written separately, and both inverse-image compositors and the final
compactification transport are retained. -/
def compactFiberStalkBaseChangeThreeSquares
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X₁ X₂ X₃ Y Y₁ Y₂ T : Scheme.{u}}
    {f : X ⟶ Y} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂} {f₃ : X₃ ⟶ T}
    {g₁ : Y₁ ⟶ Y} {g₂ : Y₂ ⟶ Y₁} {b : T ⟶ Y₂}
    {a₁ : X₁ ⟶ X} {a₂ : X₂ ⟶ X₁} {a₃ : X₃ ⟶ X₂}
    [QuasiCompact f₃]
    (sq₁ : IsPullback a₁ f₁ f g₁) (sq₂ : IsPullback a₂ f₂ f₁ g₂)
    (sq₃ : IsPullback a₃ f₃ f₂ b) (c : Compactification f)
    (K : DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) : Prop := by
  let B := ModuleCat.{u + 1} A
  let c₁ := c.ofIsPullback sq₁
  let c₂ := c₁.ofIsPullback sq₂
  let c₃ := c₂.ofIsPullback sq₃
  let sqd := (sq₃.paste_horiz sq₂).paste_horiz sq₁
  let cd := c.ofIsPullback sqd
  let K₁ := (Etale.upperStar B a₁).leftDerivedFunctor.obj K
  let K₂ := (Etale.upperStar B a₂).leftDerivedFunctor.obj K₁
  let e := Etale.leftDerivedUpperStarComp B (a₃ ≫ a₂) a₁ ≪≫
    Functor.isoWhiskerLeft (Etale.upperStar B a₁).leftDerivedFunctor
      (Etale.leftDerivedUpperStarComp B a₃ a₂)
  exact (Etale.rightDerivedGlobalSections B T).map
    ((Etale.leftDerivedUpperStarComp B (b ≫ g₂) g₁).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification B c).obj K) ≫
      (Etale.upperStar B (b ≫ g₂)).leftDerivedFunctor.map
        ((Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap B sq₁ c).app K) ≫
      (Etale.leftDerivedUpperStarComp B b g₂).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification B c₁).obj K₁) ≫
      (Etale.upperStar B b).leftDerivedFunctor.map
        ((Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap B sq₂ c₁).app K₁) ≫
      (Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap B sq₃ c₂).app K₂ ≫
      (Etale.rightDerivedLowerShriekOfCompactification B c₃).map (e.inv.app K) ≫
      (Etale.rightDerivedLowerShriekOfCompactificationIso A c₃ cd).hom.app
        ((Etale.upperStar B ((a₃ ≫ a₂) ≫ a₁)).leftDerivedFunctor.obj K)) =
    (Etale.rightDerivedGlobalSections B T).map
      ((Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap B sqd c).app K)

/-- Independence of the geometric stalk comparison under a change of
compactification, as an equality of arrows after the canonical comparisons
on both ends. Source: latest blueprint, thm-pur-rank-one-thom.proof.md, Step 3
(blueprint: lem-pur-cfiber-stalk-base-change). -/
def compactFiberStalkBaseChangeIndependent
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y T : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ T}
    {b : T ⟶ Y} {bE : X' ⟶ X} [QuasiCompact f] [QuasiCompact f']
    (sq : IsPullback bE f' f b) (c d : Compactification f)
    (K : DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) : Prop := by
  let B := ModuleCat.{u + 1} A
  exact (Etale.rightDerivedGlobalSections B T).map
    (((Etale.upperStar B b).leftDerivedFunctor).map
        ((Etale.rightDerivedLowerShriekOfCompactificationIso A c d).hom.app K) ≫
      (Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap B sq d).app K) =
    (Etale.rightDerivedGlobalSections B T).map
      ((Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap B sq c).app K ≫
        (Etale.rightDerivedLowerShriekOfCompactificationIso A
          (c.ofIsPullback sq) (d.ofIsPullback sq)).hom.app
            (((Etale.upperStar B bE).leftDerivedFunctor).obj K))


end WeilConjectures
