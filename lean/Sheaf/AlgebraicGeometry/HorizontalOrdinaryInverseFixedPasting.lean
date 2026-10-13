/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.AlgebraicGeometry.HorizontalDualityMateComparisons
public import Sheaf.AlgebraicGeometry.QCohInverseBaseChangeMate

/-! # Ordinary inverse geometric pasting with fixed comparisons

Source: Stacks Project, Tags 0ATM and 0ATR.
(blueprint: lem-sc-horizontal-ordinary-inverse-fixed-pasting).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare
namespace AlgebraicGeometry

/-- The ordinary inverse geometric pasting equation, before any supplied right
adjoints to the direct images of the outer or iterated projection are introduced.
Source: Stacks Project, Remark 20.28.5 (Tag 0ATM), and the ordinary-square
comparison used at the end of Lemma 48.5.2 (Tag 0ATR).
(blueprint: lem-sc-horizontal-ordinary-inverse-fixed-pasting).

Proof: Transpose the outer ordinary base-change square and the horizontally
pasted forward ordinary squares under the pinned pullback/direct-image adjunction
for the projection p. Expand base change as the transpose of pullback of the
counit for f. Naturality moves the first counit through the second square; the
middle projection's adjunction triangle cancels its intervening unit and counit.
Associativity of the pinned pullback comparison family identifies the base chain
h,g and the upper chain of first projections. The two projection equations for e
identify the scheme morphisms and their equality transports. The conjugate
composition comparison for direct images, followed by right-adjoint uniqueness
for e, is li. The inverse unit of ev removes inverse pullback followed by pullback.
Consequently, writing beta for the forward outer square and rho for the forward
paste, forward pasting says b.hom followed by beta equals rho followed by the
pushforward of s.hom followed by li and the inverse equivalence unit. Full
faithfulness of the QCoh inclusions reflects the three assumed component
isomorphisms. Multiply the forward equation on the left by the inverse of rho
and on the right by the inverse of beta. Naturality of inverse transformations
and functoriality of inverses identify the inverse of rho with sigma, the
horizontal composite of the two inverse ordinary squares. The resulting equation
is precisely the displayed formula. No right adjoint to p or q is supplied or
chosen in this argument; li uses only the pinned pullback/direct-image
adjunctions and the explicitly constructed scheme-isomorphism equivalence.
All cancellations involve assumed ordinary isomorphisms or the displayed
comparison isomorphisms, so identity maps, zero objects and empty schemes are
included. -/
theorem horizontal_ordinary_inverse_fixed_pasting
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' Z : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition E.obj))
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (h : Z ⟶ Y')
    (hβh : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f (h ≫ g)) (h ≫ g)
        (pullback.fst f (h ≫ g)) pullback.condition E.obj))
    (hβ₂ : ∀ E : schemeDerivedQCohCategory (pullback f g),
      IsIso (schemeDerivedBaseChangeMap (pullback.snd f g)
        (pullback.snd (pullback.snd f g) h) h
        (pullback.fst (pullback.snd f g) h) pullback.condition E.obj)) :
    letI : QuasiSeparatedSpace (pullback f (h ≫ g) : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))
    letI : QuasiSeparatedSpace (pullback (pullback.snd f g) h : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h)
    let s := horizontalMateComp (pullback.fst (pullback.snd f g) h) (pullback.fst f g) ≪≫
      eqToIso (congrArg horizontalMatePullback
        (pullbackLeftPullbackSndIso_hom_fst f g h).symm) ≪≫
      (horizontalMateComp (pullbackLeftPullbackSndIso f g h).hom
        (pullback.fst f (h ≫ g))).symm
    let e := pullbackLeftPullbackSndIso f g h
    let ev := horizontalMateEquivalence e
    let q := pullback.snd f (h ≫ g)
    let p := pullback.snd (pullback.snd f g) h
    let ri := (horizontalMateAdjunction e.hom).rightAdjointUniq ev.toAdjunction
    let li := eqToIso (congrArg qcDirectImage
        (pullbackLeftPullbackSndIso_hom_snd f g h).symm) ≪≫
      horizontalMatePushComp e.hom q ≪≫
      Functor.isoWhiskerRight ri (horizontalMatePushforward q)
    let k : TwoSquare (horizontalMatePullback e.hom)
        (horizontalMatePushforward q) (horizontalMatePushforward p)
        (𝟭 (schemeDerivedQCohCategory Z)) :=
      .mk _ _ _ _ <|
        (Functor.isoWhiskerLeft (horizontalMatePullback e.hom) li).hom ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight ev.unitIso.inv (horizontalMatePushforward q) ≫
          (Functor.leftUnitor (horizontalMatePushforward q)).hom ≫
          (Functor.rightUnitor (horizontalMatePushforward q)).inv
    let τ := qcInverseBaseChange f (h ≫ g) hβh
    let σ := qcInverseBaseChange f g hβ ≫ₕ
      @qcInverseBaseChange _ (pullback f g) Y' Z _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
        (pullback.snd f g) _ _ h hβ₂
    ∀ E : schemeDerivedQCohCategory X,
      (horizontalMatePushforward (pullback.snd (pullback.snd f g) h)).map
          (s.hom.app E) ≫ (τ ≫ₕ k).app E =
        σ.app E ≫ (horizontalMateComp h g).hom.app
          ((horizontalMatePushforward f).obj E) := by sorry

end AlgebraicGeometry
