/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.AlgebraicGeometry.HorizontalDualityMateComparisons
public import Sheaf.AlgebraicGeometry.QCohInverseBaseChangeMate
import Sheaf.AlgebraicGeometry.DerivedBaseChangeHorizontalPasting
import Sheaf.AlgebraicGeometry.DerivedBaseChangePasting

/-! # Forward ordinary geometric pasting with fixed comparisons

Source: Stacks Project, Tags 0ATM and 0ATR.
(blueprint: lem-sc-horizontal-ordinary-forward-fixed-pasting).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare
namespace AlgebraicGeometry

/-- The canonical ordinary transfer square for a scheme isomorphism over a base.
Source: Stacks Project, Tags 0D5S, 0D5T and 0ATR.
(blueprint: def-sc-horizontal-ordinary-transfer).

Its data are constructed from the pinned direct-image composition, right-adjoint
uniqueness for pullback, and the inverse unit of the explicit equivalence. -/
noncomputable def horizontalOrdinaryTransfer
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {P Q Z : Scheme.{u}}
    [CompactSpace P] [QuasiSeparatedSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (e : P ≅ Q) (q : Q ⟶ Z) (p : P ⟶ Z)
    [QuasiCompact q] [QuasiSeparated q] [QuasiCompact p] [QuasiSeparated p]
    (hp : e.hom ≫ q = p) :
    TwoSquare (horizontalMatePullback e.hom) (horizontalMatePushforward q)
      (horizontalMatePushforward p) (𝟭 (schemeDerivedQCohCategory Z)) :=
  let ev := horizontalMateEquivalence e
  let ri := (horizontalMateAdjunction e.hom).rightAdjointUniq ev.toAdjunction
  let li := eqToIso (congrArg qcDirectImage hp.symm) ≪≫
    horizontalMatePushComp e.hom q ≪≫
    Functor.isoWhiskerRight ri (horizontalMatePushforward q)
  .mk _ _ _ _ <|
    (Functor.isoWhiskerLeft (horizontalMatePullback e.hom) li).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight ev.unitIso.inv (horizontalMatePushforward q) ≫
      (Functor.leftUnitor (horizontalMatePushforward q)).hom ≫
      (Functor.rightUnitor (horizontalMatePushforward q)).inv

/-- The fixed upper comparison, with the same three factors as the pinned family.
Source: Stacks Project, Tags 0D5S and 0ATR.
(blueprint: def-sc-horizontal-ordinary-upper-comparison). -/
noncomputable def horizontalOrdinaryUpperComparison
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y S T : Scheme.{u}} (f : X ⟶ Y) (g : S ⟶ Y) (h : T ⟶ S) :
    qcPullback (pullback.fst f g) ⋙ qcPullback (pullback.fst (pullback.snd f g) h) ≅
      qcPullback (pullback.fst f (h ≫ g)) ⋙
        qcPullback (pullbackLeftPullbackSndIso f g h).hom :=
  horizontalMateComp (pullback.fst (pullback.snd f g) h) (pullback.fst f g) ≪≫
    eqToIso (congrArg horizontalMatePullback
      (pullbackLeftPullbackSndIso_hom_fst f g h).symm) ≪≫
    (horizontalMateComp (pullbackLeftPullbackSndIso f g h).hom
      (pullback.fst f (h ≫ g))).symm

/-- The fixed base comparison, with the QCoh functors displayed in its signature.
Source: Stacks Project, Tag 0D5S.
(blueprint: def-sc-horizontal-ordinary-base-comparison). -/
noncomputable def horizontalOrdinaryBaseComparison
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {Y S T : Scheme.{u}} (g : S ⟶ Y) (h : T ⟶ S) :
    qcPullback g ⋙ qcPullback h ≅ qcPullback (h ≫ g) := horizontalMateComp h g

/-- Forward ordinary base-change pasting with the canonical comparisons, without
any invertibility hypothesis on base change.
Source: Stacks Project, Remark 20.28.5 (Tag 0ATM), Remark 20.28.3 (Tag 08HY),
and Lemma 20.27.2 (Tag 0D5S).
(blueprint: lem-sc-horizontal-ordinary-forward-fixed-pasting).

Proof: Transpose the outer ordinary square and the two successive ordinary squares
under the pinned adjunction for the iterated second projection. Expand each base-change
map as pullback of the counit followed by adjunction transposition. Naturality moves the
first counit through the second comparison; the middle projection triangle identity
cancels its unit and counit. Associativity of the pinned pullback comparison family
identifies the base chain h,g and the upper chain of first projections. The two projection
equations for the canonical pullback isomorphism identify the scheme maps and their
transports. The conjugate of the pullback composition comparison is the pinned direct
image comparison. Right-adjoint uniqueness identifies direct image along the scheme
isomorphism with the inverse of its explicitly constructed pullback equivalence;
the inverse equivalence unit cancels that inverse pullback. Thus the transported outer
square has exactly the displayed transfer component k. Injectivity of the adjunction
Hom equivalence gives the ambient equation, and faithfulness of the QCoh inclusions
reflects it to the displayed equality. No ordinary square is inverted. The calculation
uses only naturality and triangle identities, so identity arrows, empty schemes and
zero complexes require no extra hypothesis. -/
theorem horizontal_ordinary_forward_fixed_pasting
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' Z : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (h : Z ⟶ Y') :
    letI : QuasiSeparatedSpace (pullback f (h ≫ g) : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))
    letI : QuasiSeparatedSpace (pullback (pullback.snd f g) h : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h)
    let s := horizontalOrdinaryUpperComparison f g h
    let e := pullbackLeftPullbackSndIso f g h
    let q := pullback.snd f (h ≫ g)
    let p := pullback.snd (pullback.snd f g) h
    let k := horizontalOrdinaryTransfer e q p (pullbackLeftPullbackSndIso_hom_snd f g h)
    let β := qcBaseChange f (h ≫ g)
    let γ := fun E : schemeDerivedQCohCategory X ↦
      (qcPullback h).map ((qcBaseChange f g).app E) ≫
        (@qcBaseChange _ (pullback f g) Y' Z _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
          (pullback.snd f g) _ _ h).app ((qcPullback (pullback.fst f g)).obj E)
    ∀ (s' : qcPullback (pullback.fst f g) ⋙
        qcPullback (pullback.fst (pullback.snd f g) h) ≅
        qcPullback (pullback.fst f (h ≫ g)) ⋙ qcPullback e.hom)
      (k' : TwoSquare (horizontalMatePullback e.hom)
        (horizontalMatePushforward q) (horizontalMatePushforward p)
        (𝟭 (schemeDerivedQCohCategory Z))),
      s' = s → k' = k → ∀ E : schemeDerivedQCohCategory X,
      (horizontalOrdinaryBaseComparison g h).hom.app ((qcDirectImage f).obj E) ≫
          β.app E =
        γ E ≫ (qcDirectImage p).map (s'.hom.app E) ≫
          k'.app ((qcPullback (pullback.fst f (h ≫ g))).obj E) := by sorry

end AlgebraicGeometry
