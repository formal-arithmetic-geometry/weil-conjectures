/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.AlgebraicGeometry.HorizontalDualityMateComparisons
public import Sheaf.AlgebraicGeometry.QCohInverseBaseChangeMate

/-! # Ordinary inverse-square pasting with the fixed upper transport

Source: Stacks Project, Tags 0ATM and 0ATR.
(blueprint: lem-sc-horizontal-inverse-square-fixed-pasting).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare
namespace AlgebraicGeometry

/-- The pasted inverse ordinary square agrees with the rectangle inverse square,
after changing its upper projection and base pullback by the pinned comparisons.
This statement involves no right adjoint to the bottom direct image.
Source: Stacks Project, Remark 20.28.5 (Tag 0ATM), and Lemma 48.5.2 (Tag 0ATR).
(blueprint: lem-sc-horizontal-inverse-square-fixed-pasting).

Proof: Transpose the rectangle ordinary square and the horizontal composite under
pullback along the outer upper projection. Expand schemeDerivedBaseChangeMap as
its defining counit transpose. Naturality moves each composition comparison past
the counit. Apply associativity of the pinned pullback composition family to the
base chain h,g and to the upper projection chain. The two projection equations
of pullbackLeftPullbackSndIso identify the resulting maps; injectivity of the
adjunction Hom equivalence gives ordinary pasting. Invert these ordinary squares.
The comparison of direct images along the upper scheme isomorphism is the
conjugate of the pinned pullback comparison. Its right-adjoint comparison is
horizontalMateRightAdjointIso: use rightAdjointUniq_hom_app_counit for the
transported adjunction, then the equivalence triangle identities. Consequently
its inverse ordinary square is the inverse mate of that right-adjoint comparison.
Whiskering the inverted ordinary pasting equation with the two pullback
comparisons gives the displayed identity. All comparisons are natural, and all
cancellations invert only ordinary squares or the displayed isomorphisms; zero
objects, identity morphisms and empty schemes are included. -/
theorem horizontal_inverse_square_fixed_pasting
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
    (c : schemeDerivedQCohCategory Z ⥤
      schemeDerivedQCohCategory (pullback f (h ≫ g)))
    (adjc : (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty (pullback f (h ≫ g))).ι ⋙
        schemeDerivedDirectImage (pullback.snd f (h ≫ g))) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (h ≫ g))) _ _ _ _
          (pullback.snd f (h ≫ g)) _ _).fst E.obj E.property) ⊣ c)
    (hβh : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f (h ≫ g)) (h ≫ g)
        (pullback.fst f (h ≫ g)) pullback.condition E.obj))
    (d : schemeDerivedQCohCategory Z ⥤
      schemeDerivedQCohCategory (pullback (pullback.snd f g) h))
    (adjd : (schemeDerivedQCohProperty Z).lift
      ((schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι ⋙
        schemeDerivedDirectImage (pullback.snd (pullback.snd f g) h)) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd (pullback.snd f g) h))
          _ _ _ _ (pullback.snd (pullback.snd f g) h) _ _).fst E.obj E.property) ⊣ d)
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
    let r := horizontalMateRightAdjointIso (pullbackLeftPullbackSndIso f g h)
      (pullback.snd f (h ≫ g)) (pullback.snd (pullback.snd f g) h)
      (pullbackLeftPullbackSndIso_hom_snd f g h) c d adjc adjd
    let κ := (mateEquiv adjc adjd).symm
      (r.inv ≫ (Functor.leftUnitor d).inv)
    let τ := qcInverseBaseChange f (h ≫ g) hβh
    let σ := qcInverseBaseChange f g hβ ≫ₕ
      @qcInverseBaseChange _ (pullback f g) Y' Z _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
        (pullback.snd f g) _ _ h hβ₂
    ∀ E : schemeDerivedQCohCategory X,
      (horizontalMatePushforward (pullback.snd (pullback.snd f g) h)).map
          (s.hom.app E) ≫ (τ ≫ₕ κ).app E =
        σ.app E ≫ (horizontalMateComp h g).hom.app
          ((horizontalMatePushforward f).obj E) := by sorry

end AlgebraicGeometry
