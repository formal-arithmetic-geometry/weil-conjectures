/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.AlgebraicGeometry.HorizontalDualityMateComparisons
public import Mathlib.CategoryTheory.Comma.Arrow
public import Sheaf.AlgebraicGeometry.QCohInverseBaseChangeMate

/-! # Rectangle inverse mate with fixed endpoint comparisons

Source: Stacks Project, Tag 0ATR, proof of Lemma 48.5.2; Tag 0ATM.
(blueprint: lem-sc-horizontal-rectangle-inverse-mate-fixed-transport).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare
namespace AlgebraicGeometry

/-- Transport of the rectangle second mate to the mate of the pasted inverse ordinary
base-change square using the fixed source and target comparisons. There is no
middle right adjoint in this statement.
Source: Stacks Project, Tag 0ATR, proof of Lemma 48.5.2; Tag 0ATM.
(blueprint: lem-sc-horizontal-rectangle-inverse-mate-fixed-transport).

Proof: Transpose the ordinary rectangle base-change map under the outer
pullback/direct-image adjunction. Expand its counit definition and the two square
base-change maps. The associativity law of the pinned derived pullback composition
family and the two projection equations identify the transposes; injectivity of
the Hom equivalence gives ordinary base-change pasting. Conjugate and invert these
ordinary maps. Transport the upper adjunction through the pullback associativity
isomorphism, using the conjugate direct-image comparison. The counit compatibility
of right-adjoint uniqueness identifies this transport with
horizontalMateRightAdjointIso, hence with horizontalMateTargetIso after composing
the input pullbacks. Naturality of the units and counits gives the asserted
identity of the rectangle mate with the mate of the pasted inverse square. The
source comparison is exactly horizontalMateSourceIso by its construction from
the same composition family. No middle right adjoint, or invertibility of a second
mate, is used. All steps are natural transformation identities, so identity maps,
zero objects and empty schemes require no additional hypotheses. -/
theorem horizontal_rectangle_inverse_mate_fixed_transport
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' Z : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adjf : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y
          (QuasiCompact.compactSpace_of_compactSpace f)
          (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _ f _ _).fst E.obj E.property) ⊣ a)
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition E.obj))
    (K : schemeDerivedQCohCategory Y)
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
    let G := Arrow.mk ((derivedPullback (pullbackLeftPullbackSndIso f g h).hom).map
      ((schemeDerivedQCohProperty (pullback f (h ≫ g))).ι.map
        (@dualityEquationBaseChangeMap _ X Y Z
          (QuasiCompact.compactSpace_of_compactSpace f)
          (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
          f (h ≫ g) a c adjf adjc hβh K)))
    let α := @qcInverseBaseChange _ X Y Y'
      (QuasiCompact.compactSpace_of_compactSpace f)
      (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _ f _ _ g hβ
    let δ := @qcInverseBaseChange _ (pullback f g) Y' Z
      (QuasiCompact.compactSpace_of_compactSpace (pullback.snd f g))
      (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
      (pullback.snd f g) _ _ h hβ₂
    let M := (schemeDerivedQCohProperty (pullback (pullback.snd f g) h)).ι.map
      ((mateEquiv adjf adjd (α ≫ₕ δ)).app K)
    G.hom ≫ (horizontalMateTargetIso f g h c d adjc adjd K).inv =
      (horizontalMateSourceIso f g h (a.obj K).obj).inv ≫ M := by sorry

end AlgebraicGeometry
