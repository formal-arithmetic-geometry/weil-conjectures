/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDirectImageCoordinates
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedMateEvaluation

/-! # AffineSpectrumPullbackSquareCoherence

Source: Stacks Project, Tags 0D5S and 08HY.
(blueprint: lem-pc-affine-spectrum-pullback-square-coherence).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

@[reassoc] private theorem composition_assoc_reverse {W X Y Z : Scheme.{u}}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (N : schemeDerivedCategory Z) :
    (canonicalDerivedPullbackComposition a b).hom.app ((derivedPullback c).obj N) ≫
      (canonicalDerivedPullbackComposition (a ≫ b) c).hom.app N =
    (derivedPullback a).map ((canonicalDerivedPullbackComposition b c).hom.app N) ≫
      (canonicalDerivedPullbackComposition a (b ≫ c)).hom.app N ≫
      eqToHom (congrArg (fun q => (derivedPullback q).obj N) (Category.assoc a b c).symm) := by
  apply (cancel_mono (eqToHom
    (congrArg (fun q => (derivedPullback q).obj N) (Category.assoc a b c)))).1
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using
    (composition_assoc a b c N).symm

@[reassoc] private theorem composition_congr_left {P Q R : Scheme.{u}} (a a' : P ⟶ Q)
    (b : Q ⟶ R) (e : a = a') (N : schemeDerivedCategory R) :
    eqToHom (congrArg (fun q => (derivedPullback q).obj ((derivedPullback b).obj N)) e) ≫
      (canonicalDerivedPullbackComposition a' b).hom.app N =
    (canonicalDerivedPullbackComposition a b).hom.app N ≫
      eqToHom (congrArg (fun q => (derivedPullback q).obj N)
        (congrArg (fun q => q ≫ b) e)) := by
  subst a'
  simp

@[reassoc] private theorem composition_congr_right {P Q R : Scheme.{u}} (a : P ⟶ Q)
    (b b' : Q ⟶ R) (e : b = b') (N : schemeDerivedCategory R) :
    (derivedPullback a).map
        (eqToHom (congrArg (fun q => (derivedPullback q).obj N) e)) ≫
      (canonicalDerivedPullbackComposition a b').hom.app N =
    (canonicalDerivedPullbackComposition a b).hom.app N ≫
      eqToHom (congrArg (fun q => (derivedPullback q).obj N)
        (congrArg (fun q => a ≫ q) e)) := by
  subst b'
  simp

@[reassoc] private theorem square_naturality {P Q P' Q' : Scheme.{u}}
    (a : P ⟶ Q) (a' : P' ⟶ Q') (b : Q' ⟶ Q) (b' : P' ⟶ P)
    (e : b' ≫ a = a' ≫ b) {M N : schemeDerivedCategory Q} (k : M ⟶ N) :
    (derivedPullback a').map ((derivedPullback b).map k) ≫
        canonicalDerivedSquareComparison a a' b b' e N =
      canonicalDerivedSquareComparison a a' b b' e M ≫
        (derivedPullback b').map ((derivedPullback a).map k) := by
  let i := canonicalDerivedPullbackComposition a' b ≪≫
    eqToIso (congrArg (fun q => derivedPullback q) e.symm) ≪≫
    (canonicalDerivedPullbackComposition b' a).symm
  simpa only [i, canonicalDerivedSquareComparison, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, eqToIso.hom, eqToHom_app, Functor.comp_map, Category.assoc] using
    i.hom.naturality k

end AlgebraicGeometry
