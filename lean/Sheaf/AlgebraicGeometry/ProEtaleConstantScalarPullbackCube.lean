/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X7
-/
module

public import Sheaf.SecSmoothPurity.DirectImageScalarOperations
import Sheaf.AlgebraicGeometry.ProEtaleCanonicalDerivedPullbackNormalization
import Sheaf.SecSmoothPurity.ConstantScalarPullbackSquare
import Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# The coefficient cube for canonical constant-ring inverse images

Source: Stacks Project, Tags 0D6D and 0E47, coefficient inverse-image comparisons
(blueprint: lem-sp-constant-scalar-pullback-cube).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
-- Replaying the dependent transport calculations for tactic linting is expensive.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry.ProEtale
attribute [local irreducible] completedAdicDerivedChange
  Functor.mapDerivedCategory Functor.rightDerivedFunctor proEtaleCanonicalDerivedPullbackComparison
  proEtaleRingCompositeCoefficients

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem constantComp_normalized
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (A : Type u) [CommRing A] :
    eqToIso (congrArg
        (proEtaleRingDerivedPullback (h ≫ k) (proEtaleConstantRing V A)
          (proEtaleConstantRing Z A))
        (proEtaleConstantRingCompositeCoefficients_eq h k A).symm) ≪≫
      proEtaleCanonicalDerivedPullbackComparison h k
        (proEtaleConstantRing V A) (proEtaleConstantRing W A) (proEtaleConstantRing Z A)
        (proEtaleConstantRingComparison k A) (proEtaleConstantRingComparison h A) =
    Functor.mapDerivedCategoryNatIso
        (StrictTower.moduleGComp (ULift.{u + 1, u} A) h k) ≪≫
      Functor.mapDerivedCategoryCompIso
        (StrictTower.modulePullback (ULift.{u + 1, u} A) k)
        (StrictTower.modulePullback (ULift.{u + 1, u} A) h) := by
  have e := proEtaleCanonicalDerivedPullback_normalization h k
    (StrictTower.coefficients (ULift.{u + 1, u} A) V)
    (StrictTower.coefficients (ULift.{u + 1, u} A) W)
    (StrictTower.coefficients (ULift.{u + 1, u} A) Z)
    (StrictTower.constantRingIso (ULift.{u + 1, u} A) k)
    (StrictTower.constantRingIso (ULift.{u + 1, u} A) h)
    (StrictTower.constantRingIso (ULift.{u + 1, u} A) (h ≫ k))
    (StrictTower.constantRingIso_comp (ULift.{u + 1, u} A) h k).symm
    (StrictTower.moduleRComp (ULift.{u + 1, u} A) h k)
    (Classical.choose_spec
      (StrictTower.moduleRComp_existsUnique (ULift.{u + 1, u} A) h k)).1
  exact e

private theorem transportIso_paste {C : Type*} [Category C]
    {P P' Q Q' L R : C} (a : P ≅ L) (b : Q ≅ R)
    (e : P' = P) (e' : Q' = Q) (h : P = Q) (h' : P' = Q') :
    a.symm ≪≫ eqToIso h ≪≫ b =
      (eqToIso e ≪≫ a).symm ≪≫ eqToIso h' ≪≫ (eqToIso e' ≪≫ b) := by
  cases e
  cases e'
  have hh : h' = h := Subsingleton.elim _ _
  subst h'
  simp only [eqToIso_refl, Iso.refl_trans]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_transport
    {T V : Scheme.{u}} {f g : T ⟶ V} (e : f = g) (A : Type u) [CommRing A] :
    (Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (StrictTower.modulePullback (ULift.{u + 1, u} A)) e))).hom =
      (eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) e)).hom := by
  cases e
  exact Functor.mapDerivedCategoryNatIso_refl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem constantSquare_normalized
    (A : Type u) [CommRing A] {X' X Y' Y : Scheme.{u}}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare h f' f g) :
    ProEtale.directImageConstantPullbackIso A sq =
      Functor.mapDerivedCategorySquareIso
        (StrictTower.moduleSquareG (ULift.{u + 1, u} A) h f' f g sq.w) := by
  let c {V W Z : Scheme.{u}} (a : Z ⟶ W) (b : W ⟶ V) :=
    eqToIso (congrArg
      (proEtaleRingDerivedPullback (a ≫ b) (proEtaleConstantRing V A)
        (proEtaleConstantRing Z A))
      (proEtaleConstantRingCompositeCoefficients_eq a b A).symm) ≪≫
        proEtaleCanonicalDerivedPullbackComparison a b
          (proEtaleConstantRing V A) (proEtaleConstantRing W A) (proEtaleConstantRing Z A)
          (proEtaleConstantRingComparison b A) (proEtaleConstantRingComparison a A)
  have ht : ProEtale.directImageConstantPullbackIso A sq =
      (c f' g).symm ≪≫
        eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) sq.w.symm) ≪≫ c h f := by
    let ep := congrArg
      (proEtaleRingDerivedPullback (f' ≫ g) (proEtaleConstantRing Y A)
        (proEtaleConstantRing X' A))
      (proEtaleConstantRingCompositeCoefficients_eq f' g A).symm
    let eq := congrArg
      (proEtaleRingDerivedPullback (h ≫ f) (proEtaleConstantRing Y A)
        (proEtaleConstantRing X' A))
      (proEtaleConstantRingCompositeCoefficients_eq h f A).symm
    let ew := congrArg (proEtaleConstantRingDerivedPullback A) sq.w.symm
    unfold ProEtale.directImageConstantPullbackIso proEtaleAmbientRingedPullbackComparison
    dsimp only
    exact (Iso.trans_assoc _ _ _).trans (transportIso_paste
      (proEtaleCanonicalDerivedPullbackComparison f' g
        (proEtaleConstantRing Y A) (proEtaleConstantRing Y' A) (proEtaleConstantRing X' A)
        (proEtaleConstantRingComparison g A) (proEtaleConstantRingComparison f' A))
      (proEtaleCanonicalDerivedPullbackComparison h f
        (proEtaleConstantRing Y A) (proEtaleConstantRing X A) (proEtaleConstantRing X' A)
        (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison h A))
      ep eq (ep.symm.trans (ew.trans eq)) ew)
  rw [ht]
  dsimp only [c]
  rw [constantComp_normalized, constantComp_normalized]
  apply Iso.ext
  simp only [Functor.mapDerivedCategorySquareIso, StrictTower.moduleSquareG_eq,
    Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc]
  rw [derived_transport sq.w.symm A]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical tensor/inverse-image comparison respects the canonical comparison
around a geometric square, before taking any direct-image mates.
Source: Stacks Project, Tag 0D6D (`lemma-derived-pullback-composition`) and Tag 0E47
(`remark-compose-base-change-horizontal`), coefficient inverse-image comparison.
(blueprint: lem-sp-constant-scalar-pullback-cube).

Proof: first identify the ambient canonical geometric compositor with the exact
localization of StrictTower.moduleSquareG. The normalized derived-composition
characterization fixes each ordinary adjunction by its unit sections and the
ordinary direct-image compositor by restriction along Over.pullbackComp. The
coefficient transport equalities paste compatibly, by proof irrelevance.
The ordinary restriction comparison commutes with this square on sections.
Exact derived composition coherence transports that equality to the derived
restriction functors. Taking its scalar-adjunction mates gives the equality for
the inverse tensor comparisons, as proved by scalarTensorPullbackSquare.
The two required composites of isomorphisms therefore have equal inverses, and
hence equal forward maps. Extensionality in the input gives equality of natural
transformations. This uses no finiteness or flatness hypothesis and also applies
to empty schemes and zero coefficient rings. -/
theorem proEtaleConstantScalarPullback_cube
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X' X Y' Y : Scheme.{u}}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare h f' f g) :
    Functor.whiskerLeft (ProEtale.directImageScalarExtension φ Y)
        (ProEtale.directImageConstantPullbackIso B sq).hom ≫
      Functor.whiskerRight (ProEtale.directImageScalarPullbackIso φ f).hom
        (proEtaleConstantRingDerivedPullback B h) ≫
      Functor.whiskerLeft (proEtaleConstantRingDerivedPullback A f)
        (ProEtale.directImageScalarPullbackIso φ h).hom =
    Functor.whiskerRight (ProEtale.directImageScalarPullbackIso φ g).hom
        (proEtaleConstantRingDerivedPullback B f') ≫
      Functor.whiskerLeft (proEtaleConstantRingDerivedPullback A g)
        (ProEtale.directImageScalarPullbackIso φ f').hom ≫
      Functor.whiskerRight (ProEtale.directImageConstantPullbackIso A sq).hom
        (ProEtale.directImageScalarExtension φ X') := by
  apply NatTrans.ext
  funext N
  let la {V W : Scheme.{u}} (a : V ⟶ W) :=
    ProEtale.directImageScalarPullbackIso φ a
  let ta (R : Type u) [CommRing R] := ProEtale.directImageConstantPullbackIso R sq
  let L := (ta B).app ((ProEtale.directImageScalarExtension φ Y).obj N) ≪≫
    (proEtaleConstantRingDerivedPullback B h).mapIso ((la f).app N) ≪≫
    (la h).app ((proEtaleConstantRingDerivedPullback A f).obj N)
  let R := (proEtaleConstantRingDerivedPullback B f').mapIso ((la g).app N) ≪≫
    (la f').app ((proEtaleConstantRingDerivedPullback A g).obj N) ≪≫
    (ProEtale.directImageScalarExtension φ X').mapIso ((ta A).app N)
  have hi : L.inv = R.inv := by
    have e := DirectScalar.scalarTensorPullbackSquare φ h f' f g sq N
    dsimp only at e
    rw [← constantSquare_normalized A sq, ← constantSquare_normalized B sq] at e
    simpa only [L, R, la, ta, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
      Category.assoc] using e.symm
  exact (Iso.inv_eq_inv L R).mp hi

end AlgebraicGeometry.Scheme
