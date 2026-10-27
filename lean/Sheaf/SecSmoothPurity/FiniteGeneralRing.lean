/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurityDiagonalDualizingObject
public import Sheaf.SecSmoothPurity.ReductionExceptional
public import Sheaf.Paper.FiniteSmoothCoefficientArrows
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.Targets.VectorBundlePurity
public import Sheaf.SecSmoothPurity.FiniteGeneralRingData
import Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation
import Sheaf.SecSmoothPurity.FiniteGeneralRingTensorFormula
import Sheaf.SecSmoothPurity.FiniteGeneralRingExponent
import Sheaf.AlgebraicGeometry.CompactifiableOverField

/-! # Smooth purity over an arbitrary finite coefficient ring

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-thm-smooth-purity/sk-thm-smooth-purity-general-ring.md
(blueprint: det-sp-finite-general-ring).

All functors and arrows are the published canonical constructions. In particular,
the exceptional functor is the transported ordinary compact-support right adjoint,
and the direct orientation is normalized by the actual diagonal/Rees/integration equation.

## Main definitions

* `finiteGeneralRingReduction`: the canonical scalar/exceptional comparison at the unit.
* `finiteGeneralRingOrientationExtension`: scalar extension of the recorded orientation.
* `FiniteGeneralRingAt`: the three clauses and Kummer-normalized exponent independence.

## Main statements

* `finiteGeneralRingSmoothPurity`: smooth purity for every finite ell-primary ring.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

private def sourceInLine (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : Etale.FiniteSmoothPurity.proCategory A Y) :
    Etale.FiniteSmoothPurity.comparison A X ⋙
        (ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((Etale.FiniteSmoothPurity.proPullback A f).obj K) ⟶
      (Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((Etale.ordinaryFinitePullback A f).obj
            ((Etale.FiniteSmoothPurity.origin A Y).obj K)) ⋙
        Etale.FiniteSmoothPurity.comparison A X := by
  let : IsNoetherianRing A := isNoetherian_of_finite A A
  let : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar
  exact Functor.whiskerLeft (Etale.FiniteSmoothPurity.comparison A X)
      ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).map
        ((Etale.FiniteSmoothPurity.proPullback A f).map
            (Etale.FiniteSmoothPurity.originInverse A Y K) ≫
          (Etale.FiniteSmoothPurity.sitePullbackIso A f).hom.app
            ((Etale.FiniteSmoothPurity.origin A Y).obj K))) ≫
    (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A)
      ((Etale.ordinaryFinitePullback A f).obj
        ((Etale.FiniteSmoothPurity.origin A Y).obj K))).inv

private theorem sourceInLine_app (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : Etale.FiniteSmoothPurity.proCategory A Y)
    (L : Etale.DerivedCategoryModule A X) :
    (sourceInLine A f K).app L = Etale.FiniteSmoothPurity.sourceToOrigin A f L K := by
  let : IsNoetherianRing A := isNoetherian_of_finite A A
  let : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar
  simp only [sourceInLine, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.map_comp, NatTrans.comp_app, Etale.FiniteSmoothPurity.sourceToOrigin,
    Etale.FiniteSmoothPurity.proSource, Functor.comp_map,
    Etale.FiniteSmoothPurity.sourceAtOriginIso, Iso.trans_inv,
    Category.assoc]
  rfl

private theorem gammaInLine (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {L M : Etale.DerivedCategoryModule A X} (b : M ≅ L)
    (alpha : Etale.dualizingComplex (ModuleCat.{u + 1} A) f ≅ L)
    (K : Etale.FiniteSmoothPurity.proCategory A Y) :
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((Etale.FiniteSmoothPurity.proPullback A f).obj K)).map
          ((Etale.FiniteSmoothPurity.comparison A X).map b.hom) ≫
        Etale.FiniteSmoothPurity.proGamma A f L alpha K =
      Etale.FiniteSmoothPurity.sourceToOrigin A f M K ≫
        (Etale.FiniteSmoothPurity.comparison A X).map
          (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
              ((Etale.ordinaryFinitePullback A f).obj
                ((Etale.FiniteSmoothPurity.origin A Y).obj K))).map
                  (b.hom ≫ alpha.inv) ≫
            Etale.smoothTensorDualityMap (ModuleCat.{u + 1} A) f
              (Etale.isIso_projectionMap_of_finite A f)
              ((Etale.FiniteSmoothPurity.origin A Y).obj K)) := by
  have hn := (sourceInLine A f K).naturality b.hom
  rw [sourceInLine_app, sourceInLine_app] at hn
  dsimp only [Functor.comp_map] at hn
  simp only [Etale.FiniteSmoothPurity.proGamma, Etale.FiniteSmoothPurity.gamma,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]

private theorem gammaOrientationEquality (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {L L' M : Etale.DerivedCategoryModule A X} (b : M ≅ L) (b' : M ≅ L')
    (alpha : Etale.dualizingComplex (ModuleCat.{u + 1} A) f ≅ L)
    (alpha' : Etale.dualizingComplex (ModuleCat.{u + 1} A) f ≅ L')
    (h : alpha.hom ≫ b.inv = alpha'.hom ≫ b'.inv)
    (K : Etale.FiniteSmoothPurity.proCategory A Y) :
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((Etale.FiniteSmoothPurity.proPullback A f).obj K)).map
          ((Etale.FiniteSmoothPurity.comparison A X).map b.hom) ≫
        Etale.FiniteSmoothPurity.proGamma A f L alpha K =
      ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((Etale.FiniteSmoothPurity.proPullback A f).obj K)).map
          ((Etale.FiniteSmoothPurity.comparison A X).map b'.hom) ≫
        Etale.FiniteSmoothPurity.proGamma A f L' alpha' K := by
  have he : b.hom ≫ alpha.inv = b'.hom ≫ alpha'.inv := by
    have hi := congrArg Iso.inv (Iso.ext h : alpha ≪≫ b.symm = alpha' ≪≫ b'.symm)
    exact hi
  rw [gammaInLine, gammaInLine, he]

/-- Smooth purity for every finite commutative ring killed by a positive ell-power.
Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-thm-smooth-purity/sk-thm-smooth-purity-general-ring.md
(blueprint: det-sp-finite-general-ring).

Proof:
1. At the bottom finite subextension E=Q_ell, identify O_E/(varpi^n) with Z/ell^n.
   det-sp-scalar-extension-functor supplies real derived coefficient extension,
   preserving finite constructibility and Tor amplitude. Apply the canonical
   counit-transpose comparison of det-sp-reduction-exceptional at the coefficient
   unit. Its inverse followed by extension of diagonalDualizingObject, and the
   generator-normalized Tate comparison, gives theta in clause (1).
2. Pull back exceptional coefficient change along the diagonal. The coefficient
   comparison identifies the diagonal base-change arrows. On the actual Rees family,
   lem-pur-dnc-coefficient-transport identifies the unique t=1-normalized comparison,
   and hence its specialization at zero. Kummer-normalized projective-line traces
   commute with coefficient extension; ordered affine counits, followed by unique
   frame gluing, identify vector integration. The bundle arrow is the inverse of
   the integration adjunct of thm-amb-vector-bundle-purity. Thus the resulting
   orientation satisfies exactly OrientationNormalized over A. Comparison at the
   unit identifies this direct orientation with theta, proving clause (2).
3. Intrinsic Dctf objects have bounded ordinary-etale origins by finite comparison.
   thm-asd-smooth-tensor applies to arbitrary finite A. Its canonical inverse-PF and
   one-tensor-counit transpose, tensored with alpha inverse, is gamma. Transport it
   with the actual origin counit, tensorator and compact-support comparison, as in
   lem-pur-finite-ring-site-tensor-transpose. This is proGamma; it is invertible and
   natural on Dctf. sk-prop-sf-rf-shriek-preservation gives the Dctf target.
4. For any other positive annihilating exponent, pass to the common maximum. The
   Kummer power maps identify the Chern boundary classes. They therefore identify
   projective-line traces, ordered affine counits and their uniquely glued bundle
   integrations, including rank zero. The t=1 normalization then identifies both
   direct Rees orientations. Tensoring their inverse orientations with the same
   canonical tensor mate gives the displayed equality of the entire purity maps.
-/
theorem finiteGeneralRingSmoothPurity
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] (d : ℕ) [SmoothOfRelativeDimension d f]
    (n : ℕ) (hn : 1 ≤ n)
    (A : Type u) [CommRing A] [Finite A] (hA : ((ell ^ n : ℕ) : A) = 0) :
    ∃ (hX : IsNoetherian X) (hY : IsNoetherian Y) (hqc : QuasiCompact f),
      ∃ hc : HasCompactification f,
        FiniteGeneralRingAt (finiteGeneralRingPrimeSetting D ell hEll n hn) A
          hA d f (Y ↘ Spec (.of D.k)) hX hY hqc hc := by
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  let : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
  let hX : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of D.k))
  let hY : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of D.k))
  let hqc : QuasiCompact f := inferInstance
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have : LocallyOfFiniteType f := inferInstance
  let hc : HasCompactification f :=
    hasCompactification_of_finiteType_over_field D.k X Y f
  let P := finiteGeneralRingPrimeSetting D ell hEll n hn
  let hAU := congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA
  obtain ⟨e, t, alpha, geometry, hu, hr, heq, hnorm⟩ :=
    finiteGeneralRingOrientation D ell hEll f d n hn A hA
  let := hu
  let theta := (asIso (finiteGeneralRingDualizingUnitMap (ULift.{u + 1, u} A) f)).symm ≪≫
    (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} A) X).mapIso alpha
  refine ⟨hX, hY, hqc, hc, e, t, theta, alpha, geometry, hr, heq, hu, ?_, hnorm, ?_, ?_⟩
  · dsimp only [theta, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    exact IsIso.hom_inv_id_assoc _ _
  · apply finiteGeneralRingTensorFormula (ULift.{u + 1, u} A) (ell ^ n)
      (pow_pos (Fact.out : ell.Prime).pos n) hAU f d _ _ alpha
    intro y
    simpa only [map_natCast, P, WeilConjectures.PurityFiniteSetting.diagonalExponent,
      finiteGeneralRingPrimeSetting] using
      (P.diagonalExponent_isUnit (Y ↘ Spec (.of D.k))).map
        (Y.presheaf.germ ⊤ y trivial).hom
  · intro n' hn' hA'
    obtain ⟨hM, q, q', b, b', alpha', hb, hb', hnrm, he⟩ :=
      finiteGeneralRingExponent (ULift.{u + 1, u} A) ell n hn hAU d f geometry
        (fun m hm ↦ ({ P with level := m, level_pos := hm } :
          WeilConjectures.PurityFiniteSetting).diagonalExponent_isUnit
            (f ≫ (Y ↘ Spec (.of D.k)))) alpha hnorm n' hn' hA'
    refine ⟨hM, q, q', b, b', alpha', hb, hb', hnrm, he, ?_⟩
    intro K _hK
    exact gammaOrientationEquality (ULift.{u + 1, u} A) f
      (finiteGeneralRingLevelPower _ _ _ hM hAU X b d)
      (finiteGeneralRingLevelPower _ _ _ hM hA' X b' d) alpha alpha' he K

end AlgebraicGeometry.ProEtale
