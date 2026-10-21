/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
public import Sheaf.AlgebraicGeometry.BirationalQuasiModification
public import Sheaf.TraceFormula.Modification
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.FieldTheory.IsSepClosed

import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import Sheaf.TraceFormula.FlatDenseGenericFibrePureDimension
import Sheaf.TraceFormula.FlatFiniteTypeDensePresentation
import Sheaf.AlgebraicGeometry.ProperBirationalNormalCurveIso
import WeilConjectures.RingTheory.SmoothNormalRing

/-!
# Horizontal curve models over finite-height valuation rings

Source: Temkin, *Stable modification of relative curves*, Remark 4.1,
the opening of §4.2, and Lemma 3.5.1
(blueprint: lem-trf-valuation-horizontal-curve-models).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A valuation domain with separably closed fraction field and finite prime chain.
Source: Temkin, §4 opening conventions
(blueprint: lem-trf-valuation-horizontal-curve-models). -/
structure HorizontalValuationBase where
  V : Type u
  K : Type u
  commRingV : CommRing V
  isDomainV : IsDomain V
  valuationV : ValuationRing V
  fieldK : Field K
  algebraVK : Algebra V K
  fractionVK : IsFractionRing V K
  sepClosedK : IsSepClosed K
  finitePrime : Finite (PrimeSpectrum V)
  primeChain : ∀ p q : PrimeSpectrum V, p ≤ q ∨ q ≤ p

attribute [instance] HorizontalValuationBase.commRingV HorizontalValuationBase.isDomainV
  HorizontalValuationBase.valuationV HorizontalValuationBase.fieldK
  HorizontalValuationBase.algebraVK HorizontalValuationBase.fractionVK
  HorizontalValuationBase.sepClosedK HorizontalValuationBase.finitePrime

/-- The valuation scheme. Source: Temkin, §4
(blueprint: lem-trf-valuation-horizontal-curve-models). -/
abbrev HorizontalValuationBase.T (B : HorizontalValuationBase.{u}) : Scheme.{u} :=
  Spec (.of B.V)

/-- The actual generic-point morphism from the specified fraction field.
Source: Temkin, §4 (blueprint: lem-trf-valuation-horizontal-curve-models). -/
def HorizontalValuationBase.genericMap (B : HorizontalValuationBase.{u}) :
    Spec (.of B.K) ⟶ B.T :=
  Spec.map (CommRingCat.ofHom (algebraMap B.V B.K))

/-- A flat finitely presented relative curve, with no separatedness assumption.
Finite presentation includes quasi-compactness and quasi-separatedness.
Source: Temkin, §1.2 (blueprint: lem-trf-valuation-horizontal-curve-models). -/
structure RelativeCurve {T Y : Scheme.{u}} (y : Y ⟶ T) : Prop where
  flat : Flat y
  finitelyPresented : LocallyOfFinitePresentation y
  quasiCompact : QuasiCompact y
  quasiSeparated : QuasiSeparated y
  pure : ∀ t : T, (y.fiber t).IsPureDimension 1

/-- The canonical generic base change of the given map, constructed in the slice category.
Source: Temkin, Remark 4.1 and §4.2
(blueprint: lem-trf-valuation-horizontal-curve-models). -/
def horizontalGenericCurveMap {T S Y : Scheme.{u}} (P : MultipointedCurve T)
    (η : S ⟶ T) (q : Y ⟶ P.X) :
    pullback (q ≫ P.x) η ⟶ pullback P.x η :=
  ((Over.pullback η).map (Over.homMk q rfl : Over.mk (q ≫ P.x) ⟶ Over.mk P.x)).left

/-- The inverse image of the generic marking, hence its intersection with the generic open
when the generic curve map is an open immersion. This is a specified closed subscheme.
Source: Temkin, Remark 4.1 and §4.2
(blueprint: lem-trf-valuation-horizontal-curve-models). -/
def horizontalGenericMarkingι {T S Y : Scheme.{u}} (P : MultipointedCurve T)
    (η : S ⟶ T) (q : Y ⟶ P.X) :
    pullback (horizontalGenericCurveMap P η q) (P.markingBaseChange η) ⟶
      pullback (q ≫ P.x) η :=
  pullback.fst _ _

/-- The flat schematic closure of the specified embedded generic subscheme.
The kernel is Mathlib's quasi-coherent ideal sheaf of the scheme-theoretic image;
on affine charts it is the kernel of restriction to the generic marking quotient.
The prescribed fibre compares ideals in the ambient generic fibre,
not abstract isomorphism types.
Source: Temkin, Lemma 3.5.1 and Remark 4.1
(blueprint: lem-trf-valuation-horizontal-curve-models). -/
structure FlatClosure {T S Y Z E : Scheme.{u}} (y : Y ⟶ T) (η : S ⟶ T)
    (j : Z ⟶ pullback y η) (e : E ⟶ Y) : Prop where
  closed : IsClosedImmersion e
  closureIdeal : e.ker = (j ≫ pullback.fst y η).ker
  flat : Flat (e ≫ y)
  finitelyPresented : LocallyOfFinitePresentation (e ≫ y)
  quasiCompact : QuasiCompact (e ≫ y)
  quasiSeparated : QuasiSeparated (e ≫ y)
  pureZero : ∀ t : T, (e ≫ y).fiber t |>.IsPureDimension 0
  prescribedGenericFibre : e.ker.comap (pullback.fst y η) = j.ker

/-- Closure commutes with quasi-compact open restriction: the restricted ideal is the
scheme-theoretic image ideal of the restricted generic marking. The restricted marking
also remains flat, finitely presented and pure zero-dimensional over the base.
Source: Temkin, Remark 4.1, affine kernel localization
(blueprint: lem-trf-valuation-horizontal-curve-models). -/
def ClosureRestrictionStable {T Y Z E : Scheme.{u}} (y : Y ⟶ T)
    (m : Z ⟶ Y) (e : E ⟶ Y) : Prop :=
  ∀ U : Y.Opens, QuasiCompact U.ι →
    e.ker.comap U.ι = (pullback.snd m U.ι).ker ∧
      Flat ((e ∣_ U) ≫ U.ι ≫ y) ∧
      LocallyOfFinitePresentation ((e ∣_ U) ≫ U.ι ≫ y) ∧
      QuasiCompact ((e ∣_ U) ≫ U.ι ≫ y) ∧
      QuasiSeparated ((e ∣_ U) ≫ U.ι ≫ y) ∧
      (∀ t : T, (((e ∣_ U) ≫ U.ι ≫ y).fiber t).IsPureDimension 0)

/-- The multipointed curve supplied by the curve and flat-closure conclusions.
All its data are the given schemes and maps.
Source: Temkin, Remark 4.1 (blueprint: lem-trf-valuation-horizontal-curve-models). -/
def horizontalClosurePair {T S Y Z E : Scheme.{u}} (y : Y ⟶ T) (η : S ⟶ T)
    (j : Z ⟶ pullback y η) (e : E ⟶ Y) (hy : RelativeCurve y)
    (he : FlatClosure y η j e) : MultipointedCurve T where
  X := Y
  D := E
  x := y
  d := e ≫ y
  i := e
  comm := rfl
  flat_X := hy.flat
  lfp_X := hy.finitelyPresented
  qc_X := hy.quasiCompact
  qs_X := hy.quasiSeparated
  pure_X := hy.pure
  flat_D := he.flat
  lfp_D := he.finitelyPresented
  qc_D := he.quasiCompact
  qs_D := he.quasiSeparated
  pure_D := he.pureZero
  closed := he.closed

/-- The compatible pair morphism from the closure pair, using the existing pair interface.
Source: Temkin, Remark 4.1 (blueprint: lem-trf-valuation-horizontal-curve-models). -/
def horizontalClosurePairMap {T S Y E : Scheme.{u}} (P : MultipointedCurve T)
    (η : S ⟶ T) (q : Y ⟶ P.X) (e : E ⟶ Y)
    (hy : RelativeCurve (q ≫ P.x))
    (he : FlatClosure (q ≫ P.x) η (horizontalGenericMarkingι P η q) e)
    (r : E ⟶ P.D) (hr : r ≫ P.d = e ≫ q ≫ P.x)
    (hi : r ≫ P.i = e ≫ q) :
    (horizontalClosurePair (q ≫ P.x) η (horizontalGenericMarkingι P η q) e hy he).Hom P where
  curve := q
  marking := r
  curve_over := rfl
  marking_over := hr
  comm := hi

/-- Horizontal models and closures of their actual generic markings.
Source: Temkin, Remark 4.1, opening §4.2, and Lemma 3.5.1
(blueprint: lem-trf-valuation-horizontal-curve-models).

Proof: (1) flatness embeds affine coordinate rings into their generic localizations;
smoothness makes those reduced, and finite presentation gives finite generic components.
(2) For a reduced proper modification, schematic density meets every generic point.
Proper birational maps to the normal smooth generic curve are isomorphisms. Reducedness
then gives torsion-freeness over the valuation ring and hence flatness. The finite-type
dense-presentation criterion gives finite presentation, and the dense generic fibre
pure-dimension lemma gives pure relative dimension one. (3) On each affine chart take the
kernel of restriction to the generic marking quotient. The quotient is torsion-free,
hence flat, and the dense-presentation criterion gives finite presentation. Its dense
zero-dimensional generic fibre gives pure relative dimension zero. Pullback of the ideal
of D vanishes generically, hence vanishes by flatness, giving the proper marking map and
the eta-modification pair. (4) For any other flat closed subscheme with the same embedded
generic fibre, torsion-freeness makes its ideal the same kernel, proving uniqueness over Y.
(5) Localization is exact, so restriction of this kernel is the closure kernel on each
quasi-compact open. (6) For a birational quasi-modification use the inverse image of the
generic marking in its generic open and repeat the kernel, flatness, finite presentation,
pure-dimension and localization arguments. Empty markings give empty closures throughout.
-/
theorem horizontal_curve_models (B : HorizontalValuationBase.{u})
    (P : MultipointedCurve B.T)
    (hSmooth : Smooth (pullback.snd P.x B.genericMap))
    (hEtale : Etale (pullback.snd P.d B.genericMap)) :
    ∃ hX : IsReduced P.X,
      Finite (irreducibleComponents P.X) ∧
      (∀ {Y : Scheme.{u}} (q : Y ⟶ P.X), IsReduced Y → SchemeModification q →
        IsIso (horizontalGenericCurveMap P B.genericMap q) ∧
        ∃ (hy : RelativeCurve (q ≫ P.x)) (E : Scheme.{u}) (e : E ⟶ Y)
          (he : FlatClosure (q ≫ P.x) B.genericMap
            (horizontalGenericMarkingι P B.genericMap q) e)
          (r : E ⟶ P.D) (hr : r ≫ P.d = e ≫ q ≫ P.x)
          (hi : r ≫ P.i = e ≫ q),
          (∀ (F : Scheme.{u}) (f : F ⟶ Y),
            IsClosedImmersion f → Flat (f ≫ q ≫ P.x) →
              f.ker.comap (pullback.fst (q ≫ P.x) B.genericMap) =
                (horizontalGenericMarkingι P B.genericMap q).ker →
              ∃ h : F ≅ E, h.hom ≫ e = f) ∧
          (horizontalClosurePairMap P B.genericMap q e hy he r hr hi).IsEtaModification
            B.genericMap ∧
          ClosureRestrictionStable (q ≫ P.x)
            (horizontalGenericMarkingι P B.genericMap q ≫ pullback.fst (q ≫ P.x) B.genericMap)
            e) ∧
      (∀ {Y : Scheme.{u}} (q : Y ⟶ P.X) (hY : IsIntegral Y),
        RelativeCurve (q ≫ P.x) →
        @IsBirationalQuasiModification Y P.X hY hX q →
        IsOpenImmersion (horizontalGenericCurveMap P B.genericMap q) →
        ∃ (E : Scheme.{u}) (e : E ⟶ Y),
          FlatClosure (q ≫ P.x) B.genericMap
            (horizontalGenericMarkingι P B.genericMap q) e ∧
          ClosureRestrictionStable (q ≫ P.x)
            (horizontalGenericMarkingι P B.genericMap q ≫ pullback.fst (q ≫ P.x) B.genericMap)
            e) := by
  sorry

end AlgebraicGeometry
