/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.ClassicalRawLisseRealizationData
public import Sheaf.Paper.IntegralPullbackCompletedComparison

/-! # Coherent operations on classical raw lisse realizations

Source: BS 6.8.4, 6.8.14, 6.8.15
(blueprint: def-zl-classical-raw-lisse-point-fibres).
## Main definitions

* Comparison data using the recorded classical realization and actual fibre maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async true
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped TensorProduct
namespace WeilConjectures.ClassicalRawLisse
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (W : PerAdic.Base D.k)

variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Fibres of an arbitrary heart object identified on a locally closed stratum.
The comparison is the completed pullback followed by the specified raw identification.
Source: BS Remark 6.8.15
(blueprint: def-zl-classical-raw-lisse-point-fibres). -/
structure RestrictedFibres (a : LisseRealization.Family D l hl)
    (b : ContinuousRational.Family.{u} l) (s : Family D l hl a b)
    (V : PerAdic.Base D.k) (f : V.scheme ⟶ W.scheme) [IsImmersion f] where
  completed (x : Spec (.of D.k) ⟶ V.scheme) :
    @rationalDerivedPullback l _ E _ _ _ V.scheme W.scheme f
        (baseInvertible D l hl V) (baseInvertible D l hl W) ⋙
      sfAdicRationalFiber l E V.scheme x ≅ sfAdicRationalFiber l E W.scheme (x ≫ f)
  identified (x : Spec (.of D.k) ⟶ V.scheme)
      (N : sfRationalHeart l E W.scheme) (M : Rational D l E V)
      (e : (@rationalDerivedPullback l _ E _ _ _ V.scheme W.scheme f
        (baseInvertible D l hl V) (baseInvertible D l hl W)).obj N.obj ≅
          ((s.raw E V).raw.obj M).obj) :
    (sfAdicRationalFiber l E W.scheme (x ≫ f)).obj N.obj ≅
      classicalFibre D l E V M.obj x
  normalization (x : Spec (.of D.k) ⟶ V.scheme)
      (N : sfRationalHeart l E W.scheme) (M : Rational D l E V)
      (e : (@rationalDerivedPullback l _ E _ _ _ V.scheme W.scheme f
        (baseInvertible D l hl V) (baseInvertible D l hl W)).obj N.obj ≅
          ((s.raw E V).raw.obj M).obj) :
    (identified x N M e).hom = (completed x).inv.app N.obj ≫
      (sfAdicRationalFiber l E V.scheme x).map e.hom ≫ ((s.finite E V).fibre x M).hom

/-- The actual map of the lifted etale points, on pointed neighbourhoods precomposing
with h. This is the classical restriction/coprojection operation on germs.
Source: Stacks 03PN, BS 6.8.15
(blueprint: def-zl-classical-raw-lisse-point-fibres). -/
def pointReparam (x : Spec (.of D.k) ⟶ W.scheme)
    (h : Spec (.of D.k) ⟶ Spec (.of D.k)) :
    (pointSmallEtale (h ≫ x)).ulift.{u + 1} ⟶ (pointSmallEtale x).ulift.{u + 1} :=
  ⟨Functor.whiskerRight (pointSmallEtalePrecomp x h).hom uliftFunctor.{u + 1, u}⟩

/-- Classical point transport is the inverse-limit map of the actual germ maps,
followed by ordinary localization. Its definition includes every finite iterate of h.
Source: Weil II (1.1.1)b,c, BS Remark 6.8.15
(blueprint: def-zl-classical-raw-lisse-point-fibres). -/
def classicalTransport (M : Systems D l E W) (x : Spec (.of D.k) ⟶ W.scheme)
    (h : Spec (.of D.k) ⟶ Spec (.of D.k)) :
    classicalFibre D l E W M x ⟶ classicalFibre D l E W M (h ≫ x) :=
  (ModuleCat.extendScalars.{u, u, u + 1} (Padic.coefficientExtensionIntegers l E).subtype).map
    (limMap (Functor.whiskerLeft M.obj.obj
      ((pointReparam D W x h).sheafFiber
        (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)))))

/-- Rational point sections after the normalized coefficient restriction. The iso
is pinned on every pure tensor by the identity on the underlying sections.
Source: BS 6.8.14(2) (blueprint: def-zl-classical-raw-lisse-point-fibres). -/
structure PointSectionsTransport where
  comparison : PerAdic.pointSections l E D.k ⋙
      ModuleCat.extendScalars (PerAdic.integerToField l E) ≅
    purOrdinaryCoefficientModel l E (Spec (.of D.k)) ⋙
      pointCompletedSections D.k l E ⋙ pointModuleRationalization l E
  sectionMap (M : pbcModules (Spec (.of D.k))
      (pbcAdicCompletion (Spec (.of D.k)) (pbcIntegralDatum l E))) :
    (PerAdic.pointSections l E D.k).obj M →
      (pointCompletedSections D.k l E).obj
        ((purOrdinaryCoefficientModel l E (Spec (.of D.k))).obj M)
  section_identity (M : pbcModules (Spec (.of D.k))
      (pbcAdicCompletion (Spec (.of D.k)) (pbcIntegralDatum l E)))
      (m : (PerAdic.pointSections l E D.k).obj M) : HEq (sectionMap M m) m
  tensor (M : pbcModules (Spec (.of D.k))
      (pbcAdicCompletion (Spec (.of D.k)) (pbcIntegralDatum l E)))
      (c : E) (m : (PerAdic.pointSections l E D.k).obj M) :
    HEq (comparison.hom.app M (c ⊗ₜ[PbcIntegralRing l E] m))
      (c ⊗ₜ[Padic.coefficientExtensionIntegers l E]
        (sectionMap M m))

/-- Exact H0/sections comparison, including the identity-on-sections coefficient
restriction and both canonical exact-functor homology comparisons.
Source: BS 6.8.14(2) (blueprint: def-zl-classical-raw-lisse-point-fibres). -/
def pointSectionsH0 (t : PointSectionsTransport D l E)
    (K : PbcCompletedDerived (Spec (.of D.k)) (pbcIntegralDatum l E)) :=
  t.comparison.hom.app ((DerivedCategory.homologyFunctor _ 0).obj K) ≫
    (pointModuleRationalization l E).map
      ((pointCompletedSections D.k l E).map
        ((purOrdinaryCoefficientModel l E (Spec (.of D.k))).mapDerivedCategoryHomologyFunctorIso
          0 |>.hom.app K)) ≫
    (pointModuleRationalization l E).map
      (((pointCompletedSections D.k l E).mapDerivedCategoryHomologyFunctorIso 0).hom.app
        ((purCoefficientModel l E (Spec (.of D.k))).functor.obj K)) ≫
    ((pointModuleRationalization l E).mapDerivedCategoryHomologyFunctorIso 0).hom.app
      ((pointCompletedDerivedSections D.k l E).obj
        ((purCoefficientModel l E (Spec (.of D.k))).functor.obj K))

/-- The ordinary fibre square for every point automorphism and every finite iterate.
The right-hand map is literally restriction then the inverse-image coprojection;
the compositor has the prescribed pulled-back tensor-unit normalization.
Source: BS Remark 6.8.15 (blueprint: def-zl-classical-raw-lisse-point-fibres). -/
structure PointComparison (a : LisseRealization.Family D l hl)
    (b : ContinuousRational.Family.{u} l) (s : Family D l hl a b) where
  sections : PointSectionsTransport D l E
  pullback (x : Spec (.of D.k) ⟶ W.scheme) :
    IntegralCompletedComparison.Comparison l E x
  complete (M : Rational D l E W) :
    IntegralCompletedComparison.Complete l E
      ((purCoefficientModel l E W.scheme).inverse.obj
        ((s.raw E W).integral.obj M.obj).obj)
  completed (x : Spec (.of D.k) ⟶ W.scheme) (M : Rational D l E W) :
    (purCoefficientModel l E (Spec (.of D.k))).functor.obj
      ((pbcActualCompletedPull x (pbcIntegralDatum l E)).obj
        ((purCoefficientModel l E W.scheme).inverse.obj
          ((s.raw E W).integral.obj M.obj).obj)) ⟶
      (integralDerivedPullback l E x).obj
        ((purCoefficientModel l E W.scheme).functor.obj
          ((purCoefficientModel l E W.scheme).inverse.obj
            ((s.raw E W).integral.obj M.obj).obj))
  completed_normalization (x : Spec (.of D.k) ⟶ W.scheme) (M : Rational D l E W) :
    HEq (completed x M)
      ((pullback x).gamma
        ((purCoefficientModel l E W.scheme).inverse.obj
          ((s.raw E W).integral.obj M.obj).obj) (complete M)).inv
  comparison (x : Spec (.of D.k) ⟶ W.scheme) (M : Rational D l E W) :
    classicalFibre D l E W M.obj x ≅
      (LisseRealization.sections D l hl E).obj
        ((LisseRealization.ordinaryPull l E x).obj ((s.finite E W).modules.obj M))
  intrinsic (x : Spec (.of D.k) ⟶ W.scheme) (M : Rational D l E W) :
    (sfAdicRationalFiber l E W.scheme x).obj ((s.raw E W).raw.obj M).obj ≅
      (LisseRealization.fibre D l hl E).obj
        ((LisseRealization.pull D l hl E
          (X := LisseRealization.point D l hl)
          (Y := realizationBase D l hl W) x).obj ((s.raw E W).raw.obj M).obj)
  intrinsic_normalization (x : Spec (.of D.k) ⟶ W.scheme) (M : Rational D l E W) :
    HEq ((intrinsic x M).hom ≫
      (LisseRealization.fibreNormalization D l hl E
        ((LisseRealization.pull D l hl E
          (X := LisseRealization.point D l hl)
          (Y := realizationBase D l hl W) x).obj ((s.raw E W).raw.obj M).obj)).hom)
      (pointSectionsH0 D l E sections
        ((pbcActualCompletedPull x (pbcIntegralDatum l E)).obj
          ((purCoefficientModel l E W.scheme).inverse.obj
            ((s.raw E W).integral.obj M.obj).obj)) ≫
        (DerivedCategory.homologyFunctor _ 0).map
          ((pointModuleDerivedRationalization l E).map
            ((pointCompletedDerivedSections D.k l E).map
              (completed x M ≫ (integralDerivedPullback l E x).map
                ((purCoefficientModel l E W.scheme).counitIso.hom.app
                  ((s.raw E W).integral.obj M.obj).obj)))))
  normalization (x : Spec (.of D.k) ⟶ W.scheme) (M : Rational D l E W) :
    ((s.finite E W).fibre x M).hom ≫ (comparison x M).hom =
      (intrinsic x M).hom ≫
        (a.point E).comparison.hom.app
          ⟨(LisseRealization.pull D l hl E
            (X := LisseRealization.point D l hl)
            (Y := realizationBase D l hl W) x).obj ((s.raw E W).raw.obj M).obj,
            (a.along E (X := LisseRealization.point D l hl)
              (Y := realizationBase D l hl W) x).preserves
                ((s.raw E W).raw.obj M).obj ((s.finite E W).lisse M)⟩ ≫
        (LisseRealization.sections D l hl E).map
          ((a.along E (X := LisseRealization.point D l hl)
            (Y := realizationBase D l hl W) x).comparison
              ((s.raw E W).raw.obj M).obj ((s.finite E W).lisse M)).hom ≫
        (LisseRealization.sections D l hl E).map
          ((LisseRealization.ordinaryPull l E x).map
            ((s.finite E W).comparison.hom.app M))
  natural (x : Spec (.of D.k) ⟶ W.scheme) (M N : Rational D l E W) (g : M ⟶ N) :
    ((s.finite E W).fibre x M).inv ≫
        (sfAdicRationalFiber l E W.scheme x).map ((s.raw E W).raw.map g).hom ≫
        ((s.finite E W).fibre x N).hom ≫ (comparison x N).hom =
      (comparison x M).hom ≫ (LisseRealization.sections D l hl E).map
        ((LisseRealization.ordinaryPull l E x).map ((s.finite E W).modules.map g))
  transport (x : Spec (.of D.k) ⟶ W.scheme)
      (h : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso h]
      (M : Rational D l E W) (z : classicalFibre D l E W M.obj x) :
    (comparison (h ≫ x) M).hom (classicalTransport D l E W M.obj x h z) =
      (LisseRealization.sections D l hl E).map
        ((a.composition E (X := LisseRealization.point D l hl)
          (Y := realizationBase D l hl W) (Z := LisseRealization.point D l hl) x h).ordinary.inv.app
          ((s.finite E W).modules.obj M))
        (LisseRealization.ordinaryPointTransport D l hl E h
          ((LisseRealization.ordinaryPull l E x).obj ((s.finite E W).modules.obj M))
          ((comparison x M).hom z))

end WeilConjectures.ClassicalRawLisse
