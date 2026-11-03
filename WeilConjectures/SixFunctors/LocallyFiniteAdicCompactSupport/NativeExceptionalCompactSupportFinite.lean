/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData

import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportScalarMateInvertible
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationNaturalIso
import Mathlib.LinearAlgebra.TensorProduct.Tower
import all WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
import all Mathlib.Logic.Small.Defs
import all Mathlib.Algebra.Field.Shrink
import all Mathlib.Algebra.Algebra.Shrink

/-! # Finite coefficient comparisons for a specified exceptional system

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard Padic
  CategoryTheory.ScalarLocalization.category
  WeilConjectures.sfCompactSupportFiniteFunctor
  WeilConjectures.sfRationalConstructibleLocalization
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
set_option allowUnsafeReducibility true in
attribute [local irreducible] WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageSystem
attribute [local instance 2000] Shrink.instField Shrink.instAlgebra
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients

variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (source : Realization l X) (target : Realization l Y)
  (S : System.{u, 0} l (PadicAlgCl l) D hl (f := f)) (c : Compactification f)

set_option allowUnsafeReducibility true in
attribute [local reducible] ScalarLocalization.category
  sfCompactSupportFiniteFunctor sfRationalConstructibleLocalization in

/-- The preimage of an isomorphism under a fully faithful functor is invertible. -/
private theorem preimageIsIso
    {A B : Type*} [Category A] [Category B]
    (T : A ⥤ B) (ff : T.FullyFaithful) {K L : A}
    (m : T.obj K ⟶ T.obj L) (hm : IsIso m) : IsIso (ff.preimage m) := by
  let := hm
  exact (ff.preimageIso (asIso m)).isIso_hom

/-- Integral localization commutes with the prescribed pure-tensor compact-support action.
Source: the raw compact-support Hom formula
(blueprint: lem-sf-native-exceptional-compact-support-finite). -/
def systemIntegralLocalizationIso (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    sfRationalConstructibleLocalization l E X ⋙ sfCompactSupportFiniteFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E ≅
    sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E ⋙
        sfRationalConstructibleLocalization l E Y :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro K L h
    dsimp only [Functor.comp_map, Functor.comp_obj, sfCompactSupportFiniteFunctor,
      sfRationalConstructibleLocalization, ScalarLocalization.localization, Iso.refl_hom,
      ScalarLocalization.category]
    simp only [Category.comp_id, Category.id_comp]
    change sfCompactSupportFiniteHomMap l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E ⟨K⟩ ⟨L⟩
        ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l E))
          ⊗ₜ[Padic.coefficientExtensionIntegers l E] h) = _
    exact LinearMap.baseChange_tmul _ _ _)

/-- Restrict the desired square to one finite rational coefficient field.
Source: the specified common-stage inclusion and compact-support operation
(blueprint: lem-sf-native-exceptional-compact-support-finite). -/
abbrev systemFiniteSource (E : Index l (PadicAlgCl l)) :=
  GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙
    (S.ring.operation c .closed).F ⋙ target.J

/-- Restrict the native side to one finite rational coefficient field.
Source: Bhatt--Scholze, Proposition 6.8.14
(blueprint: lem-sf-native-exceptional-compact-support-finite). -/
abbrev systemFiniteTarget (E : Index l (PadicAlgCl l)) :=
  GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ source.J ⋙ actual l c

section SourceBoundary
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.Stage category Shrink.instField Shrink.instAlgebra
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5

/-- The prescribed finite rational operation agrees with the included closed operation.
Source: the supplied commonComparison and rationalLeft
(blueprint: lem-sf-native-exceptional-compact-support-finite). -/
def systemRationalSource (E : Index l (PadicAlgCl l)) :
    GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ (S.ring.operation c .closed).F ≅
      sfCompactSupportFiniteFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c
        (Coefficient.{u} l (PadicAlgCl l) E) ⋙
      GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := Y) E :=
  (S.common.commonComparison c E).q.symm ≪≫
    Functor.isoWhiskerRight (S.ring.rationalLeft c (commonField l (PadicAlgCl l) E))
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := Y) E)

attribute [local irreducible] systemRationalSource

/-- The integral source boundary of the normalized scalar square.
Source: rationalLeft, integral realization and completed compact-support realization
(blueprint: lem-sf-native-exceptional-compact-support-finite). -/
def systemIntegralSource [G : NativeGeometry.{u} l]
    (E : Index l (PadicAlgCl l)) :
    (sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
      systemFiniteSource l D hl target S c E) ⋙ (sections l Y).mapDerivedCategory ≅
    (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι ⋙
      PurCompactSupport.image (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)) c ⋙
          pbcDerivedExtend ((target.coefficient E).integralMap l Y) :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        (sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X)
        (Functor.isoWhiskerRight (systemRationalSource l D hl S c E) target.J))
      (sections l Y).mapDerivedCategory ≪≫
    Functor.isoWhiskerRight
      (systemIntegralLocalizationIso l D hl c (Coefficient.{u} l (PadicAlgCl l) E))
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := Y) E ⋙ target.J ⋙
        (sections l Y).mapDerivedCategory) ≪≫
    Functor.isoWhiskerLeft
      (sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c
        (Coefficient.{u} l (PadicAlgCl l) E)) (target.integral E) ≪≫
    Functor.isoWhiskerRight
      (sfQcqsCompactSupportRealization l (Coefficient.{u} l (PadicAlgCl l) E) D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c).symm
      (pbcDerivedExtend ((target.coefficient E).integralMap l Y))

end SourceBoundary

/-- The integral target boundary of the normalized scalar square.
Source: integral realization and the native section transport
(blueprint: lem-sf-native-exceptional-compact-support-finite). -/
def systemIntegralTarget [G : NativeGeometry.{u} l]
    (E : Index l (PadicAlgCl l)) :
    (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι ⋙
        pbcDerivedExtend ((source.coefficient E).integralMap l X) ⋙
          PurCompactSupport.image (nativeCoefficients l) c ≅
    (sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
      systemFiniteTarget l source c E) ⋙ (sections l Y).mapDerivedCategory :=
  Functor.isoWhiskerRight (source.integral E).symm
      (PurCompactSupport.image (nativeCoefficients l) c) ≪≫
    Functor.isoWhiskerLeft
      (sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ source.J)
      (operationTransport l c).symm

attribute [local irreducible] systemIntegralSource systemIntegralTarget
  systemIntegralLocalizationIso

/-- The section-level scalar composite with its two normalized boundary maps.
Source: Bhatt--Scholze, Remark 6.8.15
(blueprint: lem-sf-native-exceptional-compact-support-finite). -/
def systemSectionMap [G : NativeGeometry.{u} l]
    (E : Index l (PadicAlgCl l))
    (a : PurCompactSupport.Change (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (hs : a.map X = (source.coefficient E).integralMap l X)
    (ht : a.map Y = (target.coefficient E).integralMap l Y) :
    (sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
      systemFiniteSource l D hl target S c E) ⋙ (sections l Y).mapDerivedCategory ⟶
    (sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
      systemFiniteTarget l source c E) ⋙ (sections l Y).mapDerivedCategory :=
  let I := (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι
  let b := systemIntegralSource l D hl target S c E ≪≫
    Functor.isoWhiskerLeft
      (I ⋙ PurCompactSupport.image (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)) c)
      (eqToIso (congrArg pbcDerivedExtend ht.symm))
  let d := Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft I (eqToIso (congrArg pbcDerivedExtend hs)))
      (PurCompactSupport.image (nativeCoefficients l) c) ≪≫
    systemIntegralTarget l source c E
  b.hom ≫ Functor.whiskerLeft I (PurCompactSupport.comparison a c) ≫ d.hom

/-- The unique integral morphism whose section image is the proper/open scalar mate.
Source: Bhatt--Scholze, Remark 6.8.15; section equivalence is fully faithful
(blueprint: lem-sf-native-exceptional-compact-support-finite). -/
def systemIntegralMap [G : NativeGeometry.{u} l]
    (E : Index l (PadicAlgCl l))
    (a : PurCompactSupport.Change (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (hs : a.map X = (source.coefficient E).integralMap l X)
    (ht : a.map Y = (target.coefficient E).integralMap l Y) :
    sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        systemFiniteSource l D hl target S c E ⟶
      sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        systemFiniteTarget l source c E :=
  ((Functor.FullyFaithful.ofFullyFaithful
    (sections l Y).mapDerivedCategory).whiskeringRight _).preimage
      (systemSectionMap l D hl source target S c E a hs ht)

/-- The scalar map is invertible on the full integral constructible category.
Source: integral residue Tor and the invertible native compact-support scalar mate
(blueprint: lem-sf-native-exceptional-compact-support-finite).

Proof: residue Tor equips the unchanged underlying integral object with finite-Tor
bounds. The proper/open scalar mate is invertible on it. The two boundary maps are
isomorphisms, and the section equivalence reflects isomorphisms. -/
theorem systemSectionMap_isIso [G : NativeGeometry.{u} l]
    [∀ x : X, Invertible (l : X.residueField x)]
    (E : Index l (PadicAlgCl l))
    (a : PurCompactSupport.Change (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (ha : ∀ (T : Scheme.{u})
      (C : CoefficientPresentation l T (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)),
      a.map T = C.integralMap l T) :
    IsIso (systemSectionMap l D hl source target S c E a
      (ha X (source.coefficient E)) (ha Y (target.coefficient E))) := by
  let I := (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι
  let middle := Functor.whiskerLeft I (PurCompactSupport.comparison a c)
  let hm : IsIso middle := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun K ↦ ?_)
    let K' : finiteTorConstructibleIntegralCategory l
        (Coefficient.{u} l (PadicAlgCl l) E) X :=
      ⟨K.obj, by
        rw [← (integral_residue_tor D l hl (Coefficient.{u} l (PadicAlgCl l) E) X).2]
        exact K.property⟩
    exact native_compact_support_scalar_mate_invertible l D hl c E a ha K'
  let b := systemIntegralSource l D hl target S c E ≪≫
    Functor.isoWhiskerLeft
      (I ⋙ PurCompactSupport.image (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)) c)
      (eqToIso (congrArg pbcDerivedExtend (ha Y (target.coefficient E)).symm))
  let d := Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft I
        (eqToIso (congrArg pbcDerivedExtend (ha X (source.coefficient E)))))
      (PurCompactSupport.image (nativeCoefficients l) c) ≪≫
    systemIntegralTarget l source c E
  change IsIso (b.hom ≫ middle ≫ d.hom)
  exact (b ≪≫ ((@asIso _ _ _ _ middle hm) ≪≫ d)).isIso_hom

/-- The integral scalar map is invertible by fully faithful lifting of its section map.
Source: native section equivalence and integral residue Tor
(blueprint: lem-sf-native-exceptional-compact-support-finite). -/
theorem systemIntegralMap_isIso [G : NativeGeometry.{u} l]
    [∀ x : X, Invertible (l : X.residueField x)]
    (E : Index l (PadicAlgCl l))
    (a : PurCompactSupport.Change (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (ha : ∀ (T : Scheme.{u})
      (C : CoefficientPresentation l T (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)),
      a.map T = C.integralMap l T) :
    IsIso (systemIntegralMap l D hl source target S c E a
      (ha X (source.coefficient E)) (ha Y (target.coefficient E))) := by
  let n := systemSectionMap l D hl source target S c E a
    (ha X (source.coefficient E)) (ha Y (target.coefficient E))
  exact preimageIsIso _
    ((Functor.FullyFaithful.ofFullyFaithful
      (sections l Y).mapDerivedCategory).whiskeringRight _) n
    (systemSectionMap_isIso l D hl source target S c E a ha)

/-- The normalized integral scalar comparison extends uniquely to rational arrows.
Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15; categorical localization
(blueprint: lem-sf-native-exceptional-compact-support-finite).

Proof: the integral scalar map is invertible by the preceding residue-Tor argument.
Raw scalar localization is categorical localization at uniformizer powers, so fully
faithful precomposition extends this natural isomorphism uniquely. Its component
formula retains the specified integral scalar map. -/
theorem systemFiniteComparison [G : NativeGeometry.{u} l]
    [∀ x : X, Invertible (l : X.residueField x)]
    (E : Index l (PadicAlgCl l))
    (a : PurCompactSupport.Change (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (ha : ∀ (T : Scheme.{u})
      (C : CoefficientPresentation l T (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)),
      a.map T = C.integralMap l T) :
    ∃! alpha : systemFiniteSource l D hl target S c E ≅ systemFiniteTarget l source c E,
      ∀ K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X,
        alpha.hom.app ((sfRationalConstructibleLocalization l
          (Coefficient.{u} l (PadicAlgCl l) E) X).obj K) =
        (systemIntegralMap l D hl source target S c E a
          (ha X (source.coefficient E)) (ha Y (target.coefficient E))).app K := by
  let := systemIntegralMap_isIso l D hl source target S c E a ha
  exact @ScalarLocalization.naturalIso_of_integral
    (Padic.coefficientExtensionIntegers l (Coefficient.{u} l (PadicAlgCl l) E)) _
    (sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X)
    _ _ _ _ _ (fun n ↦ inferInstance) _ _
    (fun n ↦ sfIntegralConstructibleShift_linear l
      (Coefficient.{u} l (PadicAlgCl l) E) X n)
    (Padic.coefficientExtensionUniformizer l (Coefficient.{u} l (PadicAlgCl l) E)) _ _
    (systemFiniteSource l D hl target S c E) (systemFiniteTarget l source c E)
    (asIso (systemIntegralMap l D hl source target S c E a
      (ha X (source.coefficient E)) (ha Y (target.coefficient E))))

attribute [local irreducible] systemSectionMap

set_option allowUnsafeReducibility true in
attribute [local reducible] sfRationalConstructibleLocalization in
end WeilConjectures.LocallyFiniteAdicCompactSupport
