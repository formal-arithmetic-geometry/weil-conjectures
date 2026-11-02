/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CondensedTwConventions.CondensedTwConventions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedGeometricFrobeniusTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk

/-! # Geometric Frobenius on condensed constant cohomology

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/
sk-thm-sf-tensor-hom/sk-rem-sf-pf-done/def-tw-frobenius-action.md
(blueprint: def-tw-frobenius-action).

The scheme map is the geometric Galois Frobenius of the finite-field model.
Both operators are point insertion, canonical exchange, and the coefficient-unit map,
in that order. Compact exchange uses its normalized proper-refinement comparison.
The last definition applies integer homology to these specified automorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096


universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedTwConventions

open CondensedRing
namespace FrobeniusAction

variable (T : CondensedTwConventions.{u})

/-- The published geometric Frobenius square of the specified finite-field model.
It includes the actual projection equality, without a postponed square proof.
Source: latest blueprint, geometric Frobenius and construction step 1
(blueprint: def-tw-frobenius-action). -/
abbrev geometry := CohomologyTransport.geometricFrobeniusGeometry T.datum T.X

/-- Geometric Frobenius of the specified finite-field model, on its actual geometric fibre.
Source: latest blueprint, first sentence (blueprint: def-tw-frobenius-action). -/
abbrev schemeAut : Aut T.geometricBaseChange.left := (geometry T).h

/-- Geometric Frobenius on the coefficient base point, using the same field automorphism.
Source: latest blueprint, base-change convention (blueprint: def-tw-frobenius-action). -/
abbrev pointAut := (geometry T).b

/-- The canonical coefficient-unit identification, derived from multiplication on the
regular module. No Weil structure is supplied as an extra parameter.
Source: latest blueprint, induced constant-coefficient action, construction step 2
(blueprint: def-tw-frobenius-action). -/
def coefficientIso :
    (CohomologyTransport.L (Profinite.padicAlgClRingObj T.ell) (schemeAut T).hom).obj
        T.coefficientObject ≅ T.coefficientObject :=
  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
    (Profinite.padicAlgClRingObj T.ell) (schemeAut T).hom).app _ ≪≫
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj T.ell)
      (schemeAut T).hom).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (upperStarObjRegularIso _ (schemeAut T).hom)

/-- Point insertion along geometric Frobenius, transported by the canonical point
coefficient comparison, and then evaluated by exactly the dependency's `Fib_s`.
Source: latest blueprint, cohomology transport, construction step 3
(blueprint: def-tw-frobenius-action). -/
def pointInsertion :
    T.pointFiber ≅
      CohomologyTransport.L (Profinite.padicAlgClRingObj T.ell) (pointAut T).hom ⋙
        T.pointFiber :=
  (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight
    ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
      (Profinite.padicAlgClRingObj T.ell) (pointAut T).hom ≪≫
      Functor.mapDerivedCategoryNatIso
        (CondensedRing.upperStarIsoIdOfIsSepClosed
          (Profinite.padicAlgClRingObj T.ell) (pointAut T).hom) ≪≫
      Functor.mapDerivedCategoryIdIso _).symm) _

/-- Normalized compact exchange for this geometric Frobenius square. The data's
`exchange_normalization` identifies exchange with `squareExchange` followed by
`targetCompare`, whose refinement and cocycle laws fix the comparison.
Source: latest blueprint, compact-support action, construction step 3
(blueprint: def-tw-frobenius-action). -/
def compactData : CohomologyTransport.FrobeniusTransportData
    (Profinite.padicAlgClRingObj T.ell) (geometry T) :=
  (CohomologyTransport.geometricFrobeniusCohomologyTransport T.datum T.X T.ell
    T.different (⟨⊥, inferInstance⟩ : PadicAlgCl.FiniteIntermediateField T.ell) true).2.2.choose

/-- The regular coefficient complex is bounded constructible in the native condensed category.
Source: the constant-coefficient clause (blueprint: def-tw-frobenius-action).
Proof: the regular module has its one-stratum finite constant model and the degree-zero
single complex is bounded constructible. -/
theorem boundedCoefficient_mem :
    ProEtale.boundedConstructible T.coefficientRing T.coefficientObject := by
  sorry

/-- The regular coefficient object, with its bounded-constructibility proof.
Source: latest blueprint, constant coefficients in construction step 3
(blueprint: def-tw-frobenius-action). -/
def boundedCoefficient : T.coefficientCategory :=
  ⟨T.coefficientObject, boundedCoefficient_mem T⟩

/-- The ordinary derived operator is transport followed by the coefficient identification.
Source: latest blueprint, ordinary induced action, construction step 4
(blueprint: def-tw-frobenius-action). -/
def ordinaryEnd : End
    (T.ordinaryCoefficientComplex.obj T.coefficientObject) :=
   (pointInsertion T).hom.app _ ≫
    T.pointFiber.map
      ((CohomologyTransport.ordinary _ (schemeAut T).hom T.geometricBaseChange.hom
        T.geometricBaseChange.hom (pointAut T).hom (geometry T).comm).app T.coefficientObject ≫
        (CohomologyTransport.R _ T.geometricBaseChange.hom).map (coefficientIso T).hom)

/-- Compact support uses exactly the compactification and fibre functor of the conventions.
Exchange reindexes this compactification and compares it back by the normalized mate.
Source: latest blueprint, compact induced action, construction steps 3--4
(blueprint: def-tw-frobenius-action). -/
def compactEnd : End (T.compactSections.obj T.coefficientObject) := by
  letI : QuasiCompact T.geometricBaseChange.hom :=
    CondensedTwConventions.geometricQuasiCompact T
  exact (pointInsertion T).hom.app _ ≫
    T.pointFiber.map
      (((compactData T).exchange
          (T.compactification)
          (T.compactification)).hom.app
          (boundedCoefficient T) ≫
        (CohomologyTransport.C _
          (T.compactification)).map
            (coefficientIso T).hom)

/-- Both specified constant-coefficient derived Frobenius operators are invertible.
Source: latest blueprint, both automorphism clauses (blueprint: def-tw-frobenius-action).
Proof: step 1 identifies the scheme automorphism and its inverse by geometric and
arithmetic field Frobenius. Step 2 identifies the pulled-back regular module by
multiplication, with inverse b ↦ b tensor 1. Step 3 applies the normalized ordinary
and compact isomorphism-square exchanges to this semilinear square; the constant
module is bounded constructible by its single rank-one stratum. Point insertion is
restriction along the base automorphism and is inverted by restriction along its
inverse. For compact support Q80’s FrobeniusTransportData.exchange_normalization identifies
the exchange with squareExchange followed by targetCompare; the proper-refinement
normalization and cocycle compare the reindexed compactification with the chosen one
and make this independent of that choice. Step 4
composes the invertible transport with the image of the coefficient isomorphism;
the inverse is the reverse composite of their inverses. -/
theorem end_isIso : IsIso (ordinaryEnd T) ∧ IsIso (compactEnd T) := by
  sorry

/-- The pair of specified derived Frobenius automorphisms before taking homology.
Source: latest blueprint, both induced automorphisms, construction step 4
(blueprint: def-tw-frobenius-action). -/
def complexAction :=
  letI := (end_isIso T).1
  letI := (end_isIso T).2
  (asIso (ordinaryEnd T), asIso (compactEnd T))

/-- Ordinary and compactly supported linear automorphisms in every integer degree.
The target is the very same compact cohomology as in `def-tw-conventions`; all scalars
are the ordinary singleton sections of the condensed algebraic closure. Reapplying this
construction to any specified base-changed finite-field model gives the same notation.
Source: latest blueprint, the displayed action and final sentence
(blueprint: def-tw-frobenius-action). -/
def action (i : ℤ) :=
  letI := CondensedTwConventions.scalarHasDerived T
  ((DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} T.scalarRing) i).mapIso (complexAction T).1,
    (DerivedCategory.homologyFunctor
      (ModuleCat.{u + 1} T.scalarRing) i).mapIso (complexAction T).2)

end FrobeniusAction
end WeilConjectures.CondensedTwConventions
