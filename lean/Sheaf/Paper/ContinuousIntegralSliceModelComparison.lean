/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R5
-/
module

public import Sheaf.Paper.ContinuousConstructibleModule
public import Sheaf.Paper.IntegralStratifiedPerfectModels
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.ContinuousCoefficientModuleEncoding

/-!
# Integral scalar models on a slice site

Source: Bhatt--Scholze, Lemma 6.5.8(1) and Definition 6.8.10.
(blueprint: lem-weil-pbc-continuous-integral-slice-model-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- Coefficient transport identifies the finite scalar models on each slice after a
locally closed immersion. Both sides use ordinary scalar extension, with torsion allowed.
Source: Bhatt--Scholze, Lemma 6.5.8(1), Definition 6.8.10 and the completed coefficient
presentation of Definition 6.5.1.
(blueprint: lem-weil-pbc-continuous-integral-slice-model-comparison).

Proof: use the given normalized coefficient isomorphism c.
For a locally closed immersion h, inverse image commutes with the finite-quotient
inverse limit by Lemma 6.5.8(1). The resulting coefficient comparison is the adjunct of
precomposition of continuous functions: after every finite projection this is the
constant-ring pullback comparison. The same computation on constant sections shows
that the two scalar maps agree. Thus ordinary inverse image and scalar extension,
transported through these ring isomorphisms, commute by their adjunction universal
properties. The resulting isomorphism sends the pullback of integralConstantModule X N
to continuousCoefficientModule Z P, with P and N related by the lifted valuation-ring
isomorphism s. This is an equivalence of scalar-module categories and preserves finite
presentation. All the functor comparisons restrict to slice sites via overFunctor;
the coefficient isomorphisms induce equivalences there. Applying these equivalences
and their fully faithful inverses to the local model isomorphisms proves both directions.
The argument includes zero modules, torsion modules, the empty base and the empty slice;
it asserts no completeness for an arbitrary M. -/
theorem continuousIntegralSliceModelComparison
    (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [IsNoetherian X]
    (s : ULift.{u + 1} (latticeCoefficientIntegers l E) ≃+* Scheme.PbcIntegralRing l E)
    (c : Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E) ≅
      latticeCoefficientSheaf X (latticeCoefficientIntegers l E))
    (_hc : (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
        s.toCommRingCatIso.hom ≫ Scheme.pbcCompletedScalar X (Scheme.pbcIntegralDatum l E) =
      continuousCoefficientConstantMap X (latticeCoefficientIntegers l E) ≫ c.inv) :
      ∀ {Z : Scheme.{u}} (h : Z ⟶ X) [IsImmersion h]
        (M : SheafOfModules.{u + 1}
          (latticeModuleRing X (latticeCoefficientIntegers l E))) (U : Z.ProEt),
        (∃ P : ModuleCat.{u + 1} (ULift.{u + 1} (latticeCoefficientIntegers l E)),
          Module.FinitePresentation (ULift.{u + 1} (latticeCoefficientIntegers l E)) P ∧
          Nonempty ((continuousModulePullback h (latticeCoefficientIntegers l E) M).over U ≅
            (continuousCoefficientModule Z (latticeCoefficientIntegers l E) P).over U)) ↔
        (∃ N : ModuleCat.{u + 1} (Scheme.PbcIntegralRing l E),
          Module.FinitePresentation (Scheme.PbcIntegralRing l E) N ∧
          Nonempty ((SheafOfModules.overFunctor _ U).obj
            ((Scheme.proEtaleModuleInverseImage h
              (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))).obj
                ((CondensedRing.ringModuleEquivalenceOfIso X
                  ((Scheme.adicLisseForget X).mapIso c)).functor.obj M)) ≅
            (SheafOfModules.overFunctor _ U).obj
              ((Scheme.proEtaleModuleInverseImage h
                (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))).obj
                  ((Scheme.integralConstantModule X (Scheme.pbcIntegralDatum l E)).obj N)))) := by
  sorry

end AlgebraicGeometry.ProEtale
