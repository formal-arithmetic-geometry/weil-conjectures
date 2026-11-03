/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalLocalizingProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowProEtaleComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
public import WeilConjectures.AlgebraicGeometry.ProEtalePfAdmissibleModels
public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionComparisonEtaleOrigin
public import WeilConjectures.AlgebraicGeometry.DetFiniteCondensedProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralProperProjectionFormula
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.PoincareDuality.CurrentProEtaleProjection.CurrentProEtaleProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralProjectionFormulaLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperProjectionFormulaField

/-! # The pro-etale projection formula statement

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/
sk-thm-sf-pf-proetale/_section.md, complete unit statement, both paragraphs, read with the
standing Six Functors setting (blueprint: sk-thm-sf-pf-proetale).

The finite clause quantifies over every finite commutative coefficient ring killed by a
power of the fixed prime and retains the etale-origin witnesses and finite Tor intervals.
The condensed clauses record the direct results sk-thm-sf-pf-adic and sk-thm-sf-pf-field:
for proper `p`, the canonical `moduleObjectProjectionMap` on the localizing closures
`localizingClosureProEtale` for `O_E`, `E` and `Qbar_l`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale

/-- Projection formula for the pro-etale realization, with the complete finite and condensed
coefficient clauses of the blueprint unit.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/
sk-thm-sf-pf-proetale/_section.md, complete unit statement, both paragraphs, read with the
standing Six Functors setting (blueprint: sk-thm-sf-pf-proetale).

The first conjunct states the finite admissible clause: `A` is finite commutative and killed by
an ell-power; `K` and `L` are specified pro-etale realizations of bounded constructible etale
complexes with finite Tor amplitude; and the canonical projection map for every compactification
is an isomorphism between bounded-below endpoints. The remaining conjuncts state the direct
condensed proper projection maps for the three coefficient families, with both arguments in the
recorded `localizingClosureProEtale` classes and no additional endpoint predicate.

Proof (node sk-thm-sf-pf-proetale, source sk-thm-sf-pf-proetale.proof.md):
1. Write `M, H` for the etale antecedents, `f = r j` the compactification. Represent `M` by a
   bounded complex and `H` by a bounded flat complex; pullback, exact `j_!` and `Rr_*` keep
   lower bounds, so both projection endpoints and the comparison inputs lie in `D+`.
2. The etale projection map is `Rr_*(γ_e) ∘ π_e`, the proper projection map of `r` followed by
   the open tensor comparison; both factors are invertible for every finite commutative `A`.
3. The exact comparison `ν^*` commutes with tensor and pullback; pasting the proper projection
   comparison square with the open tensor square identifies `ν^*` of the etale projection map
   with the pro-etale `projectionMapOfCompactification` up to the specified comparisons
   (`r` is proper, hence qcqs).
4. Hence the pro-etale map is an isomorphism between `D+` objects; conjugating by the
   retained origin isomorphisms `wK.iso`, `wL.iso` gives the assertion for `K, L`.
5. The remaining conjuncts are the direct condensed results sk-thm-sf-pf-adic (`O_E`) and
   sk-thm-sf-pf-field (`E`, `Qbar_l`) on their stated domains; no etale transport.
The proof below follows these steps through the landed comparison and finite proper results.
-/
theorem hasProjectionFormula_of_constructibleFiniteTor_statement
    (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    (hk : Finite k ∨ IsAlgClosed k) [Fact (ringChar k).Prime]
    (hkl : ringChar k ≠ ell)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X.left ⟶ Y.left) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    (∀ (A : Type (u + 1)) [CommRing A] [Finite A]
        (hA : ∃ n : ℕ, ∀ a : A, (ell ^ n : A) * a = 0)
        (K : DerivedCategory.Plus
          (Sheaf (Scheme.ProEt.topology X.left) (ModuleCat.{u + 1} A)))
        (L : DerivedCategory.Plus
          (Sheaf (Scheme.ProEt.topology Y.left) (ModuleCat.{u + 1} A)))
        (wK : Scheme.FixedEtaleOriginWitness X.left A K)
        (wL : Scheme.FixedEtaleOriginWitness Y.left A L)
        (_hK : Etale.DerivedCategory.isBoundedConstructible A X.left wK.complex.obj)
        (_hL : Etale.DerivedCategory.isBoundedConstructible A Y.left wL.complex.obj)
        (_tK : ∃ a b : ℤ,
          Etale.DerivedCategory.hasTorAmplitudeIn A X.left a b wK.complex.obj)
        (_tL : ∃ a b : ℤ,
          Etale.DerivedCategory.hasTorAmplitudeIn A Y.left a b wL.complex.obj),
        ∃ (hS : DerivedCategory.TStructure.t.plus
            (((derivedTensorRightDerivedLowerShriek (ModuleCat.{u + 1} A) c).obj
              K.obj).obj L.obj))
          (hT : DerivedCategory.TStructure.t.plus
            (((rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
              (ModuleCat.{u + 1} A) c).obj K.obj).obj L.obj)),
          IsIso (ObjectProperty.homMk
            (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app K.obj).app L.obj) :
            (⟨_, hS⟩ : DerivedCategory.Plus
              (Sheaf (Scheme.ProEt.topology Y.left) (ModuleCat.{u + 1} A))) ⟶
              ⟨_, hT⟩)) ∧
      (∀ (E : PadicAlgCl.FiniteIntermediateField ell),
        (∀ (p : X ⟶ Y) [IsProper p.left]
          (M : DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
              (condensedRingObj
                (Profinite.padicIntegersRingObj ell E.1) X.left)))
          (N : DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
              (condensedRingObj
                (Profinite.padicIntegersRingObj ell E.1) Y.left))),
          localizingClosureProEtale
              (Profinite.padicIntegersRingObj ell E.1) X.left M →
            localizingClosureProEtale
              (Profinite.padicIntegersRingObj ell E.1) Y.left N →
            IsIso (moduleObjectProjectionMap
              (Profinite.padicIntegersRingObj ell E.1) p.left M N)) ∧
        (∀ (p : X ⟶ Y) [IsProper p.left]
          (M : DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
              (condensedRingObj
                (Profinite.continuousMapRingObj E.1) X.left)))
          (N : DerivedCategory
            (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
              (condensedRingObj
                (Profinite.continuousMapRingObj E.1) Y.left))),
          localizingClosureProEtale
              (Profinite.continuousMapRingObj E.1) X.left M →
            localizingClosureProEtale
              (Profinite.continuousMapRingObj E.1) Y.left N →
            IsIso (moduleObjectProjectionMap
              (Profinite.continuousMapRingObj E.1) p.left M N))) ∧
      (∀ (p : X ⟶ Y) [IsProper p.left]
        (M : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
            (condensedRingObj
              (Profinite.padicAlgClRingObj ell) X.left)))
        (N : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
            (condensedRingObj
              (Profinite.padicAlgClRingObj ell) Y.left))),
        localizingClosureProEtale
            (Profinite.padicAlgClRingObj ell) X.left M →
          localizingClosureProEtale
            (Profinite.padicAlgClRingObj ell) Y.left N →
          IsIso (moduleObjectProjectionMap
            (Profinite.padicAlgClRingObj ell) p.left M N)) := by
  have : Fact (ringChar k ≠ ell) := ⟨hkl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro A _ _ hA K L wK wL hK hL tK tL
    have hbK : _root_.DerivedCategory.TStructure.t.bounded wK.complex.obj := by
      obtain ⟨a, b, _, h⟩ := hK.2
      exact ⟨⟨a, (_root_.DerivedCategory.isGE_iff _ a).2
        (fun i hi ↦ h i (Or.inl hi))⟩,
        ⟨b, (_root_.DerivedCategory.isLE_iff _ b).2
          (fun i hi ↦ h i (Or.inr hi))⟩⟩
    obtain ⟨a, b, ht⟩ := tL
    have htE := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp ht
    have hML := Etale.plus_derivedTensor_leftDerivedUpperStar c.g
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).bounded_mapDerivedCategory_obj
        hbK) htE
    have := Etale.isIso_rightDerivedLowerStarProjectionMap_of_finite A c.g
    have hPF : IsIso
        (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app K.obj).app
          L.obj) :=
      hasProjectionFormulaOfCompactification_of_comparison c wK.iso wL.iso hbK hML
        inferInstance
    have htP : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) Y.left a b
        L.obj :=
      (DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) Y.left a b).prop_of_iso
        wL.iso ((DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b
          wL.complex.obj).2 htE)
    have hS : _root_.DerivedCategory.TStructure.t.plus
        (((derivedTensorRightDerivedLowerShriek (ModuleCat.{u + 1} A) c).obj
          K.obj).obj L.obj) := by
      rw [derivedTensorRightDerivedLowerShriek_obj_obj]
      obtain ⟨r, hr⟩ := K.property
      have : K.obj.IsGE r := hr
      have := (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).isGE_mapDerivedCategory_obj
        K.obj r
      have : ((rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) c).obj K.obj).IsGE r :=
        Functor.isGE_rightDerivedFunctor_obj _ _ r
      exact ⟨r + a, _root_.DerivedCategory.isGE_tensor_of_torAmplitudeGE_right
        (_root_.DerivedCategory.torAmplitudeGE_of_torAmplitudeIn htP) _ r⟩
    have := hPF
    refine ⟨hS, _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
      (asIso (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app
        K.obj).app L.obj)) hS, ?_⟩
    exact (ObjectProperty.isIso_hom_iff _).mp hPF
  · intro E
    constructor
    · intro p _ M N hM hN
      exact isIso_integral_projection_formula_localizing ell E k p M N hM hN
    · intro p _ M N hM hN
      exact (projectionFormulaField ell
        (Profinite.continuousMapRingObj E.1)
        (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)).2 p M N hM hN
  · intro p _ M N hM hN
    exact (projectionFormulaField ell (Profinite.padicAlgClRingObj ell)
      (Or.inr ⟨Iso.refl _⟩)).2 p M N hM hN

end AlgebraicGeometry.ProEtale
