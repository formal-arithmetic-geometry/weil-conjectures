# NativeEncoding ordinary interface and finiteness proof imports

## Reason

The projective-space finiteness proof can reuse the general condensed proper direct-image
finiteness theorem. Its original imports lead back to native lower-star finiteness through
FieldStagePointers and two unused scalar-extension/local-model proof imports. The original
NativeEncodingDerivedOperations container also publicly imports WeilSheaf.LowerShriek,
which reaches native lower-star finiteness. Extracting only its native ordinary interface
and narrowing three proof imports breaks these cycles. All existing declaration signatures,
attributes, visibility and non-theorem bodies are preserved. No adopted source is edited.

## Old

The following declarations were defined in `Sheaf.Paper.NativeEncodingDerivedOperations`,
in namespace `AlgebraicGeometry.ProEtale.NativeEncoding`. Signatures, verbatim:

```lean
abbrev coefficientIso (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    condensedRingObj (Profinite.padicAlgClRingObj l) T ≅
      (weilCoefficientsForgetAb l T).obj (adicConstantSheaf l T)

@[instance] theorem coefficientIsoMon (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    IsMonHom (coefficientIso l T).hom

def encoding (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    AdicSheaf l T ⥤ Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) T)

@[instance] theorem encodingAdditive (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (encoding l T).Additive

@[instance] theorem encoding_isEquivalence (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (encoding l T).IsEquivalence

def equivalence (l : ℕ) [Fact l.Prime] (T : Scheme.{u})

abbrev derivedEncoding (l : ℕ) [Fact l.Prime] (T : Scheme.{u})

theorem encoding_underlying (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    encoding l T ⋙ Mod.forget (condensedRingObj (Profinite.padicAlgClRingObj l) T) =
      AdicSheaf.forget (l

theorem encoding_exact_derived (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    PreservesFiniteLimits (encoding l T) ∧ PreservesFiniteColimits (encoding l T) ∧
      (derivedEncoding l T).IsEquivalence ∧
      (∀ I : CochainComplex (AdicSheaf l T) ℤ,
        CochainComplex.IsKInjective (((encoding l T).mapHomologicalComplex (.up ℤ)).obj I) ↔
          I.IsKInjective)

theorem encoding_ordinary_operations (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ p : adicLowerStar l f ⋙ encoding l Y ≅
        encoding l X ⋙ CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f,
      (∀ (M : AdicSheaf l X) (V : Y.ProEtᵒᵖ)
        (m : ((adicLowerStar l f).obj M).X.obj.obj V),
        ((p.hom.app M).hom.hom.app V) m = m) ∧
      ∃ q : adicUpperStar l f ⋙ encoding l X ≅
          encoding l Y ⋙ CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f,
      (mateEquiv (adicUpperStarLowerStarAdjunction l f)
        (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
        q.inv).natTrans = p.hom ∧
      PreservesFiniteLimits (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f) ∧
      PreservesFiniteColimits (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f) ∧
      (condensedPushforwardHom (Profinite.padicAlgClRingObj l) f ≫
          (lowerStar Ab.{u + 1} f).map (coefficientIso l X).hom =
        (coefficientIso l Y).hom ≫
          (weilCoefficientsForgetAb l Y).map (adicConstantSheafToLowerStar l f))

def pushComparison (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)

def pullComparison (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)

def derivedPushComparison (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (adicLowerStar l f).rightDerivedFunctor ⋙ derivedEncoding l Y ≅
      derivedEncoding l X ⋙ CondensedRing.moduleObjectDerivedPushforward
        (Profinite.padicAlgClRingObj l) f
```

The original module publicly imported its fixed-pair/Weil-sheaf dependencies together with
these general native declarations. Three old private proof imports were:

```lean
import WeilConjectures.SixFunctors.Etale.Derived.FieldStagePointers
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension
import Sheaf.Paper.CompatibleFiniteDerivedTrivializations
```

They belonged respectively to EllAdicProperConstructibleCohomology,
FiniteLevelProEtaleBaseChange, and LisseNormalizedTowerLocalModels.

## New

The declarations are now defined in `Sheaf.Paper.NativeAdicEncodingCore`, under the identical
namespace, attributes and signatures. All non-theorem bodies are identical; four theorem
proofs are now complete. NativeEncodingDerivedOperations adds
`public import Sheaf.Paper.NativeAdicEncodingCore` and retains every other original import
and every fixed-pair declaration. The existing weil_resolution_comparison and
native_encoding_derived_operations theorem holes are filled using the generic K-injectivity
API and the existing comparison definitions, without changing their statements. Its old importers see the same native API.
The moved signatures remain verbatim:

```lean
abbrev coefficientIso (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    condensedRingObj (Profinite.padicAlgClRingObj l) T ≅
      (weilCoefficientsForgetAb l T).obj (adicConstantSheaf l T)

@[instance] theorem coefficientIsoMon (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    IsMonHom (coefficientIso l T).hom

def encoding (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    AdicSheaf l T ⥤ Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) T)

@[instance] theorem encodingAdditive (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (encoding l T).Additive

@[instance] theorem encoding_isEquivalence (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (encoding l T).IsEquivalence

def equivalence (l : ℕ) [Fact l.Prime] (T : Scheme.{u})

abbrev derivedEncoding (l : ℕ) [Fact l.Prime] (T : Scheme.{u})

theorem encoding_underlying (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    encoding l T ⋙ Mod.forget (condensedRingObj (Profinite.padicAlgClRingObj l) T) =
      AdicSheaf.forget (l

theorem encoding_exact_derived (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    PreservesFiniteLimits (encoding l T) ∧ PreservesFiniteColimits (encoding l T) ∧
      (derivedEncoding l T).IsEquivalence ∧
      (∀ I : CochainComplex (AdicSheaf l T) ℤ,
        CochainComplex.IsKInjective (((encoding l T).mapHomologicalComplex (.up ℤ)).obj I) ↔
          I.IsKInjective)

theorem encoding_ordinary_operations (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ p : adicLowerStar l f ⋙ encoding l Y ≅
        encoding l X ⋙ CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f,
      (∀ (M : AdicSheaf l X) (V : Y.ProEtᵒᵖ)
        (m : ((adicLowerStar l f).obj M).X.obj.obj V),
        ((p.hom.app M).hom.hom.app V) m = m) ∧
      ∃ q : adicUpperStar l f ⋙ encoding l X ≅
          encoding l Y ⋙ CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f,
      (mateEquiv (adicUpperStarLowerStarAdjunction l f)
        (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
        q.inv).natTrans = p.hom ∧
      PreservesFiniteLimits (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f) ∧
      PreservesFiniteColimits (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f) ∧
      (condensedPushforwardHom (Profinite.padicAlgClRingObj l) f ≫
          (lowerStar Ab.{u + 1} f).map (coefficientIso l X).hom =
        (coefficientIso l Y).hom ≫
          (weilCoefficientsForgetAb l Y).map (adicConstantSheafToLowerStar l f))

def pushComparison (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)

def pullComparison (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)

def derivedPushComparison (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (adicLowerStar l f).rightDerivedFunctor ⋙ derivedEncoding l Y ≅
      derivedEncoding l X ⋙ CondensedRing.moduleObjectDerivedPushforward
        (Profinite.padicAlgClRingObj l) f
```

No mathematical definition changed. In particular, encoding is still the explicit composite
of scalar forgetting and restriction along coefficientIso; derivedPushComparison is still
its actual universal right-derived composition. Existing choices remain the same choices
from the same uniquely normalized statements; no new data are chosen from existence.
The existing coefficientIsoMon, encodingAdditive and encoding_underlying holes are proved
using the existing ring-map comparisons, pointwise addition and definitional equality. The
encoding_exact_derived is also proved using the exact-equivalence and K-injectivity APIs.
The other two existing sorry theorem bodies moved unchanged. No new obligation was introduced.

The three proof-import adaptations are:

- EllAdicProperConstructibleCohomology imports TorAmplitude and Stability.Generation instead
  of FieldStagePointers. The two used general facts are private, fully proved helpers
  proper_bounded_induction and proper_finite_field_tor. Its public theorem statements and
  completed proofs are preserved.
- FiniteLevelProEtaleBaseChange drops ScalarExtension and imports ExactFunctor. Its final
  derived reflection instance is proved directly using homology and exact conservative
  functors. All existing theorem signatures and other data remain identical.
- LisseNormalizedTowerLocalModels drops only CompatibleFiniteDerivedTrivializations.
  Every declaration and proof body stays identical.

No target signature or definition used by a target changes its meaning. The new theorem
encoding_constructible_iff is proved for the existing two predicates, without altering them.

## Users

`tools/downstream.py --uses` reports the original native container and
NativeForgetConstructibleCriterion as users of moved names; it reports the other two native
modules below as downstream. All original consumers retain their original import and
receive the identical declarations through public reexport. The table also lists all
adapted modules and the direct consumers of the narrowed proof-import modules.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | J1 | Proved using native core and general proper theorem. |
| Sheaf.AlgebraicGeometry.NativeAdicConstructibilityEncoding | new in J1 packet | Proved comparison using the core. |
| Sheaf.Paper.NativeAdicEncodingCore | new in J1 packet | Existing native interface extracted; four holes proved. |
| Sheaf.Paper.NativeEncodingDerivedOperations | unclaimed | Publicly reexports core; retains fixed-pair API and imports. |
| Sheaf.Paper.NativeForgetConstructibleCriterion | unclaimed | Uses encoding; identical public reexport, no edit. |
| Sheaf.Paper.NativeCompactProjectionFormula | unclaimed | Identical public reexport, no edit. |
| Sheaf.WeilSheaf.NativePullbackStarPreservation | R3 | Identical public reexport, no edit. |
| Sheaf.AlgebraicGeometry.EllAdicProperConstructibleCohomology | unclaimed | Narrow proof imports and proved private helpers. |
| Sheaf.Paper.FiniteLevelProEtaleBaseChange | unclaimed | Narrow proof import and direct derived reflection proof. |
| Sheaf.Paper.LisseNormalizedTowerLocalModels | unclaimed | Remove unused proof import only. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic | unclaimed | Same proved cohomology theorem, no public interface change. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic | unclaimed | Same public interface; no edit. |
| Sheaf.AlgebraicGeometry.ProEtaleProperBoundaryCohomology | unclaimed | Proof import narrowing has no public effect. |
| Sheaf.AlgebraicGeometry.SfFullcdEtaleOrigin | unclaimed | Proof import narrowing has no public effect. |
| Sheaf.Paper.FourArrows | unclaimed | Proof import narrowing has no public effect. |
| Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity | unclaimed | Proof import narrowing has no public effect. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed | Proof import narrowing has no public effect. |

## Status

landed 20261025T043250-L-1693096 2026-10-25 (merge of deliver/J1/Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness)
