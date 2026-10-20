# AlgebraicGeometry.Scheme.isIso_homComplex_resolution_of_isStrictlyPerfect

## Reason

Complete the listed retirement in coord/retire-items.tsv. The Sheaf copy and its
adopted source twin have identical public theorem signatures except for the binder
name `_hP` versus `hP`. Their proofs are identical with that renaming. The duplicate
has zero holes and no definition repair is needed.

The Sheaf copy additionally exposed `AlgebraicGeometry.Scheme.shortExact_of_retract`.
Its sole consumer is RingedSiteBoundedFreeRHomMapQuasiIso, which uses only this
helper and never the strictly-perfect theorem. The upstream helper is private.
Localize the existing, complete generic retract proof as a private helper in that
consumer. This preserves the mathematics without modifying the source library or
retaining a duplicate strictly-perfect module.

## Old

The retired module exposes these signatures:

```lean
theorem shortExact_of_retract
    {A : Type*} [Category A] [Abelian A] {S T : ShortComplex A}
    (i : S ⟶ T) (r : T ⟶ S) (hir : i ≫ r = 𝟙 S) (hT : T.ShortExact) :
    S.ShortExact

theorem isIso_homComplex_resolution_of_isStrictlyPerfect
    (X : Scheme.{u}) (U : X.Opens) [IsAffine U.toScheme]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose ((Opens.grothendieckTopology X).over U)
        (forget₂ CommRingCat RingCat)).obj (X.sheaf.over U)))]
    (P M : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (_hP : IsStrictlyPerfect X U P) :
    Nonempty (DerivedCategory.Q.obj (homComplex (R := X.sheaf.over U) P M) ≅
      (derivedInternalHom ((Opens.grothendieckTopology X).over U) (X.sheaf.over U)).obj
        (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj M)) ∧
    ∀ (I : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ ⥤
        CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
      (η : 𝟭 (CochainComplex
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ) ⟶ I),
      (∀ N : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
        QuasiIso (η.app N) ∧ (I.obj N).IsKInjective) →
        IsIso (DerivedCategory.Q.map
          (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map (η.app M)))
```

The consumer privately imports:

```lean
import Sheaf.AlgebraicGeometry.StrictlyPerfectDerivedInternalHom
```

## New

Withdraw lean/Sheaf/AlgebraicGeometry/StrictlyPerfectDerivedInternalHom.lean using
deleted.txt. The theorem above remains available with the same full name in
WeilConjectures.AlgebraicGeometry.StrictlyPerfectDerivedInternalHom, unchanged;
only its hypothesis binder is spelled `hP`. The node lem-pc-rhom-strict-perfect-hom
points to that upstream module and file. Its mathematical statement, proof steps,
proof dependencies, and unit route remain unchanged.

The sole consumer instead imports:

```lean
import Mathlib.CategoryTheory.MorphismProperty.Retract
```

The generic helper above becomes private to the consumer's CategoryTheory namespace,
with the identical signature and proof. Its one call becomes unqualified. All
existing consumer signatures, visibility, attributes, and mathematical content stay
identical. There is no new public declaration, definition, axiom, or proof hole.

## Users

The downstream list was obtained with tools/downstream.py for both public names.
A search of lean/ and quarantine/ found exactly one current import of the retired
module. The old retirement inventory also lists FiniteFreeDerivedDualModel and
StrictlyPerfectRHomEvaluationLocal; both now exist in the source tree and already
import the upstream twin. No source file is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictlyPerfectDerivedInternalHom | P9 | Withdraw duplicate; repoint its DAG attachment upstream. |
| Sheaf.Algebra.Homology.RationalTermHomComparison | unclaimed | Indirect importer only; no changed public signature or adaptation. |
| Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomMapQuasiIso | unclaimed | Replace the sole import with the Mathlib retract API; retain the generic proof as a private helper and change its single call. |
| Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel | unclaimed | Indirect importer only; no changed public signature or adaptation. |
| Sheaf.AlgebraicGeometry.DerivedHomSheafComparisonLisse | unclaimed | Indirect importer only; no changed public signature or adaptation. |
| Sheaf.AlgebraicGeometry.DerivedMorphismWeaklyContractibleEvaluation | unclaimed | Indirect importer only; no changed public signature or adaptation. |
| Sheaf.Paper.CompatibleFiniteDerivedTrivializations | unclaimed | Indirect importer only; no changed public signature or adaptation. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | unclaimed | Indirect importer only; no changed public signature or adaptation. |
| Sheaf.Paper.FiniteFreeHomComparison | unclaimed | Indirect importer only; no changed public signature or adaptation. |
| Sheaf.Paper.LisseNormalizedTowerLocalModels | unclaimed | Indirect importer only; no changed public signature or adaptation. |
| Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity | unclaimed | Indirect importer only; no changed public signature or adaptation. |
| Sheaf.Paper.NormalizedDerivedIsomorphismSectionReduction | unclaimed | Indirect importer only; no changed public signature or adaptation. |
| Sheaf.Paper.NormalizedDerivedIsomorphismTransport | unclaimed | Indirect importer only; no changed public signature or adaptation. |
| WeilConjectures.AlgebraicGeometry.FiniteFreeDerivedDualModel | not adapted | Sole DAG parent; already imports and uses the unchanged upstream theorem. |
| WeilConjectures.AlgebraicGeometry.StrictlyPerfectRHomEvaluationLocal | not adapted | Already imports the upstream twin. |

The current parent lem-pc-finite-free-derived-dual-model retains this dependency;
retirement does not prune the mathematical result. The unit sk-thm-picard-duality
has empty realized lists and is unchanged. Upstream and target declarations and
imports are unchanged.

Validation: the original item and the adapted sole consumer compile separately
through lcompile.py. A scratch example checks the entire original theorem signature
by applying the upstream theorem. Delivery preflight also probes the private helper
and all other declarations of the adapted consumer.

## Status

landed 20261020T221310-L-4170278 2026-10-20 (merge of deliver/P9/Sheaf.AlgebraicGeometry.StrictlyPerfectDerivedInternalHom)
