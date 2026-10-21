# AlgebraicGeometry.ProEtale.integralModelCondensedCoefficients

## Reason

Restore the missing live module assigned by coord/rework.tsv after the cluster-restore
reversion. Its authoritative archived source already contains a complete proof and zero
local holes. This is a source restoration, not a newly closed proof obligation.

## Old

The live path lean/Sheaf/Paper/IntegralModelSurjectiveClosedReflection.lean is absent.
The source preserved at quarantine/Sheaf/Paper/IntegralModelSurjectiveClosedReflection.lean
has the following coefficient definition, commutativity instance and theorem signature:

```lean
noncomputable def integralModelCondensedCoefficients (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  letI := spectralNorm.normedField (Padic l) E
  Mon.mk (Profinite.continuousCoefficientRingObj (Padic.coefficientExtensionIntegers l E))

/-- The integral condensed coefficient ring is commutative, by its pointwise operations.
Source: blueprint det-lem-int-ext-formula, proof (1)
(blueprint: lem-sfb-integral-model-surjective-closed-reflection). -/
noncomputable instance integralModelCondensedCoefficients_isCommMonObj
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    IsCommMonObj (integralModelCondensedCoefficients l E).X :=
  letI := spectralNorm.normedField (Padic l) E
  inferInstanceAs (IsCommMonObj
    (Profinite.continuousCoefficientRingObj (Padic.coefficientExtensionIntegers l E)))


theorem integralModel_surjective_closed_reflection
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [Surjective i]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralModelCondensedCoefficients l E).X X)) :
    HasFiniteConstantLocalModel (integralModelCondensedCoefficients l E).X X F ↔
      HasFiniteConstantLocalModel (integralModelCondensedCoefficients l E).X Z
        ((CondensedRing.upperStar (integralModelCondensedCoefficients l E).X i).obj F)
```

## New

Restore that source byte for byte to its assigned live path, including all public imports,
all private proved helpers, local transparency attributes and the complete theorem proof.
The coefficient ring remains the continuous condensed valuation ring with its spectral
norm topology. All signatures, universes, data, theorem hypotheses and conclusions are
identical to the archive. No target meaning changes or target semantic review reopens.
The two existing DAG attachments and all statement and proof dependencies are retained.

## Users

The downstream script reports an unknown module because the live source is missing.
An exact import scan across lean/ and quarantine/ finds the two direct consumers below.
Their source has been read; neither needs adaptation. No claim file for either consumer
is present in the shared snapshot. The archived IntegralTensorShriek uses the coefficient
and commutativity instance for its point-complex models; IntegralStratumHomFormula cites
the reflection result in its filtration argument. A separate importer compiled against
the freshly compiled restored module checks commutativity-instance synthesis, its finite
free point-model type, and the reverse reflection implication with exactly the original
hypotheses. No consumer is included or restored by this packet.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralTensorShriek | unclaimed | Quarantined direct public importer; identical coefficient, instance and public imports; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed | Quarantined direct proof importer; identical reflection statement; no adaptation. |

The item compiled alone in 3.6 seconds and with its importer in 6.3 seconds. The importer
compiled in 4.7 seconds. Coefficient-definition and commutativity axiom probes contain only
propext, Classical.choice and Quot.sound. The restored theorem has no local sorry but
reaches existing unresolved dependency proofs; this delivery adds no such dependency.

## Status

landed 20261021T021010-L-2689929 2026-10-21 (merge of deliver/F4/Sheaf.Paper.IntegralModelSurjectiveClosedReflection)
