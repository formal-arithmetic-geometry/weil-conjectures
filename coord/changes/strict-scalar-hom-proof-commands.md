# SheafOfModules.StrictScalarHom.exists_scalarHomChainIdentification

## Reason

The preflight requires a change record for commands added while proving the
item, although the public declarations and public imports remain identical.
The proof constructs a private ordinary scalar-extension functor and its
additivity proof, then uses local instances and reducibility settings to check
the constructions within 60 seconds. All attributes on imported or private
constructions are local. No source-written public signature or definition changes. To reduce constructor
helper generation, this version disables unused automatic size specifications
and constructor injectivity lemmas; consumer compilation checks this setting.

## Old

The original theorem body is exactly:

```lean
by
  sorry
```

The public section has no private ordinaryExtension additivity helper and no
associated local instance command.

## New

The theorem's statement stays verbatim; its body is:

```lean
by
  refine ⟨fun R S φ ↦ canonicalData.{c, v, u} φ, ?_⟩
  intro R S R' S' φ a b φ' h
  refine ⟨canonicalSquare.{c, v, u} h, ?_⟩
  exact coefficientCompatibility_generic.{c, v, u}
    (canonicalData.{c, v, u} φ) (canonicalData.{c, v, u} a)
    (canonicalData.{c, v, u} b) (canonicalData.{c, v, u} φ')
    (canonicalSquare.{c, v, u} h)
```

The new private helper signature and its activation are exactly:

```lean
private theorem ordinaryExtension_additive
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) :
    (ordinaryExtension.{c, v, u} φ).Additive

attribute [local instance] ordinaryExtension_additive
```

Its proof is the generator calculation for scalar extension of the sum of two
module maps. There is no new global instance. The new commands also set `genSizeOfSpec false` and `genInjectivity false`.
These suppress optional generated size specification and constructor-injectivity
lemmas of the four public structures, while retaining each structure, constructor,
projection and instance. No downstream source mentions their generated
`mk.inj`, `mk.injEq`, or size specifications. All five original downstream modules
compiled against the final candidate before delivery. The main module compiled in
48.1 seconds; the five consumers compiled in 44.0, 10.0, 6.1, 43.7, and 13.9 seconds
respectively (the report names each). Their temporary byte-identical test copies
are removed from the packet. All six compiles succeeded without warnings.

The proof-only commands set
`linter.unusedSectionVars false`, `synthInstance.maxSize 4096`,
`backward.isDefEq.respectTransparency false`, and
`backward.isDefEq.respectTransparency.types false` in this file. Later local
settings and local irreducibility attributes control unfolding of the completed
constructions; they do not alter any imported declaration or downstream scope.
The private proof section additionally sets `linter.unusedTactic false` after a
later delivery compile exceeded 60 seconds; this avoids repeated traversal of
the large tactic trees. Elaborated proofs are still fully kernel checked.
The existing public instance attribute `Extension.additive` stays verbatim.

The source-written public interface was compared declaration by declaration
against the current source. All 16 public definitions/structures, the theorem signature,
and the public import list are unchanged. No target statement or definition
used by a target changes meaning; no statement review is reopened.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.StrictScalarHomChain --uses
exists_scalarHomChainIdentification` lists these five downstream modules and
finds no downstream mention of the theorem. None is edited in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Algebra.Homology.FlatScalarEvaluationModel` | Q4 | Source-written interface unchanged; original compiled in consumer check. |
| `Sheaf.Algebra.Homology.ScalarHomChainCoefficientCoherence` | unclaimed | Source-written interface unchanged; original compiled in consumer check. |
| `Sheaf.Algebra.Homology.ScalarHomChainEvaluation` | unclaimed | Source-written interface unchanged; original compiled in consumer check. |
| `Sheaf.Algebra.Homology.SliceScalarHomChainAdjunction` | unclaimed | Source-written interface unchanged; original compiled in consumer check. |
| `Sheaf.Paper.LatticeSupportedHomFiniteComparison` | unclaimed | Source-written interface unchanged; original compiled in consumer check. |

## Status

landed 20261021T233757-L-860800 2026-10-21 (merge of deliver/Q1/Sheaf.Algebra.Homology.StrictScalarHomChain)
