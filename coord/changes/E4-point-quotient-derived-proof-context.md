# WeilConjectures.PointQuotientTower.coherentSource proof context and extraction

## Reason

Restore the assigned quarantined item with its five existing proofs intact and
complete its derived comparison assembly. Fold exact derived-functor constructions
while elaborating the new proof and respect their transparency. Profiling after
this improvement showed 18.3 seconds kernel checking the new theorem and 37.3
seconds in final validation; the combined file still took 77 seconds. Split the
self-contained definitions and new theorem after improving the slow unfolding.

## Old

The module contained all tower constructions followed by six theorem declarations.
`coherentSource` had a `by sorry` proof and inherited the existing module option
`backward.isDefEq.respectTransparency false`. The local declaration below occurred
after `coherentSource` and before `evaluation`:

```lean
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapDerivedCategoryFactorsh
```

## New

Move the unchanged tower constructions into `Sheaf.Paper.PointQuotientTowerData`
and the completed `coherentSource` into
`Sheaf.Paper.PointQuotientTowerCoherentSource`. The item publicly imports both and
retains every original public import. All public names, signatures, definitions,
instances and attributes are preserved, and the five existing proofs and their two private additive instances stay intact
in the item. Its existing local irreducibility declaration stays before evaluation.

The comparison module additionally uses local folding:

```lean
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapDerivedCategoryFactorsh
attribute [local irreducible] completedReductionTower
set_option backward.isDefEq.respectTransparency true
```

Its proof uses the existing canonical counit-isomorphism lemma and composes the
explicit canonical factor isomorphisms. Their homomorphism is definitionally the
literal prescribed composite. Proof-only access to the existing private counit
helper uses `import all Sheaf.Paper.AdicCoefficientDatum`. Two new proof imports
supply K-flat coefficient restriction and the strictly earlier comparison before
sections and localization. No shared definition is changed.

## Users

There is no public interface or mathematical-meaning change. The quarantined source
is restored and publicly re-exports the extracted declarations. No consumer
adaptation is needed; unfinished DAG parents retain this dependency.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PointQuotientTowerHomotopy | E4 | Restored; five proofs retained. |
| Sheaf.Paper.PointQuotientTowerData | new | Unchanged tower definitions extracted. |
| Sheaf.Paper.PointQuotientTowerCoherentSource | new | Canonical comparison assembly. |

## DAG records (reviewer, 2026-10-27)

The extracted declarations are owned by their new nodes only: `lem-trf-point-quotient-tower-homotopy`
lists in `lean.declarations` only the five theorems that stay in its module
(homotopical, homotopies, homotopyDescent, quotientAugmentation, evaluation). The tower
definitions belong to `def-trf-point-quotient-tower-data`, and `coherentSource` belongs to
`lem-trf-point-quotient-tower-coherent-source`. The item's theorem statements use the
extracted definitions, so its `stmt_deps` gain `def-trf-point-quotient-tower-data`. The
mathematical statement is unchanged. The four new nodes cite
`def-weil-pbc-bounded-constructible-tower` in `stmt_deps`, because their signatures use
pbcRestrict, pbcModules, pbcAdicCompletion or pbcAdicRings. The strict-comparison node also
cites `def-weil-inverse-system` there, because its signature uses Functor.ofOpSequence.

## Status

landed 20261026T222629-L-675688 2026-10-26 (merge of deliver/E4/Sheaf.Paper.PointQuotientTowerHomotopy)
