# AlgebraicGeometry.perfect_overlap_object_realization

## Reason

Repair the 2026-10-22 E3 return at 971effb98. The previous packet was based on
c70691c45, when this module was quarantined. A2 restored it at 62c1c8e4ed5 before
that packet landed. Start from the current restored source, preserving A2's
public import of WeilConjectures.AlgebraicGeometry.PerfectHomTransport and all
public declarations, signatures, attributes and definition bodies.

The original missing-public-import defect has already been repaired by A2.
Do not reapply the obsolete restoration or add the unused TransportExtension
public import. Specialize the Hom-pin rewrite explicitly at the two fixed
objects, and map the nonempty core pair with the existing typed helper. Correct
the docstring and DAG proof to describe the proved CoreData dependency rather than repeat the
construction that CoreData supplies. Drop the redundant direct stage-equivalence
node edge; that construction remains a transitive dependency of CoreData.

## Old

The private Hom-pin proof rewrites with an unspecialized transition pin:

```lean
  rw [r.transition_pin]
```

The current final theorem obtains the core through an extra local proof:

```lean
  have hdata := hcore U V hcover hU hV A B hA hB E φU φV
  obtain ⟨⟨data, core⟩⟩ := hdata
  exact ⟨⟨data, completePerfectHomObjectRealization _ _ _ _ _ _ _ _ _ _ _ _ _ _ core⟩⟩
```

The old docstring and first DAG proof step describe building the stage
and apex equivalences separately in this file, although the proof obtains
these from CoreData.

## New

Rewrite at the exact fixed objects:

```lean
  rw [r.transition_pin k (objects a) (objects b)]
```

Map the proved core pair without repeated substitution of its geometric expressions:

```lean
  exact (hcore U V hcover hU hV A B hA hB E φU φV).map fun r ↦
    ⟨r.1, completePerfectHomObjectRealization _ _ _ _ _ _ _ _ _ _ _ _ _ _ r.2⟩
```

Use `delta perfectOverlapObjectRealizationStatement` for the target and
`unfold perfectOverlapObjectRealizationCoreStatement at hcore` for the source,
in place of the previous broad unfold and rewrite. The original final proof
timed out after 60 seconds; this controlled-unfolding assembly compiled in a
24.4-second scratch check.

Keep the existing typed assembly helper, categorical conjugation proof,
elaboration settings, public import block, realization structure, proposition
and theorem signature. The updated docstring and node record name the actual
CoreData theorem and core.transition_pin used here. The only changed node fields
are proof, proof_deps and proof_origin; current attachments and maintainer review
metadata are preserved. No route at the unit level changes.

## Users

The source-only downstream check finds the following five consumers. Their
public signatures, definitions and imported interfaces remain identical; no
adaptation is needed. The complete current HomPresentation source is compiled
as a scratch consumer against the revised module before delivery: the fresh
validation set compiles the item in 47.4 seconds and the consumer in 46.4 seconds.
The axiom probe also compiles and reports only propext, Classical.choice and
Quot.sound for the realization theorem, statement, structure and CoreData theorem.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealization | E3 | specialize Hom-pin rewrite, map core pair, control unfolding, correct proof documentation |
| Sheaf.AlgebraicGeometry.PerfectOverlapHomPresentation | unclaimed | unchanged realization structure, proposition and theorem; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectOverlapHomContinuity | unclaimed | unchanged transitive interface; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonCore | unclaimed | unchanged transitive interface; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonDiagram | unclaimed | unchanged transitive interface; no adaptation |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsDescendedTransition | unclaimed | unchanged transitive interface; no adaptation |

No source-library file, public mathematical assertion, target signature or
public definition changes. No target-meaning review is reopened. No module
held by another group is changed. No archive or Lean module is withdrawn.

## Status

landed 20261023T102637-L-2941107 2026-10-23 (merge of deliver/E3/Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealization)
