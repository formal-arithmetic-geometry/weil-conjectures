## What changed

Replaced the sole proof hole of
`WeilConjectures.sfFieldShriekCompositionIntegral_component` by a complete Lean
assembly of three local obligations, without changing its statement or
`SfIntegralCompositionComponentSpec`.

The private geometric proof constructs an actual compatible tower dominating all
three given compactifications: densely compactify `cf.g` followed by `cg.i`, use
properness to make its square cartesian, and take an ambient common refinement
with the compatible tower over `cfg`. The pullback universal map gives its
refinement to `cf`. This geometry is proved, with no new hole.

The second private lemma transfers constructibility of a completed image through
the fixed qcqs realization. The component proof then takes local comparison
witnesses, proves their composite invertible, conjugates by the fixed realization
isomorphisms, and lifts through the full-subcategory inclusion. Conditional tower
independence proves the normalization on every tower and uniqueness of the
component, by faithfulness and `Iso.ext`. No equality is inferred from finite
coefficient evaluations.

Validation: `lcompile.py --all` compiled the four modules in import order, without
warnings or errors. The item took 9.9 seconds and each new module at most 5.1
seconds in the final run. The original exported signatures were compared verbatim
and are unchanged. No dependency path returns to any newly added node or to the
updated parent node.

Added three modules and matching nodes for the precise remaining analytic and
coherence steps. `sfCompletedCompositionTransport` is a real explicit composite;
it uses no choice or postponed data. All added imports of the item are private.
The change record is `coord/changes/S5-completed-composition-local-obligations.md`.

## Proved and sorry left

This is a decomposition, not a net proof gain. The old named hole closed is
`WeilConjectures.sfFieldShriekCompositionIntegral_component`
(`lem-zl-field-shriek-integral-component`); its unchanged theorem now has a complete
proof from the three lower statements. The item's textual hole count is now zero.
The geometric tower lemma and constructibility-transfer lemma are fully proved.

Three new named holes remain, each exactly the whole proof of a public theorem:

- `WeilConjectures.sfQcqsCompletedRefinement_exists`
  (`lem-zl-qcqs-completed-refinement`): existence for one proper refinement; no
  composition assertion.
- `WeilConjectures.sfCompletedCompositionOnTower_isIso`
  (`lem-zl-completed-composition-tower-is-iso`): invertibility on one fixed tower;
  no refinement comparisons, global normalization or uniqueness assertion.
- `WeilConjectures.sfCompletedCompositionTransport_independent`
  (`lem-zl-completed-composition-tower-independence`): equality of two already
  constructed completed arrows, conditional on all local witnesses; no existence
  or invertibility conclusion.

Holes closed: 1. Holes added: 3. Net change in these files: 2 more holes. These are
strict parts of the old argument, rather than the component statement renamed.

Edge cases checked: zero input, empty source, identity refinements, identical
towers with different normalized witnesses, and ambient schemes not separated
over the base field. Every composition and isomorphism remains meaningful in
those cases. The component's five quantifiers over a tower and its refinement
arrows are all retained.

## No longer needed

No existing import or module was removed. The stated dependency
`lem-sf-integral-compact-support-constructible` is not applied directly: the
constructibility of a completed image follows from the recorded functor's output,
the qcqs realization, and closure under isomorphisms. Its module remains needed
transitively by that recorded functor. The existing coefficient comparison,
strict-tower calculus and abstract refinement-coherence nodes remain obligations
of the three new local nodes. The parent node now records the actual assembly
rather than claiming those declarations directly discharge the completed maps.
No module is withdrawn, and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The historical build-error file reports a bad import of the normalization module;
the untouched original component compiled against the current published build.
The current server queue row is a proof item with one hole, not a zero-hole repair.

The original one-step plan conflates abstract strict-system coherence with its
identification on the prescribed completed coefficient maps. The existing
`PurCompactSupport.refinementProperOpen_existsUnique` cannot be applied at this
qcqs statement because it requires separated structure morphisms. The new
refinement obligation states precisely the needed version, without strengthening
the item's hypotheses. No existing shared statement was changed.

## New nodes

`lem-zl-qcqs-completed-refinement`, in `Sheaf.Paper.QcqsCompletedRefinement`, records
one local proper-refinement comparison with its open-adjunction normalization.
Its proof plan is restriction to the source open, the strict finite proper/open
comparison, complete-cone conservativity and proper composition.

`lem-zl-completed-composition-tower-is-iso`, in
`Sheaf.Paper.CompletedCompositionTowerIsIso`, records invertibility of the actual
single-tower proper/open map. Its proof plan follows finite proper/open comparison
and completed conservativity before whiskering by proper and open compositors.

`lem-zl-completed-composition-tower-independence`, in
`Sheaf.Paper.CompletedCompositionTowerIndependence`, records the conditional
six-square equality under common refinement. Its explicit transport definition
has no hole. The node separates coherence from both existence and invertibility.

Each node has a self-contained statement, a source, a complete proof plan, three
recorded Mathlib searches and its exact Lean declaration record. All three inherit
the original chapter and unit. Change record:
`coord/changes/S5-completed-composition-local-obligations.md`.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.CompletedCompositionTowerIndependence": "c905498261da337d2ffc4a7b442c7f62902aeedc", "Sheaf.Paper.CompletedCompositionTowerIsIso": "8c6da6787a3ce728b521796a2ff98c8a7c724c84", "Sheaf.Paper.FieldShriekCompositionIntegralComponent": "1cf7d95c816de8c22ce7868d4d3133d33a1261c5", "Sheaf.Paper.QcqsCompletedRefinement": "c3bf73ec10388390eb10db01aea6c30c10f7f887"}, "results": {"Sheaf.Paper.FieldShriekCompositionIntegralNaturality": {"hash": "639e546ed0e414c555ed09d3662aa15d1a963486", "status": "OK"}, "Sheaf.Paper.FieldShriekCompositionQcqs": {"hash": "cb1cf168bdb0908a5828dd52a2f3a112253053d3", "status": "OK"}}, "seconds": 97, "time": "2026-10-28T00:51:40+0800", "transitive": 0, "version": 1}
```

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
