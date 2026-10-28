## What changed

Replaced the proof hole in
`WeilConjectures.LocallyFiniteAdicCompactSupport.system_compact_support_realization`
without changing its signature or its two public imports. Added private proof imports
for native geometry, canonical coefficient change, stagewise naturality, and the new
finite-stage construction and integral transition equation.

`Sheaf.WeilSheaf.NativeExceptionalCompactSupportFinite` constructs both integral
boundary isomorphisms for the supplied System, lifts the genuine proper/open scalar
mate through fully faithful derived sections, proves its invertibility by integral
residue Tor and the native scalar-mate theorem, and extends it uniquely through raw
rational localization. All definitions are actual composites or faithful preimages;
none contains a proof hole or chooses undetermined data from existence.

The item chooses these uniquely normalized finite comparisons. Their integral component
formula is exactly the normalization premise of the remaining transition theorem.
The existing
`StageSystem.stageComparison_naturality` then supplies naturality on all common-stage
arrows, and `NatIso.ofComponents` assembles the desired isomorphism.

## Proved and sorry left

Original holes: one, `system_compact_support_realization`.

The new proved helper theorems are `systemSectionMap_isIso`,
`systemIntegralMap_isIso`, and `systemFiniteComparison`. Their data are constructed
by `systemIntegralLocalizationIso`, `systemRationalSource`, `systemIntegralSource`,
`systemIntegralTarget`, `systemSectionMap`, and `systemIntegralMap`. The item also
contains proved private helpers for generic stage assembly and descent with fixed
coefficient changes.

The item now contains no `sorry`. Its finite construction, component invertibility,
raw-localization extension and common-stage assembly are proved in Lean from the
named library statements and the one remaining equation below.

The delivery adds exactly one hole:
`WeilConjectures.LocallyFiniteAdicCompactSupport.systemFiniteTransition`, node
`lem-sf-native-exceptional-compact-support-integral-transition`. It states the
compatibility of a supplied family of finite rational comparisons
with one field inclusion, assuming their components on every integral input equal
the constructed scalar map. It does not construct any finite comparison, prove
invertibility, extend maps to rational arrows or descend them to common-stage arrows.
Its docstring and node give the full normalization-and-mate-pasting argument.

This is a decomposition: one upper hole closed and one strictly smaller hole added,
net zero holes closed among the changed declarations. There are no holes in
definitions and no new axioms.

All three modules compile within 60 seconds per file: finite construction 35.6 s,
transition statement 10.7 s, and the item 11.2 s. The delivery tool rechecks the
exact packet after the final line-length correction.

## No longer needed

No original public imports were removed. No existing module or declaration is
withdrawn, and no global pruning is claimed. Every mathematical ingredient of the
original plan is retained, either directly in the item or through the new modules.
The lifted-closure `StageAction` and chosen-family comparison route is not used:
the finite maps are constructed directly for the supplied System and supplied
Realizations. This does not declare those existing modules globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The existing chosen-family compact-support theorem
cannot be applied verbatim: its coefficient construction uses the lifted algebraic
closure and a StageAction, and its existence statement chooses source and target
realizations. This item fixes arbitrary supplied realizations and an unlifted
System. The direct finite construction preserves these quantifiers.

The remaining calculation is exactly the original proof plan's third step: the
field-transition equality for finite comparisons with the prescribed integral
components. Finite-stage existence, the scalar map and its invertibility, unique
raw-localization extension, and the common-stage assembly are proved separately.

## New nodes

`lem-sf-native-exceptional-compact-support-finite` records the proved finite-stage
construction, invertibility and unique raw-localization extension, including the
explicit boundary and scalar-map definitions. Its module has no holes.

`lem-sf-native-exceptional-compact-support-integral-transition` records only the
remaining field-transition equation for the integral-normalized finite family,
with the same blueprint source and unit as the item. Its hypotheses fix every
integral component to the actual constructed scalar map;
its conclusion is strictly one compatibility step of the argument.

The parent node's proof, proof dependencies and proof origin follow the delivered
construction. Its statement, statement dependencies and Lean declaration record
are unchanged. No change records are needed: no existing interface was changed.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 1 INFRA, 1 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.WeilSheaf.NativeExceptionalCompactSupportFinite": "6dcaa8ef4c1a6471d1d8de554499788001a323c6", "Sheaf.WeilSheaf.NativeExceptionalCompactSupportIntegralTransition": "73fc58058265ba26dd416840b6e531aa2a9d6863", "Sheaf.WeilSheaf.NativeExceptionalCompactSupportRealization": "17a25b85f0301e28f58fc6fe5c531706ecebb504"}, "results": {"Sheaf.WeilSheaf.NativeExceptionalClosureCompactSupport": {"hash": "7d39293f80044355c3fead78b6479b741b5e65eb", "status": "OK"}, "Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitModelComparison": {"hash": "b12486410164b5012881f5f5e168c95901430799", "status": "INFRA"}}, "seconds": 121, "time": "2026-10-28T12:45:27+0800", "transitive": 0, "version": 1}
```

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
