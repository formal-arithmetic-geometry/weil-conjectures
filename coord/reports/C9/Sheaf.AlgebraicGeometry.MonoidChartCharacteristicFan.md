## What changed

Replaced the hole in `AlgebraicGeometry.monoid_chart_characteristic_fan` with a proof
combining two strictly smaller source subarguments. The original theorem signature
and its definitions are unchanged.

`MonoidChartCharacteristicStalks` states the descent and normalized ordinary/geometric
characteristic comparisons (original proof Steps 1 and 3). It also contains the three
original helper definitions, relocated verbatim and publicly re-exported by the item.
`MonoidChartCharacteristicFanMap` states the basic-open gluing construction and its
stalk formula (original Steps 4 and 5), assuming the supplied Zariski chart and ordinary
stalk equivalences. It does not assert the geometric comparison or all-prime saturation.

The item proves localness from bijective stalk maps and sharpness from the normalized
Associates equivalences. It constructs the restriction equivalences using the final
neighborhood functor for an open inclusion, verifies that the resulting inverse is
the actual `FineFan.stalkMap`, and deduces the geometric restriction equation.
Independently, it proves saturation and torsion-freeness for every affine-fan stalk
from `affineFan_localization_sections` and `face_sharpening`: transport through the
canonical group-completion equivalence, and use the finite integer basis to exclude
torsion. This includes primes outside the scheme image.

The compatibility record is `coord/changes/monoid-chart-characteristic-helper-location.md`.
No direct Lean consumers currently import the item; no other existing module is changed.
The original theorem signature and the relocated definition text were compared verbatim.
All three modules compile cleanly with `lcompile.py`; the final item compile took
15.3 seconds, below the 60-second limit. Delivery performs the axiom and hole probes.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.monoid_chart_characteristic_fan`
(node `lem-trf-monoid-chart-characteristic-fan`). Zero holes remain in the item.
The private lemmas `sharp_face_stalk_properties` and
`open_restriction_stalk_bijective` have complete proofs.

Added exactly two holes, each the entire proof of one public theorem:

- `AlgebraicGeometry.chart_characteristic_stalk_comparison`, node
  `lem-trf-chart-characteristic-stalk-comparison`.
- `AlgebraicGeometry.chart_characteristic_fan_map`, node
  `lem-trf-chart-characteristic-fan-map`.

This is a decomposition: one original hole closed, two lower holes added, net -1;
it is not a claim that the full theorem is independent of sorry. The two statements
are separate parts of the original source argument, and the proof joining them also
supplies locality, sharpness, restriction compatibility and the all-prime clause.

## No longer needed

Removed the direct proof imports of
`Sheaf.AlgebraicGeometry.ZariskiPrelogLogificationComparison`,
`Sheaf.AlgebraicGeometry.AssociatedLogUniversalStalks`,
`Mathlib.CategoryTheory.Sites.ConstantSheaf`, and
`Sheaf.CategoryTheory.Sites.GeometricMorphism` from the item. Their role belongs to
the characteristic-stalk subargument; they are still recorded in that new node's
proof dependencies and are not claimed globally pruned.

The item's proof dependencies are now the two new nodes,
`def-trf-fine-fan-blowup`, `lem-trf-affine-fan-localization-sections`, and
`lem-trf-fs-face-sharpening`. The original constant-sheaf, monoid-sheafification,
geometric-morphism, associated-log and prelog-comparison dependencies are no longer
direct steps of its proof. No existing module is withdrawn and no mathematical node
is claimed globally unnecessary. The original three public imports are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or found false. The original node's Steps 1
and 3 require the constant-chart universal-property glue and normalized pushout
quotient calculation, which are not immediate applications of the existing large
comparison theorem. Steps 4 and 5 require a sheaf morphism on basic opens and its
actual stalk normalization. These are the two explicitly stated subarguments.

Mathlib's general `PresheafedSpace.ofRestrict_stalkMap_isIso` assumes all colimits
in the value category. The project provides filtered colimits for `CommMonCat`.
The proof therefore uses its final-neighborhood argument directly, with the existing
filtered-colimit stalk and stalk-map definitions; it adds no colimit axiom or instance.

Read ILO VIII pp.98--100 and 106--108, the original node and dependency declarations,
and the latest blueprint unit. The unit has no realized statement or step assigned
to this node, and the proof retains the original logarithmic chart route. Edge cases
checked: the empty scheme is vacuous; a group chart and the all-unit face yield the
trivial characteristic; the empty prime is retained; restriction to the empty open
is vacuous; torsion-freeness is asserted only for positive exponents.

Mathlib searches via LeanFinder, LeanSearch, Loogle and grep found ordinary ringed-space
analogues and the restriction-stalk API, but no logarithmic characteristic comparison
or matching sharp-monoid-spectrum construction. Existing chart-face logification
results concern already localized geometric stalks and do not provide descent or the
specified ordinary characteristic sheaf. No source-library declaration is modified.

## New nodes

`lem-trf-chart-characteristic-stalk-comparison` carries the original Steps 1 and 3,
including the actual numerator and all-local-section germ equations. It has no fan
morphism, restriction witness, or all-prime saturation clause. Its module also carries
the relocated original definitions.

`lem-trf-chart-characteristic-fan-map` carries Steps 4 and 5, with the ordinary
normalized stalk identifications supplied as hypotheses. It constructs only the
point/sheaf morphism, its bijective stalk maps and the numerator formula. It neither
constructs the Zariski log structure nor asserts any geometric comparison.

Both nodes inherit the original chapter and unit, cite the original ILO places,
record actual three-kind Mathlib searches, and give complete proofs in words.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
