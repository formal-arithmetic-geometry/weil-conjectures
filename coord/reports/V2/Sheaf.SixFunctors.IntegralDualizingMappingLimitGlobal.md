## What changed

The original theorem keeps its exact signature and public import. Its proof now composes
three natural isomorphisms, using whiskering and the functor associator. The new comparison
imports are private proof imports.

IntegralDualizingMappingTower constructs both intermediate functors explicitly. The source
uses constant-ring sequence modules, derived internal Hom and tower-valued derived sections.
The coefficient functor uses closed Hom from the derived constant complex into the existing
positive quotient tower. A canonical localization equivalence compares its small-Hom model
with the standard tower localization. There is no data selected from an unproved existence
assertion, no new axiom, and no sorry in a definition.

All five Lean files compile together in import order through lcompile.py. The respective
compile times were 9.1, 6.5, 7.0, 7.4 and 7.8 seconds. No existing module besides the assigned
item was changed, and no existing statement, definition or public import was changed.

## Proved and sorry left

This is a decomposition, not a completed mathematical proof. The one original hole in
WeilConjectures.integralDualizing_mapping_limit_global is replaced by a complete Lean proof
from the following three new, strictly smaller obligations. Thus one original hole is closed
syntactically, three holes are added, and no net hole reduction is claimed (net -2).

- WeilConjectures.integralDualizing_mapping_tower_limit, node
  lem-coef-integral-dualizing-mapping-tower-limit: the formal comparison between mapping
  into the given Roos limit and the derived limit of its strict mapping tower. It assumes
  neither a finite dualizing identification e nor the compatibility he and concludes no
  geometric duality.
- WeilConjectures.integralDualizing_mapping_tower_finite_comparison, node
  lem-coef-integral-dualizing-mapping-tower-finite-comparison: the geometric finite-adjunction
  comparison before inverse limit. It has no integral limit object M or presentation hM,
  and its conclusion is an isomorphism in the derived category of strict towers.
- WeilConjectures.integralDualizing_coefficient_hom_tower_limit, node
  lem-coef-integral-dualizing-coefficient-hom-tower-limit: the purely algebraic coefficient
  comparison, with no scheme, compact support or dualizing object. It is natural on the
  entire unbounded coefficient derived category.

These are all remaining holes in the delivery. Their proofs are exactly `by sorry`, and
each has its source and complete proof in words in its docstring and node. Zero holes
remain in the assigned module and in the construction module.

## No longer needed

No existing import, module or node is withdrawn. The original node had no proof_deps;
its former unstructured proof paragraph is replaced by the three explicit comparison
steps. The existing Roos model public import is retained because the signature needs it.
No unit route is bypassed; the unit's realized statement and steps lists are empty.

The theorem coefTowerNaturalCurrying is not used as a proof dependency. Its module is
imported for the already constructed quotient tower, tower instances and coefficient
localization conventions, so that module is not claimed as pruned. Likewise the construction
uses the existing constant-ring Hom definitions rather than duplicating them.

## Where the brief, the DAG or earlier work was wrong

The original node left its whole mapping-tower comparison as a single non-elementary
step with no named dependencies. Its formal passage to limits, geometric finite-adjunction
comparison and pure coefficient reconstruction are separate arguments and now have explicit
Lean endpoints. The three comparison theorems are genuine parts of that displayed chain,
rather than the original assertion renamed or with a hypothesis repackaged.

Preflight exposed an existing cycle through the broader finite-mapping, trace and pairing
nodes. These stronger theorem statements are not prerequisites of the new comparison:
its proof plan constructs the coherent map directly from the finite exceptional counits,
finiteDualizingCoefficientComparisons, scalar adjunction and simultaneous resolutions.
The new quotient-tower definition node records only the actual existing data, so the
construction does not acquire the entire natural-currying theorem as a prerequisite.

The existing coefTowerNaturalCurrying theorem is marked STATEMENT-DISPUTED in its source:
its arbitrary eTrace need not preserve the exceptional counit. This delivery does not invoke
that conclusion. The finite comparison proof plan instead constructs the trace from the
actual counits pinned by e and he, as specified in the paper. This is still an unproved step,
not a claim that finite evaluation alone supplies a coherent natural map.

Closed Hom on the standard, larger-Hom derived tower localization does not synthesize from
the existing closed-derived-category instance, which uses the Grothendieck universe. The
construction therefore computes closed Hom in the existing small-Hom localization and
uses uniqueness of localization to return to the standard model. No shared instance is
changed, and no transparency option is disabled in the new modules.

Edge cases were checked mathematically: zero input and empty scheme give zero complexes;
index zero means exponent one; no global Tor interval over all inputs is assumed; and the
coefficient comparison uses resolved split transitions, not surjectivity of Hom applied to
arbitrary quotient maps. Its unbounded claim follows from the K-flat/K-injective model.

## New nodes

- def-coef-integral-dualizing-mapping-towers records the explicit constructions and the
  canonical comparison between their localization models. It contains no proof hole.
- lem-coef-integral-dualizing-mapping-tower-limit records formal global Hom/limit transport
  for the prescribed presentation.
- lem-coef-integral-dualizing-mapping-tower-finite-comparison records geometric finite
  adjunction at the strict tower level, before taking limits.
- lem-coef-integral-dualizing-coefficient-hom-tower-limit records pure coefficient
  reconstruction for all coefficient complexes.

No change record is required: only the assigned module, its own node, and new modules and
nodes are changed. The independent delivery review remains required for the new statements.

- def-coef-integral-dualizing-quotient-tower attaches the existing actual quotient-tower
  definition separately from the disputed natural-currying theorem. No existing Lean
  declaration or module is changed by this attachment.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralDualizingCoefficientHomTowerLimit": "058bb132f8a3c2d0876515b85b14124f5d517b17", "Sheaf.SixFunctors.IntegralDualizingMappingLimitGlobal": "367a4fa0e399dfdcb64bb4c9895586c6026e2ea5", "Sheaf.SixFunctors.IntegralDualizingMappingTower": "07eabf7461c4984dac7cdddeee3d70a19a647ee1", "Sheaf.SixFunctors.IntegralDualizingMappingTowerFiniteComparison": "5d7416ccc7b12a5397c6a4a430662f92adb49adc", "Sheaf.SixFunctors.IntegralDualizingMappingTowerLimit": "84e90ff0df39c252baad265a10884e582fbe1920"}, "results": {}, "time": "2026-10-28T06:49:52+0800", "transitive": 0, "version": 1}
```

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
