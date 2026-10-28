## What changed

Reduced `WeilConjectures.integralDualizing_support_system_hom_comparison` to
separate geometric and coefficient comparisons. Its signature and both original
public imports are unchanged. The proof chooses the existing base reduction
calculus, lifts the actual integral support functor into the constructible full
subcategory using its constructibility proof, and composes two whiskered natural
isomorphisms. A proved private categorical helper performs the composition on
abstract functors, avoiding costly kernel reduction of the concrete derived
functors. Local irreducibility attributes also keep elaboration from unfolding
these resolution constructions; they do not change any imported interface.
All functor maps and naturality are retained.

The new support theorem concerns constructibility and covariant reduction before
any Hom is taken. The new point theorem concerns arbitrary integral constructible
point complexes and contains no support functor, compactification, or exceptional
inverse image. Neither is the original comparison under a different name.

Read the current server queue, rework, claims, returns and build-error records.
The queue assigns a proof item, not a zero-hole repair, and there is no recorded
build error or rework row for this module.

Validation: all three delivered Lean files compile through lcompile. The final
item compile took 7.0 seconds; the new support and point modules compiled in
6.4 and 5.7 seconds respectively. The original theorem signature is byte-for-byte
unchanged, the new node signature records match their Lean declarations, and
none of the three delivered nodes reaches itself through dependency edges.

## Proved and sorry left

Original holes closed: one, in
`WeilConjectures.integralDualizing_support_system_hom_comparison`.
Its proof is complete relative to the two named intermediate statements.

Holes added: two:

- `WeilConjectures.integralDualizing_support_reduction`
  (`lem-coef-integral-dualizing-support-reduction`), in
  `Sheaf.SixFunctors.IntegralDualizingSupportReduction`.
- `WeilConjectures.point_integral_reduction_hom_tower`
  (`lem-coef-point-integral-reduction-hom-tower`), in
  `Sheaf.SixFunctors.PointIntegralReductionHomTower`.

This is a decomposition, not an unconditional proof or a net hole closure:
one original hole was replaced by two strictly separate steps (net minus one).
The item module itself has zero remaining holes. Each new theorem has exactly
one whole-body `sorry`, a source, a detailed proof in words and a matching node.
No definition or private theorem contains a hole.

## No longer needed

None. No public import or declaration was removed. The former five direct proof
dependencies remain needed by the new intermediate statements: residue Tor and
prescribed support reductions by the geometric step; point reduction, scalar
internal-Hom adjunction and the Hom-tower scalar model by the coefficient step.
The item now directly needs the two new nodes and the existing base-calculus
existence node. Its unit has no realized statement or steps to bypass.

## Where the brief, the DAG or earlier work was wrong

The declared ingredients supply finite projection comparisons, scalar internal
Hom and representative Hom towers. They do not themselves state the two strict
natural functor comparisons needed to connect the published definitions.
Matching evaluated objects and transition equations is not used as a substitute
for constructing a natural system map. The geometric step instead constructs a
reduction counit and tests its evaluations for invertibility; the coefficient
step uses one simultaneous Hom resolution and natural localization comparisons.

Searches used leanfinder, loogle and grep through msearch, and local searches of
the source tree, DAG and newest blueprint. The blueprint reduction-compatibility
lemma concerns finite étale coefficients, rather than these strict integral
proétale functors, and is not a duplicate. Read the signatures of all five original dependencies,
the point reconstruction theorem, the base reduction-calculus theorem, and the
compact-support and Hom-tower definitions. No exact existing comparison was
found. The edge checks are zero input, empty scheme, the first quotient (index
zero, exponent one), and ramified coefficient extensions; no finite Tor or
site-perfect hypothesis has been added to the item.

## New nodes

`lem-coef-integral-dualizing-support-reduction` isolates the geometric
compact-support reconstruction and reduction counit. Its conclusion contains no
internal Hom, coefficient dual, dualizing object or exceptional inverse image.

`lem-coef-point-integral-reduction-hom-tower` isolates the coefficient-point
scalar adjunction and strict Hom-tower model. Its input ranges over integral
constructible point complexes, without a compactification or support operation.
Both nodes retain the original chapter, unit and blueprint ancestor. There are
no changes to existing modules besides the assigned item and no change records.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralDualizingSupportReduction": "ef06cddee2b0bd76945ade1e58511a603e37cf07", "Sheaf.SixFunctors.IntegralDualizingSupportSystemHomComparison": "591c50c5c4ecdb84951bcfb25cf74addbb8a8d89", "Sheaf.SixFunctors.PointIntegralReductionHomTower": "359392b25fdce63da16fc468adf51bc90a987634"}, "results": {"Sheaf.SixFunctors.IntegralDualizingMappingTowerFiniteComponents": {"hash": "385694a7bd729b9dc1480773bff38db570167ea7", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T12:17:19+0800", "transitive": 0, "version": 1}
```

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
