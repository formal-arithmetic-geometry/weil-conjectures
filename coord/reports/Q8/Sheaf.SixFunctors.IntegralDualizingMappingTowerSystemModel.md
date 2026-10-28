## What changed

Replaced the sorry in `integralDualizing_mapping_tower_system_model` by a complete
Lean assembly from two independent parts of its stated argument. The theorem's
signature and all existing public imports are unchanged.

`NormalizedDVRQuotientSystemRealization` states the geometric part: a strict
quotient-system complex, coherent finite identifications, and an isomorphism of
its completed restriction with the prescribed strict tower. It has no Hom
comparison or quantification over coefficient calculi.

`CoefHomScalarNaturality` states the scalar part for a prescribed Q, naturally on
the whole completed-coefficient input derived category. It constructs no quotient
model and mentions neither a normalized DVR tower nor constructibility.

The actual assembly maps the tower isomorphism through the inverse sequence
realization and the covariant second argument of curried internal Hom, then
whiskers with constant input and sections. It composes this with scalar naturality
and restricts to constructible inputs. This is a decomposition, not a net proof.
The original unused geometric assumptions are retained; only their linter warning
is disabled. No existing definition, instance or other module is modified.

## Proved and sorry left

Original holes: 1. Its local body is closed:
`WeilConjectures.integralDualizing_mapping_tower_system_model`
(node `lem-coef-integral-dualizing-mapping-tower-system-model`).
Fully closed mathematical obligations: 0; decomposed obligations: 1.
Added holes: 2, precisely:

- `WeilConjectures.normalizedDVR_quotient_system_realization`
  (`lem-coef-normalized-dvr-quotient-system-realization`).
- `WeilConjectures.coefHom_scalar_naturality`
  (`lem-coef-hom-scalar-naturality`).

Each has its own module, exact statement, source, edge-case discussion, and full
proof in words. The item itself has zero sorry; the two new modules each have one
named theorem with body exactly `:= by sorry`. There is no new definition or axiom.
The raw hole delta is 1 closed minus 2 added = -1. This is not reported as net
proof progress. All three files compile under the 60-second per-file limit.

## No longer needed

No import was removed and no module or node is claimed globally pruned.
The original direct proof dependencies `def-weil-abstract-derived-category`,
`def-coef-normalized-dvr-tower`, `lem-weil-pbc-sequential-tower-evaluation-full`,
`lem-coef-hom-tower-scalar-model`, and
`lem-coef-derived-system-evaluation-calculus` are now dependencies of the two
smaller constructions instead of the parent's assembly. They remain needed there.
The sole existing public import `IntegralDualizingMappingTower` is retained.
The two new proof imports are both used. The unit route remains unchanged.

## Where the brief, the DAG or earlier work was wrong

The original plan named roofs, sequential fullness and scalar Hom adjunction but
had no declaration combining their source/target comparison functors into the
required quotient-system model or the natural scalar comparison.
`coefPairingHomRepresentativeComparison` supplies objectwise nonempty
isomorphisms and finite evaluation comparisons; it does not supply naturality of
the first comparison. Fullness for one fixed tower does not justify choosing
lifts naturally in a varying Hom input. The two statements isolate these distinct
gaps without asserting faithfulness or functorial choices of tower lifts.

Mathlib searches found `DerivedCategory.right_fac` for the roof step and
`Adjunction.leftAdjointUniq` for the reduction comparison, but no complete match.
The existing finite-model recursion and strict-system/sequence-site equivalence
were read as reusable constructions for the first gap. The scalar-Hom theorem
was read for the second gap. This delivery does not claim to finish either gap.
Zero complexes, the empty scheme, and equal indices are explicitly covered by
the proposed arguments. No target statement or definition has changed.

## New nodes

`lem-coef-normalized-dvr-quotient-system-realization` separates the geometric
realization and fixed-tower comparison (original steps 1--2) from all scalar Hom
claims. The completed restriction isomorphism is needed for the actual transport
in the assembly, and is not a substitute for the original mapping-functor claim.

`lem-coef-hom-scalar-naturality` separates the sequence scalar-adjunction argument
(original step 3), on a prescribed quotient complex and all derived inputs, from
construction of that complex. It contains no existential quotient realization.

The parent node's proof, proof dependencies and proof origin follow the Lean
assembly. No change record is required: no existing signature or definition is
modified, and no other existing module or node is edited.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefHomScalarNaturality": "125b3dbe475dc14d6bb07136ef64cb9d3b5dc3b2", "Sheaf.SixFunctors.IntegralDualizingMappingTowerSystemModel": "e6c4671bc7f55f926d8d4e475cda6c011663035a", "Sheaf.SixFunctors.NormalizedDVRQuotientSystemRealization": "2f30d33af8e2120846682c95486469e661bf7eff"}, "results": {"Sheaf.SixFunctors.IntegralDualizingMappingTowerFiniteComponents": {"hash": "385694a7bd729b9dc1480773bff38db570167ea7", "status": "OK"}}, "seconds": 95, "time": "2026-10-28T12:05:14+0800", "transitive": 0, "version": 1}
```

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
