## What changed

Replaced the hole in
`AlgebraicGeometry.ProEtale.CondensedRing.coefficientPush_isIso_of_filtered_flat_legs`
by the categorical assembly of the canonical restricted-mate comparison and the
filtered cohomology cocones. Private proved helpers establish projection naturality,
invertibility at a cocone vertex from invertible stage components, and conservativity
of an exact derived restriction functor.

The canonical balanced tensor presentation is explicit data in
`Sheaf.Paper.CanonicalCoefficientTensorNormalization`; the original tensor-iso
definition reuses its derived component. This shares the expensive construction,
without changing its type or canonical map. The change record is
`coord/changes/C5-canonical-coefficient-tensor-sharing.md`. No source-library
module, target signature, unit statement or unit route changes.

Two separate missing interface results are stated in new modules. One relates the
fixed canonical tensor and regular-pullback constructions to the normalization
required by the existing restricted-mate theorem. The other records the two
cohomology colimit universal properties, including their actual cocone legs.
Neither assumes the stage projections invertible or concludes the coefficient
push comparison invertible. The parent proves that implication and the leg formula.

## Proved and sorry left

Original item: one hole, in
`AlgebraicGeometry.ProEtale.CondensedRing.coefficientPush_isIso_of_filtered_flat_legs`.
Its proof now has no `sorry`. This is a decomposition, not a net proof gain.

Two holes are added and remain, each as a whole public theorem with a source,
proof in words and its own DAG node:

- `AlgebraicGeometry.ProEtale.QuotientChange.canonicalCoefficientTensorNormalization_normalized`
  (`lem-sfb-canonical-coefficient-tensor-normalization`).
- `AlgebraicGeometry.ProEtale.CondensedRing.filtered_flat_tensor_cohomology_cocones`
  (`lem-sfb-filtered-flat-tensor-cohomology`).

Thus the packet closes one upper hole and adds two strictly smaller obligations:
one decomposition, net minus one hole before closure/import-baseline accounting.
All definitions are explicit and contain zero holes; no arbitrary data are chosen
from a mere existence theorem.

Validation: the item compiles cleanly with no warnings (17.6 seconds). Both new
supporting modules compile (40.3 and 39.3 seconds). The original theorem signature
is verbatim unchanged. The first delivery preflight compiled the packet and refused only the missing
LeanSearch search-kind records on the new nodes. Those searches have now been
run and recorded; they found ordinary module and abstract colimit results, with
no matching derived internal-module interface.

Both new Lean statements match their node records; the
combined dependency closure has no cycles or missing nodes. All Lean lines meet
the 100-character limit.

## No longer needed

Removed these eight private proof imports from the item:

- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `WeilConjectures.Algebra.Homology.FilteredColimitsTensor`
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`
- `Sheaf.Paper.RingedComparisonTensorAdjunction`
- `Sheaf.Paper.CondensedQcqsPushforwardContinuity`
- `Sheaf.Paper.CondensedQbarExchangeRightAdjunct`
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`

The parent no longer directly uses
`lem-sfb-flat-coefficient-square-normalization`,
`lem-sfb-bounded-flat-tensor-continuity`,
`lem-pc-module-filtered-colimits-tensor`,
`lem-weil-pbc-ring-sheaf-change-adjunction`, or
`lem-weil-pbc-ringed-projection-mate-exact` as proof dependencies. Their roles are
now either in the two supporting interface results or in the elementary proved
parent helpers. Several remain transitively needed elsewhere, including by the
restricted-mate theorem. No entire module is claimed globally pruned or withdrawn;
all original public imports remain. The canonical normalization module is a new
public import because the shared definition uses its explicit data.

Removed the unused prospective SingleFunctor proof import from the new normalization
module and the prospective BoundedFlatTensorContinuity and
CondensedQcqsPushforwardContinuity proof imports from the new cohomology statement
module. Their DAG proof plans retain the actual mathematical dependencies; a worker
proving those statements imports the declarations it uses.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies supply the mathematical routes, but their current Lean
interfaces leave two bridges unstated. The restricted-mate theorem takes arbitrary
TensorNormalization data together with TensorNormalized proofs. The item instead
fixes Mod.residueDerivedTensorIso. No existing declaration found proves the required
normalization for that fixed presentation. Also, its regular pullback is constructed
with the standard monoidal pullback, whereas the fixed residue comparison uses a
transported monoidal structure. Equality of their ordinary unit maps must be proved;
the new normalization node explicitly includes that calculation.

The bounded continuity theorem is phrased for strict section-module representatives
and localized colimit comparisons. The parent needs universal properties after
internal-module homology. The new cohomology statement isolates exactly this
transport and exact-colimit calculation. It keeps the common lower bound needed by
HRS Lemma 5.3(1); no arbitrary derived-category colimit is asserted.

Read the current blueprint under `literature/blueprint/latest/` and HRS page 14,
Lemma 5.3(1), comparison (5.4). Searches were made with all three required msearch
modes, including LeanSearch, and logged in searches.jsonl. The generic IsColimit cocone-points isomorphism
was used for the parent assembly; no Mathlib statement matches the geometric
normalization or cohomology-cocone interfaces. Repository duplicate searches found
neither new statement. Edge cases checked mathematically: zero coefficient modules,
empty schemes, identity f/a, and a singleton presentation. No counterexample or
statement weakening was introduced.

## New nodes

`lem-sfb-canonical-coefficient-tensor-normalization` states the computation-counit
normalization of explicit canonical scalar-tensor data and equality of the two
canonical exact-single regular pullback maps. It is valid without flatness of a
coefficient extension. Its source calculation uses balanced coprojections, the
left-derived counit factorization, quotient monoidality and the ordinary unit map.
Its module also constructs the canonical data explicitly.

`lem-sfb-filtered-flat-tensor-cohomology` states the two actual homology-colimit
universal properties for flat coefficient presentations and bounded-below K. It
follows the strict representative and qcqs continuity route already in the node,
without mentioning a coefficient algebra or any projection invertibility. The
parent's naturality and conservative-isomorphism argument remains real Lean.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
