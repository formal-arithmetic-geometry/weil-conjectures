## What changed

Restored the assigned quarantined source verbatim before editing its proof. The theorem
`WeilConjectures.sfCompactSupportFiniteScalarMateNormalization` retains its entire signature,
its docstring and its two public imports. Its proof imports two new calculation modules.

The proof transports the completed mixed-unit Hom bijection at the integral compact-support
output through the inverse fixed reduction isomorphism, using `Iso.homCongr`. It then uses
injectivity of the resulting Hom equivalence to identify the finite mate. Substitution of
`hb`, the realized scalar transpose equation, and cancellation of the fixed reduction
isomorphism finish the proof. No comparison data or integral isomorphism is newly chosen.

The two new obligations separate the node's original two calculations: the generic finite
universal property of the prescribed completed mixed unit, and the transpose equation for
the explicit realized proper/open scalar map. The latter assumes neither an isomorphism b
nor a Hom bijection and does not assert invertibility. The former has no compactification,
compact-support operation or comparison b. They are strictly different parts of the argument.
The original node's proof and proof dependencies are updated accordingly.

## Proved and sorry left

Original holes: 1. The original hole in
`WeilConjectures.sfCompactSupportFiniteScalarMateNormalization`
(node `lem-sf-compact-support-finite-scalar-mate-normalization`) is replaced by a complete Lean
combination proof. The item itself has zero holes.

Added holes: 2, each the whole proof of a public theorem in its own new module:

- `WeilConjectures.sfMixedCompletedReductionHomBijective`, node
  `lem-sf-mixed-completed-reduction-hom-bijective`.
- `WeilConjectures.sfCompactSupportRealizedScalarTranspose`, node
  `lem-sf-compact-support-realized-scalar-transpose`.

This is a decomposition, not a completed proof from previously stated dependencies;
1 original hole is closed and 2 strictly smaller calculation obligations are added.
No other existing module is changed. All three delivered Lean files compiled in import order; after fixing the combination
proof, the assigned item compiled cleanly in 11.0 seconds. The generic mixed-unit theorem
and the realized-transpose theorem also elaborated successfully in the preceding all-files
compile. The delivery preflight rechecks the complete packet and probes its axioms.

## No longer needed

None: no imports, existing declarations or modules are withdrawn. The direct proof
references to `lem-pur-coefficient-extension-reduction-model`,
`def-weil-mixed-reduction-unit`, `lem-pur-sheaf-ring-derived-coefficient-adjunction`,
`lem-weil-strict-roos-comparison`, `lem-coef-normalized-dvr-effectivity` and
`def-weil-system-operation-exchange-realization` move into the two calculation nodes;
they remain needed there. The finite-action dependency remains directly used, and
`def-weil-compact-support-coefficient-action` records the finite mate's defining equivalence.
The unit `sk-def-sf-operations` has no realized proof steps bypassed by this decomposition.

## Where the brief, the DAG or earlier work was wrong

The source was listed in `coord/rework.tsv` after build quarantine. Its archive and current
Lean attachment have been preserved; absence from the live library was not treated as a
withdrawal. There is no active return for this item in `coord/returns/T8.md`.

The existing declarations provide the constituent coherent reductions and adjunctions, but
no public theorem directly identifies the specified `sfMixedCompletedReductionUnit` with
the finite scalar-adjunction unit or states the proper/open realized transpose equation.
The analogous strict direct-image implementation has additional properness/separatedness
requirements and does not supply a matching compact-support lemma here. These are the two
gaps isolated, with the original sources and proof steps retained in the new nodes.

Edge cases checked in the statement design: n=0 denotes exponent 1, not a zero quotient;
identity coefficient extension still includes the completion augmentation; arbitrary
unbounded targets remain quantified; ramified quotient maps need not be flat; and no
faithfulness of derived finite evaluation or existence/invertibility of the realized scalar
map is asserted by either calculation. The statement of the assigned theorem is unchanged.

## New nodes

`lem-sf-mixed-completed-reduction-hom-bijective`, module
`Sheaf.Paper.MixedCompletedReductionHomBijective`, states the generic completed mixed-unit
Hom bijection, before compact-support reduction transport. Its proof plan uses coherent
coefficient reduction, the normalized derived adjunction, strict Roos augmentation and
effectivity, exactly the first calculation of the original node.

`lem-sf-compact-support-realized-scalar-transpose`, module
`Sheaf.Paper.CompactSupportRealizedScalarTranspose`, states the transpose equation for the
explicit ambient realized proper/open scalar map, before any Hom-bijection uniqueness
argument. Its proof plan uses actual counit naturality, projection-normalized compact
realization, tensor-unit normalization and proper/open mate pasting.

No change record is needed: no existing signature, definition, instance, attribute or
public import is changed.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
