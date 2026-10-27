## What changed

Proved `SheafOfModules.StrictScalarHom.exists_sliceScalarHomChainAdjunction` with its
original statement and all three public structures unchanged. Reused the independently
proved canonical data underlying `exists_scalarHomChainIdentification` for the chain
isomorphisms. Derived theta's
inverse normalization using its inverse law and S-linearity of the actual Hom coordinate.

Reused the already proved private ordinary-extension, Hom-equivalence, and adjunction
helpers from `StrictScalarHomChain` with a private `import all`; transported that
adjunction to the prescribed extension and proved its normalization. Constructed the scalar-extension comparison under every continuous
cocontinuous restriction. Its sheafification comparison is locally bijective by cancellation
of the local unit from the restricted global unit. The presheaf tensor comparison, unit
naturality, generator extensionality, and inverse-isomorphism laws prove the required
natural slice comparisons and both pure formulas. No new public declarations were added.

Updated the node's proof route and dependencies. The proof-only command change record is
`coord/changes/slice-scalar-hom-adjunction-proof.md`. No consumer is adapted.

The completed module compiled without warnings in 28.5 seconds. The restriction
comparison is a named morphism with an explicit equation and a separate proof of
invertibility; its pure-tensor equation is proved before constructing its inverse.
The generic natural comparison is specialized to slices and further slices. The
canonical ordinary extension is used directly, avoiding object-equality transports
in the final assembly. All private helpers have complete proofs.

All three public structures and the theorem signature remain unchanged. No consumer
adaptation is needed. Delivery performs the final compilation and axiom probe.

## Proved and sorry left

Closed 1 of 1 original holes:
`SheafOfModules.StrictScalarHom.exists_sliceScalarHomChainAdjunction`
(node `lem-sfb-slice-scalar-hom-chain-adjunction`).

Zero holes remain in the item; zero holes added; zero split off. All private helpers
have complete proofs. The reused strict chain constructions are fully proved, and the final
axiom check verifies that no hidden sorry dependency remains.

## No longer needed

Removed the private proof imports `Sheaf.Algebra.Homology.SliceModuleSheafification`
and `Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`. Their corresponding
nodes `lem-weil-pbc-slice-module-sheafification` and
`lem-pur-sheaf-ring-coefficient-ordinary-adjunction` are no longer used by this proof.
Removed their two obsolete top-level `tool_uses` approvals from this node.
Their respective same-small-universe and HasSheafify interfaces do not match the item's
independent universes and HasWeakSheafify assumptions; the direct proofs use the module
Hom equivalence and module sheafification API without strengthening those assumptions.

The old direct proof dependencies on `def-pur-sheaf-tensor-product` and
`def-pur-sheaf-hom` are subsumed by the existing strict scalar-Hom theorem. They remain
needed transitively and as appropriate statement dependencies. The bare tensor-product
node `def-weil-pbc-module-tensor-product` is replaced by the precise scalar-extension Hom equivalence and the scalar generator
API. No module is withdrawn or claimed globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The strict scalar-Hom parent has since been proved independently and no longer imports
this item. Its current DAG proof also has no edge back to this item. Reusing its nu/theta
clauses therefore gives a valid shorter route without a cycle or a new unproved witness.
The remaining ordinary and further-slice adjunction data are constructed here, not merely
repackaged under a new existence statement. No unit-level route is bypassed: the unit's
realized statement and two steps concern restricting the ambient derived functors and
adjunctions, and do not prescribe this helper's internal proof route.

Read Stacks sites-modules.tex at lemma-sheafification-presheaf-modules (03CY),
lemma-adjointness-tensor-restrict (03CZ), section-localize (03DH), and
definition-localize-ringed-site (04IX). Repeated LeanFinder, Loogle and grep searches in this session found only ordinary
module adjunctions, generic sheafification comparisons and the slice restriction API;
none directly states this normalized slice-and-chain package. Checked the formulas for identity coefficients, zero
modules/rings, arbitrary characteristic, arbitrary unbounded complexes and arbitrary
module sheaves on a slice: the argument uses no nonzero scalar, division, boundedness,
flatness, or global-origin assumption on such a module.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
