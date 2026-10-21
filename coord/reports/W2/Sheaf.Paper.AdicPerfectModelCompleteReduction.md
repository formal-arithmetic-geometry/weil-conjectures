## What changed

Proved `AlgebraicGeometry.Scheme.adicPerfectModel_complete_reduction` in
`lean/Sheaf/Paper/AdicPerfectModelCompleteReduction.lean`, retaining every public
statement and definition. All added helpers are private and proved. The residue
comparison is constructed from adjunction uniqueness and the normalized constant
scalar-extension comparison. Completeness is proved directly by the
multiplication-difference criterion on finite quotient limits and finite-projective
retracts. The argument includes every slice using the iterated-slice equivalence.
Updated the existing node's proof, proof dependencies, and proof origin to this route.
No other Lean module, public interface, definition, or target is changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.adicPerfectModel_complete_reduction`
(node `lem-sfb-adic-perfect-model-complete-reduction`).
There are zero `sorry` declarations left in the item and zero holes added anywhere.
No statement is split off. Existing declared proof dependencies are used as intended.

## No longer needed

Removed direct proof imports:

- `Sheaf.Paper.ConstantModuleSectionProperties`
- `Sheaf.Paper.RestrictionLocalCompleteness`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`

The proof no longer cites the corresponding nodes
`lem-weil-pbc-constant-module-section-properties`,
`lem-weil-pbc-restriction-local-completeness`, and
`lem-weil-proetale-weakly-etale-localization` directly. Completeness is proved over
the completed ring itself from its finite quotient cone, avoiding both coefficient
ULift transport and the extended-ideal scalar-restriction comparison. Iterated slices
are handled by their explicit equivalence with a single slice. These are item-level
prunings only; declarations and modules used elsewhere are retained. The tensor
product definition is supplied by the scalar-extension and flatness interfaces, so
`def-pur-sheaf-tensor-product` is no longer a separate proof dependency.

The proof retains `TorsionLimitSheafCompleteness` for its proved geometric-series,
natural-transformation limit, and nilpotent multiplication helpers. It retains
`LocalizedSiteTensorRestriction` for its proved slice-sheafification comparison,
including the unit equation. No source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The planned torsion-limit theorem uses a
ULift coefficient presentation, whereas this item uses the original coefficient
ring. A direct multiplication-difference proof avoids that transport and proves
the same kernel-completeness predicate. The residue isomorphism works for every
complex through composition of extension adjunctions; finite projectivity is needed
for completeness and K-flatness, not for constructing that isomorphism.
The finite-homology proof uses the Noetherian quotient and does not need to install
a field structure from maximality. Bounds follow from zero actual terms, including
the empty interval. No new nodes are needed. The change record
`coord/changes/W2-adic-perfect-model-proof-commands.md` documents proof-local
command additions flagged by the conservative interface check; the public API is unchanged.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
