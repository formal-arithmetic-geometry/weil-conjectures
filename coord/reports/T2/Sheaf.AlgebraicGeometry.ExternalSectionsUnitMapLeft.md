## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_externalSectionsUnitOpenTransportLeft`
without changing its statement or the existing definitions. Added the proof-only import
`Sheaf.AlgebraicGeometry.ExternalOpenFactorUnitsLeft`.

Added two modules, each with its own node:
`Sheaf.AlgebraicGeometry.ScalarOpenTensorTransport` proves general scalar-linear transport
of tensor sections along an open immersion, using bijectivity of the open pullback unit
and `module_pullback_tensor`.
`Sheaf.AlgebraicGeometry.ExternalOpenFactorUnitsLeft` constructs the cartesian open map,
the scalar restriction isomorphism and the two coefficient isomorphisms, and proves
both factor-unit formulas by the conjugate-isomorphism unit equations and restriction
naturality. The main theorem combines these formulas with tensor-section transport.

All data are actual constructions. The only existential choices used are the existing
normalized adjunctions and coefficient comparisons, with their unit/section formulas.
No statement, definition or visibility of an existing declaration changed.
The original DAG node now records the proved factor/tensor decomposition.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.exists_externalSectionsUnitOpenTransportLeft`
(node `lem-sc-external-sections-unit-open-transport-left`).

The new theorems are also proved:
`AlgebraicGeometry.Scheme.Modules.exists_scalarOpenTensorTransport`
(node `lem-sc-scalar-open-tensor-transport`) and
`AlgebraicGeometry.Scheme.Modules.exists_externalOpenFactorUnitsLeft`
(node `lem-sc-external-open-factor-units-left`).
There are no `sorry`s in any delivered Lean module. No holes were added or split off.
This is a proof from existing declarations, rather than a decomposition leaving new holes.

The proofs include empty opens/factors and zero modules: the general lemma explicitly
assumes only the open-image and top-preimage conditions, and the factor proof establishes
those conditions by the cartesian square. It uses no quasi-coherence, separation,
compactness or nonemptiness hypotheses.

## No longer needed

No existing imports removed and no modules or nodes pruned. The original plan's four
comparison dependencies remain needed: open-immersion restriction, composite adjunctions,
conjugate-isomorphism unit equations and module-pullback tensor compatibility. Their uses
are now recorded on the two new helper nodes instead of as direct proof dependencies of
the main theorem. `ScalarGlobalSectionsComparison` remains the public statement import.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The generic Mathlib tools recorded by the DAG do fit,
but sectionwise scalar linearity and the restriction transports require explicit glue.
Mathlib search found restriction and adjunction tools, with no assembled theorem.
LeanSearch returned Internal Server Error; LeanFinder, Loogle and local grep succeeded.
The Stacks source was read online because the listed local TeX files are absent here.

## New nodes

`lem-sc-scalar-open-tensor-transport`: a general, proved comparison for arbitrary module
coefficients and supplied coefficient isomorphisms over an open immersion. Its proof uses
unit bijectivity, scalar coefficient linearity, `module_pullback_tensor` and tensor-section
naturality. Module: `Sheaf.AlgebraicGeometry.ScalarOpenTensorTransport`.

`lem-sc-external-open-factor-units-left`: a proved comparison for the two individual factor
units under first-factor open base change, before tensoring coefficients or sections.
Module: `Sheaf.AlgebraicGeometry.ExternalOpenFactorUnitsLeft`. Neither helper restates the
original external-product theorem. Both inherit its chapter and unit; no unit route changes.

## Second reading by T2

1. PASS: Compared every delivered module with the repository. Only the original
   module already exists; its definitions, declarations, visibility and signatures
   are unchanged. Its sole new import is proof-only. Restored one extra space before
   the final theorem's `:=` so its signature remains byte-for-byte unchanged.
2. PASS: Read all three modules and checked the unit, mate and restriction equations.
   Each compiles locally. No delivered module contains `sorry`, a custom axiom,
   unsafe/opaque/extern/implemented_by declarations, or hollow data. A scratch probe
   printed axioms for the original theorem and all five new public declarations:
   each uses exactly `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.
   The chosen normalized adjunction and scalar coefficient map have section formulas
   determining them; the tensor comparison is constructed by its already-proved
   upstream theorem. No arbitrary witness from an unproved existence is used.
3. PASS: No open statement is split off. The two new theorems are proved and strictly
   separate parts of the original argument: a general tensor transport and untensored
   factor-unit transport. Checked identity/open-top cases, empty opens and factors,
   and zero coefficients: all conditions and formulas remain valid without extra
   assumptions. Fresh LeanFinder and Loogle queries for open-immersion section tensor
   transport and adjunction-unit uniqueness, plus local searches for tensor transport
   and restriction-unit formulas, found the generic tools already used, not duplicate
   assembled helpers. Their docstrings explain the complete constructions and proof.
4. PASS: Read from the original theorem downward through both helpers and the existing
   unit/tensor comparisons. No shorter assembled library result was found. Each import
   supplies statement data or proof tools: the helper's public imports are needed by
   its signatures, while PullbackUnit and PullbackCarrier are proof-only. The old
   comparison dependencies remain used transitively, as listed in No longer needed;
   no node or module can be pruned by this proof. The unit sk-prop-av-cube and its
   realized record are untouched, and its route is not bypassed.
5. PASS: Compared all three nodes with the Lean statements and proof steps. The main
   node records exactly the factor/tensor reduction; the helper nodes record unit
   bijectivity, scalar linearity, tensor compatibility, the conjugate-isomorphism unit
   equations and restriction naturality. New nodes have their source, searches,
   creation/blueprint/Lean records, chapter and unit. No forbidden existing-node field
   is changed by the delivery.

Second reading changed only the extra signature whitespace and this review report.
One original hole is closed, zero holes are added, and zero modules are pruned.
