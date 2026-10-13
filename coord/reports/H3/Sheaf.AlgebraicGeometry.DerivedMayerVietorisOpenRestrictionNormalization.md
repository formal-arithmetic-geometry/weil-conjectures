## What changed

Replaced the proof of `AlgebraicGeometry.schemeMVOpenRestriction_unit_normalization`.
A proved private helper calculates the four canonical comparison factors for arbitrary
additive functors with exact source and target restriction functors. The scheme theorem
specializes that calculation, using open restriction's K-injectivity preservation.
Statements, definitions, visibility, and existing imports are unchanged.

The calculation follows the node's existing proof: apply the right-derived unit
factorization equations, use naturality of the exact-target comparison, cancel the
exact-source localization factors, and identify the homotopy composition comparison.
No K-injectivity assumption is imposed on the homotopy object.

## Proved and sorry left

Closed one original hole (full-module compilation passed): `AlgebraicGeometry.schemeMVOpenRestriction_unit_normalization`
(node `lem-pc-derived-mayer-vietoris-open-restriction-normalization`).
The private helper `AlgebraicGeometry.restriction_unit_normalization` is proved.
No holes added, no split statements, and no `sorry` remains in the delivered module.

## No longer needed

None. Both public imports provide data used in the theorem's unchanged statement.
The proof follows the existing DAG route and retains both proof dependencies.
No new proof import or node is required.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The earlier missing-artifact block is resolved locally
by compiling the sandbox's byte-identical copy of the existing
`DerivedMayerVietorisOpenCounitModel` before the item. Both files compiled without
errors or warnings (5.7 s and 22.9 s). The dependency copy contributes no source diff
and is not an adaptation. No shared build or tool was modified.

## Earlier second reading (a previous round; superseded)
Second reading is pending delivery; the generic helper is private, and the public
statement is unchanged. The proof follows the node's normalization route and introduces
no new statements or nodes.

The change record is `coord/changes/restriction-unit-normalization.md`: preflight
conservatively flags the nested generic section commands; it documents their scope
and the unchanged public interface.

## Second reading by H3

1. PASS: diffed both sandbox modules against the repository. The counit-model module
   is byte-identical. The normalization module changes only the original theorem's
   proof and adds a private, fully proved categorical helper. The original public
   signature, universes, section variables, docstring, imports, and visibility are
   byte-for-byte unchanged. No definition or target statement changes.
2. PASS: compiled the two modules in import order through lcompile.py, with no errors
   or warnings. The delivered sources contain no sorry, axiom, unsafe, opaque,
   implemented_by, or extern. A scratch copy probes the public theorem's axioms;
   the probe printed exactly propext, Classical.choice, and Quot.sound. The
   delivery tool also probes every declaration.
3. PASS: no split-off statement or new public statement exists. The helper is proved,
   rather than an assumed restatement. Its hypothesis on LX is supplied by the open
   restriction theorem and the equivalence, never by an assumption on K. Empty and
   full opens are included; the calculation does not assume a nonempty open or an
   injective input object. No arbitrary witness is chosen from an unproved existence.
4. PASS: checked h₁, h₂, h₃ against rightDerivedNatTrans_fac, h₄ and hLY against
   rightDerivedFunctorIsoMapDerivedCategory_hom_fac, and the inverse cancellations.
   hfirst uses naturality of the exact-target comparison; hfirst' cancels its
   isomorphism. The final he identifies the homotopy composition factors on quotient
   representatives. Read the canonical comparison definition: its four factors and
   underived comparison agree with the specialization. Searched the upstream
   MapDerivedCategory and Comp modules and Sheaf's FiniteExactHomSingleCounitTransport
   for composition/unit factorization; their existing equations are used, and no
   shorter theorem for this four-factor square was found. Both public imports are
   needed by the unchanged statement. Both old proof dependencies remain used, so
   No longer needed is complete. Read dag/units/sk-thm-picard-semicon.json: its
   realized lists are empty, and this proof changes no unit route or realization.
5. PASS: read the normalization node and its two dependency modules. The node's
   formula matches every factor of the public statement, including arbitrary K.
   Its proof_deps remain exactly the two definition nodes. Updated only proof and
   proof_origin to record the private calculation and the K-injectivity preservation
   instance used in the completed Lean proof.

Changes from second reading: no Lean proof changes; corrected the stale validation
report, expanded the private-helper change record required by the conservative command check, and completed
proof metadata. The byte-identical dependency copy is local compile support only.

The first dry run required a change record for the generic section commands. The
record now explains their local scope and includes the exact helper statement.
