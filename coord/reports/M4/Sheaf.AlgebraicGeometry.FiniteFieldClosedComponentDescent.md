## What changed

Closed `AlgebraicGeometry.exists_finite_intermediateField_closed_component_descent`
in `Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent`, preserving its signature
and visibility. Added proof-only imports of
`Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends` and
`Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends`.

The shorter route takes a nonempty affine open inside each component's exclusive
interior. Its closure is the component. Compact-open descent supplies a finite field
fixing that open, hence fixing its closure. A finite induction joins these fields.
The pullback tower isomorphism transports component finiteness and the Galois action;
closed-subset descent over the joined field supplies the requested closed subsets.
Surjectivity follows from the single-point spectra of fields and base-change stability.

Three private helpers are proved completely: `finite_components_homeomorph`,
`component_finite_stabilizer`, and `components_finite_stabilizer`. No new public
statement, definition, module, or interface change. Updated the existing node's
`proof`, `proof_deps`, and `proof_origin` to this route. The unit's realized statements
and steps are unchanged; this is a shortcut below the unit level.

Sources checked: [Stacks 04KU](https://stacks.math.columbia.edu/tag/04KU),
[Stacks 038B](https://stacks.math.columbia.edu/tag/038B), the existing Lean declarations,
and Mathlib's irreducible-component, affine-open, intermediate-field and pullback APIs.
The action compatibility calculation follows the already proved calculation in
`GaloisFiniteInvariantClopenPartition`; that module is not imported.

Validation: the complete module compiles through `lcompile.py` without errors or
warnings. Both proof imports pass `import_direction.py may`. Removing the redundant
explicit Mathlib pullback-pasting import also compiles. Empty schemes are handled by
the empty-family case of the finite induction, using the bottom field; one component
uses its dense affine open. No Noetherian or quasi-separated hypothesis is required
by this route. The original locally-finite-type hypothesis remains in the signature.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.exists_finite_intermediateField_closed_component_descent`
(node `new-lem-sbc-finite-field-closed-component-descent`).
No `sorry` remains in the item's module; no hole is added in another module.
This is a proof from existing declarations, not a decomposition into new statements.
The existing compact-open descent theorem and closed-subset descent theorem are
already proved; their existing transitive dependencies remain future work as applicable.

## No longer needed

The old route's following direct proof dependencies are unnecessary here:

- `lem-weil-pbc-finite-type-algebra-noetherian`;
- `lem-weil-pbc-algebraic-generators-finite-extension`;
- `lem-weil-pbc-field-extension-base-change-faithfully-flat`;
- `lem-weil-pbc-faithfully-flat-surjective-spectrum`.

They had no explicit proof imports in the assigned module, so no existing import
line was removed. Their corresponding Mathlib finite-type-Noetherian, algebraic
adjoin, and faithfully-flat tensor/spectrum arguments are not needed by this proof.
The redundant temporary proof import
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting` was removed after checking
compilation. The two original public imports are kept to preserve the public interface.
No existing Sheaf module is claimed to leave the whole target closure: that is for
the maintainer's ledger to determine, and compact-open descent may still use some
of the pruned algebraic facts transitively.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement or tool failure was found. The original minimal-prime
finite-type proof is unnecessary: compact-open descent gives finite stabilizers
for closures of affine opens, and finitely many components have nonempty exclusive
interiors. The existing theorem docstring retains its original valid proof plan;
the inline comment and updated node describe the implemented shorter proof.

## Second reading by M4

Independent second reader, 2026-10-13. Read the delivered module, its repository
version, both versions of its node, the two imported descent modules, the Mathlib
irreducible-component lemmas, and `dag/units/sk-prop-normal-form.json`.

1. **Interface: pass.** Compared the delivered module with the repository version
   and checked the existing theorem's complete signature byte for byte, from its
   name through the conclusion preceding `:= by`. It is unchanged, including the
   locally-finite-type and finite-component hypotheses, universes, finite-field
   conclusion, projection surjectivity, component finiteness, and exact preimage
   equality. The original public section and public imports remain unchanged.
   Only the proof, three proved private helpers, and two plain proof imports are
   added. There are no definitions or interface change records in this delivery.
2. **Proof: pass.** Independently compiled the delivered file with `lcompile.py`
   (5.9 seconds, no warnings or errors). Compiled a scratch copy containing
   `#print axioms` for the original theorem and each private helper. All four use
   exactly `propext`, `Classical.choice`, and `Quot.sound`; none uses `sorryAx`.
   Scanned the delivered source for `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, `extern`, and `debug.skipKernelTC`: none occurs. In particular,
   no data is chosen from an unproved existence theorem. The point chosen in a
   field spectrum is justified by the proved nonemptiness instance.
3. **Split statements and small cases: pass, none split off.** All three helpers
   are proved. Finiteness of the components makes the complement of the other
   components open and dense in the chosen component, by Mathlib's
   `closure_sUnion_irreducibleComponents_sdiff_singleton`. A component is nonempty,
   so an affine neighborhood inside this complement exists and is compact; its
   nonempty intersection with the irreducible component is dense. Thus compact-open
   descent really fixes the entire component after taking closure. Intersecting
   components cause no problem because the chosen open avoids their intersections.
   For no components the finite induction uses the bottom field and no nonempty
   open is requested; for one component it uses a nonempty affine open. Composita
   preserve finiteness and fixing them pointwise fixes both constituent fields.
   No new public statement, module, node, or sorry is introduced.
4. **Route and pruning: pass.** Checked Mathlib's irreducible-component APIs and
   searched the library and upstream source with the alternative concepts
   `finite.*stabiliz`, `stabiliz.*finite`, `components.*descend`, and
   `descend.*components`. No existing theorem supplies the complete finite-field
   descent directly. The proof uses existing compact-open descent and invariant
   closed-subset descent rather than duplicating them. Both new imports are plain
   `import` and are used in proofs; the original public imports supply statement
   vocabulary. The four old proof dependencies absent from the new route are
   exactly those listed under `## No longer needed`. No existing import is removed,
   and no whole-target-closure module pruning is claimed. The unit has empty
   `realized.statement` and two empty `realized.steps` lists; these are untouched.
   This shortcut changes a below-unit argument, not the normal-form or slicing
   route. The tower action compatibility is checked with both projections;
   restricting an Omega/L automorphism fixes L, so the stabilizer theorem applies.
   The field spectrum map is surjective and its pullback remains surjective.
5. **DAG: pass.** Parsed and compared both node records: exactly `proof`,
   `proof_deps`, and `proof_origin` differ. The six recorded proof dependencies
   have existing Lean declarations or Mathlib matches. Their uses match affine
   neighborhoods, compact-open descent, separable-closure Galois instances,
   pullback pasting, surjective base change, and invariant closed-subset descent.
   The union of the proof steps' `uses` is precisely `proof_deps`. The node's
   statement, Lean statement record, source, chapter, unit, and other fields are
   unchanged. The homeomorphism transport and finite-compositum induction are
   recorded in the proof steps and implemented by the proved private helpers.

Changes by the second reader: appended this independent review and the explicit
axiom-check evidence. No Lean or DAG correction was necessary. The result closes
one original hole, adds zero holes, and is a proof rather than a decomposition.
