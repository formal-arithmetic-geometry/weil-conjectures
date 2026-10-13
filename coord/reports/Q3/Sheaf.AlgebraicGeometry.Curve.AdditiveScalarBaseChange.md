## What changed

Completed `exists_additive_scalar_base_change` in the sandbox module. Added a private
construction of the structural scalar action on additive sheaf cohomology, then used
the existing additive cohomology comparison and linear base-change declarations to
construct the finite-dimensional module and both scalar compatibilities. The proof
also establishes the required tensor-normalized base-change formula. Added only
proof-only imports required by these declarations.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.IsCurve.exists_additive_scalar_base_change` without changing its
signature. Proved the private helper `exists_additive_cohomology_scalar_action` by
an explicit sectionwise construction and the additive cohomology functor laws.

Added one hole:
`AlgebraicGeometry.IsCurve.exists_additive_cohomology_linear_base_change`, node
`lem-pbc-additive-cohomology-linear-base-change`, in its new module. Its proof is
exactly `by sorry`. This is a decomposition: one original hole closed, one new
hole added, net zero from these declarations. The original theorem still depends
on `sorryAx` through this and other open imported comparisons; it is not an
axiom-free completed target. No hole is added inside a definition.

## No longer needed

No original import was removed: the original file had only signature imports.
All four added proof-only imports are used. Relative to the original node's
`proof_deps`, these direct dependencies have been replaced:

- `lem-pc-euler-characteristic-well-defined` and
  `Sheaf.Paper.EulerCharacteristicWellDefined`: proper finiteness is obtained
  directly from `Scheme.Modules.finiteDimensional_H_of_isProper`.
- `lem-sc-etale-zariski-qcoh-comparison` and
  `Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison`: the proof uses the existing
  scalar-compatible additive/source-H comparison instead.
- `lem-pc-cech-computes` and
  `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray`, and
  `lem-sc-flat-base-change-coherent` and
  `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`: not direct dependencies
  of the item anymore; their mathematical steps remain in the new linear
  base-change obligation's plan. They are not claimed globally pruned.

The original Ext/derived comparison dependency remains. No module is claimed
removed from the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt had no completed delivery, but its sandbox proof already supplied
the needed route. The DAG's multi-step plan is realized through the existing comparison
and the new, still-open linear base-change declaration. The first report did not
account for the added hole and omitted the replaced direct proof dependencies.
The new node initially cited `lem-pc-flat-base-change-cohom`, which only gives
a finrank equality; second reading replaced it by
`lem-sc-flat-base-change-coherent`, the existing coherent linear equivalence.

## Earlier second reading (a previous round; superseded)

Pending the independent second reading. The reader should check the unchanged target
signature, the private scalar-action construction, and the imported linear base-change
statement and node `lem-pbc-additive-cohomology-linear-base-change`.

## New nodes

`lem-pbc-additive-cohomology-linear-base-change` is delivered in
`lean/Sheaf/AlgebraicGeometry/Curve/AdditiveCohomologyLinearBaseChange.lean`; it states
the canonical linear base-change equivalence used by the completed scalar theorem and
retains its documented proof obligation as a `sorry` for the next worker.


## Second reading by Q3

1. Compared both delivered modules with the repository. The scalar module's
   existing theorem signature is byte-for-byte identical, including every
   hypothesis and conclusion. Its docstring and public imports are unchanged.
   The linear module is new, with no existing interface to alter. No definition
   or target statement changed; no change record is required.
2. Compiled both modules with `lcompile.py --all` (3.1 s and 12.3 s). Inspected
   every line of both proofs, including restriction naturality, multiplication
   order, the module axioms, scalar naturality and finite-dimensionality transfer.
   Scratch-copy `#print axioms` for both public declarations gives exactly
   `propext`, `Classical.choice`, `Quot.sound`, `sorryAx`. The only delivered
   `sorry` is the new named linear theorem. No forbidden declarations or hollow
   definitions occur. The module actions are explicit constructions, not
   arbitrary witnesses extracted into definitions from an unproved existence.
3. The new statement is true: IsCurve gives finite type and separatedness;
   flat field extension and quasi-coherent etale/Zariski comparison give its
   normalized linear isomorphism. Its scalar hypotheses uniquely determine the
   actions, by sectionwise equality of the endomorphisms. Checked identity field
   extension, empty and affine schemes, zero-dimensional schemes and nonproper
   separated curves: no finiteness is asserted; vanishing H1 gives the zero
   equivalence. Reviewed Stacks 02KH and 03P2 and the docstring's finite affine
   cover proof. It is strictly a part of the original argument: actions and
   proper finiteness are proved in the item. Independent msearch queries used
   leanfinder ("extension of a field preserves coherent sheaf cohomology with
   natural pullback"), loogle ("SheafOfModules, LinearEquiv") and grep
   ("flat.*base.*change|base.*change.*cohomology"). Also searched the source
   cohomology modules and Sheaf modules. No exact duplicate was found. The
   existing coherent equivalence does not supply the etale pullback normalization
   and coefficient comparisons; closing that obligation is not a few-minute
   application of its statement.
4. The proof uses existing additive comparison and source-library proper
   finiteness, with a real scalar-action construction and transfer argument.
   Every added import is proof-only and used. Listed every replaced old direct
   proof dependency above. Read `dag/units/sk-thm-p1.json`: its realized statement
   and steps remain in use; this local coherent/additive reduction bypasses no
   realized unit node. No global module pruning is claimed.
5. Checked the scalar node's proof steps, dependencies and origin against the
   actual Lean proof. Checked the new node's full statement against its Lean
   declaration and all required source, search, creation, blueprint, chapter,
   unit and Lean fields. Corrected the new node's coherent base-change citation
   from dimension equality to `lem-sc-flat-base-change-coherent`; the other
   dependencies describe its still-open natural comparison/Cech proof plan.

Changed only the new node's proof/dependency citation and this report (accurate
hole accounting, complete direct-dependency pruning, and this second reading).
The Lean proof needed no repair.
