## What changed
Proved all six sorries in the Ring module, without changing statements, definitions,
or imports. Scalar compatibility is restriction along the existing ΓSpecIso ring
homomorphism. Identity and composition follow from the point maps and Lie equivalences;
injectivity follows from cancellation by a monomorphism. Centrality follows by applying
the mixed-point equivalence to the trivial commutator of commuting points. For an open
immersion, every infinitesimal point has its underlying map in the identity section's
image and therefore lifts by Mathlib's IsOpenImmersion.lift; cancellation proves that
the lift is infinitesimal, giving surjectivity.

## Proved and sorry left
Proved all six original sorries:
- `AlgebraicGeometry.GrpObj.instLieAlgebraLie`
- `AlgebraicGeometry.GrpObj.differential_id`
- `AlgebraicGeometry.GrpObj.differential_comp`
- `AlgebraicGeometry.GrpObj.differential_injective`
- `AlgebraicGeometry.GrpObj.range_differential_le_center`
- `AlgebraicGeometry.GrpObj.differential_bijective_of_isOpenImmersion`

No sorry remains in this module; none was added. Existing imported results, including
mixed-point bijectivity and the Lie structures over global sections, remain dependencies.
The complete module compiles through lcompile.py without warnings.

## No longer needed
None. All three existing public imports support the file's statements or structures;
no new proof imports, nodes, or intermediate theorems were needed. The unit routes
remain intact. No existing node's planned dependency was pruned.

## Where the brief, the DAG or earlier work was wrong
The module's six sorries admit direct proofs from its existing imports, rather than
requiring new intermediate statements. No mathematical statement was disputed or changed.

The preflight treats every instance-body edit as an interface change, including this
Type-valued instance whose only changed field, `lie_smul`, is proposition-valued. Its
unchanged type and downstream impact are recorded in
`coord/changes/lie-ring-scalar-compatibility.md`; no additional module needs adaptation.


## Earlier second reading (a previous round; superseded)

1. Interface: PASS. Compared the complete module against the repository with `diff -u`.
   The only six edits replace proof bodies; every existing declaration signature,
   definition, docstring, and import is byte-for-byte unchanged. The instance inherits
   the same module data; only its `lie_smul` proof field changes. Reviewed the change
   record and corrected its false claim that `LieAlgebra` is Prop-valued.
2. Proofs: PASS. Independently compiled the module with lcompile.py without errors or
   warnings. No `sorry`, axiom, unsafe, opaque, implemented_by, or extern occurs in it.
   Scratch-copy `#print axioms` checks cover the six repaired declarations and show
   only propext, Classical.choice, Quot.sound, and sorryAx from existing imported open
   statements. Read the scalar restriction, identity/composition, mono cancellation,
   commuting mixed-point commutator, and open-immersion lift arguments. In the last
   argument the dual-number zero section is topologically the identity, so the range
   condition holds; cancellation after lifting proves reduction to the identity.
3. Split statements: PASS, vacuous. There are no new declarations, new nodes, or
   split-off statements, and hence no restatement of an original goal. The direct
   arguments also cover the zero ring, trivial groups, and identity morphisms; no
   field, reducedness, finite-type, or characteristic hypothesis is silently used.
4. Route and pruning: PASS. Searched the library for the differential and centrality
   declarations and checked Mathlib's open-immersion lift and LieAlgebra definition.
   The proofs use existing transport maps and Mathlib cancellation/lifting directly.
   Abelian supplies the center in a public signature, GroupScheme.Basic supplies
   ContainsCommutators, and Bracket supplies Lie structures and the differential's
   construction, so all three public imports support the interface. No proof-only
   public import was added. Reviewed the tangent, restriction, comparison, and Cartier
   unit records: their routes are preserved. Their existing empty `realized` lists
   are not filled or bypassed by this proof-only delivery. No old dependency is pruned.
5. DAG: PASS within this item's scope. The module occurs in the tangent definition's
   primary Lean record and in umbrella nodes' historical transitive Lean audits;
   the six repaired proof holes have no individual node plans to rewrite. The tangent
   definition and the broader closure/Cartier/same-Lie proofs retain their statements
   and dependencies. No new proof dependency or proof-origin change is introduced.

Second reading changed only the change-record explanation above and this review report;
no Lean repair was necessary. The change record is
`coord/changes/lie-ring-scalar-compatibility.md`.

## Second reading by M2

1. Interface: PASS. Diffed the complete module against the repository: every existing
   signature, definition, docstring, and import is unchanged. Only the six original proof
   bodies change. The instance's proposition-valued field edit has its change record.
2. Proofs: PASS. Independently compiled the module and its scratch axiom checks through
   lcompile.py. No errors or warnings; no sorry or forbidden declaration mechanism in
   the delivered module. All six declarations use only the permitted base axioms and
   sorryAx inherited from existing imported open results.
3. Split statements: PASS, vacuous. No new statement or node is introduced. Read all six
   arguments; none adds a hypothesis, and identity, trivial-group, and zero-ring cases
   require no exception. There is no disguised restatement of an original goal.
4. Route and pruning: PASS. Existing transport and point-map declarations give the direct
   proofs; cancellation and Mathlib's open-immersion lift close the geometric arguments.
   The three public imports supply public structures and signatures. No existing proof
   dependency is removed, and no unit route is bypassed.
5. DAG: PASS. The tangent definition's primary record and the umbrella nodes retain their
   statements and dependencies. No individual node plan for these six proof holes needs
   rewriting, and no new proof dependency or proof-origin change is introduced.

This second reading changed only the report by adding the required review section. No
Lean repair was necessary. The existing change record is
`coord/changes/lie-ring-scalar-compatibility.md`.
