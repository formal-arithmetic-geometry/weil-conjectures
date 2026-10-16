## What changed

Proved both declarations in
`lean/Sheaf/AlgebraicGeometry/TorsionLocalModelRestriction.lean`:
`AlgebraicGeometry.coherent_of_iso` and
`AlgebraicGeometry.torsionLocalModel_restriction`.

The coherence helper transfers quasi-coherence and finite local generators across an
isomorphism. The main proof constructs the restricted coherent model using the
restriction/tensor-pullback comparison, transports the over-site normalization maps,
constructs the completion comparison from the quotient comparison, and transfers the
kernel/cokernel annihilation bound through restriction and isomorphisms. The target
statement and imports are unchanged. The module compiles cleanly with `lcompile.py`.

## Proved and sorry left

Closed the two original holes:

- `AlgebraicGeometry.coherent_of_iso`;
- `AlgebraicGeometry.torsionLocalModel_restriction`.

Holes closed: 2. Holes added: 0. Holes left in the item: 0. No new theorem with
`sorry` was introduced.

## No longer needed

None. The existing imports are used by the coherence, pullback, quotient, completion,
over-site, and kernel/cokernel parts of the proof. No existing node or module is
pruned, and the node's proof dependencies remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No correction was needed. A complete proof of this exact statement was present in an
earlier project delivery; it compiles against the current upstream-synced source and
follows the node's stated route. The node and theorem signatures are unchanged.

## Second reading by M1

1. Compared the delivered module with the repository version. The namespace, imports,
   declarations, theorem signature, visibility, and target docstring are unchanged; only
   the two proof bodies replace `sorry`. No unrelated file or existing declaration is
   modified. Verdict: passes interface preservation.

2. Compiled the module with `lcompile.py` and checked a scratch copy with `#print axioms`.
   The file has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`.
   The main theorem and its private coherence helper use only `propext`, `Classical.choice`,
   and `Quot.sound`. The restricted coherent module is explicitly `R.obj F.obj`, while the
   completion comparison is built from the tensor-pullback comparison and quotient
   projections; no arbitrary object is selected from a mere existence proposition. Verdict:
   proof is kernel-accepted with permitted axioms.

3. Read the proof from the coherence transport through the normalized completion comparison,
   normalization equations, and kernel/cokernel annihilation transport. The proof closes
   both original holes and adds no split-off theorem or `sorry`. It retains the supplied
   positive exponent and handles the categorical constructions uniformly for empty opens,
   zero modules, and zero or unit ideals. The private helper is a strictly smaller coherence
   transport argument, not a restatement of the target. Verdict: statements and proof are
   mathematically appropriate and unchanged.

4. Checked the route against the node and unit records. The proof uses the stated
   restriction/tensor-pullback, formal-completion, quasi-coherent kernel/cokernel, and
   torsion-restriction ingredients; the unit route and target statement are unchanged.
   The proof-only `import all` declarations expose the private helpers needed from the
   existing pullback and torsion-restriction modules. The report's no-longer-needed section
   is complete: no direct import is removed and no node is pruned. Verdict: route and
   pruning record agree.

5. Read the node's proof, `proof_deps`, and `proof_origin` against the Lean proof. Its
   steps cover coherence and restriction, over-site normalization, quotient/completion
   comparison, and annihilation transport, and its dependency list contains the required
   declarations. No new node or statement is introduced, so there is no node/interface
   change to review. Verdict: DAG agrees with the delivered Lean code.

Changed only the report by adding this second-reading record. No proof, statement, import,
node, or change record required repair.
