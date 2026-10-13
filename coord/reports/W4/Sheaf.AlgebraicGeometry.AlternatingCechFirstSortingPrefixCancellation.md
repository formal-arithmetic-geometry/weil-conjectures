## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.cechFirstSortingPrefixCancellation`
with a compiling proof. Its signature and existing docstring are unchanged.
Added proof-only imports of `Mathlib.GroupTheory.Perm.Fin` and
`Sheaf.AlgebraicGeometry.AlternatingCechPrefixDeletionBijection`.

The new module gives explicit subtype abbreviations for the valid outgoing and
incoming indices and states their unsigned deletion/insertion correspondence.
The original module proves five private helpers: `prefix_nonjunction`,
`prefix_filter`, `sign_restrict`, `junction_restrict`, and `sum_subtype_ite`.
The first two eliminate the redundant nonjunction condition when r<a;
the others establish the generic permutation
sign after restriction, the junction-map identity by position cases, and the
conversion from filtered sums to subtype sums. The main proof then establishes
opposite integer coefficients and uses `Fintype.sum_equiv` to cancel the sums.
The node's route records these steps. This keeps the unit's Cech comparison route.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.cechFirstSortingPrefixCancellation`
(node `lem-pc-alternating-cech-first-sorting-prefix-cancellation`).
The item's module contains no remaining `sorry`.

Added and left: `AlgebraicGeometry.Scheme.cechPrefixDeletionBijection`
(node `lem-pc-alternating-cech-prefix-deletion-bijection`). Its proof is exactly
`by sorry` in its own module, with a deletion/insertion proof in its docstring and
node. This is a decomposition: one upper hole closed, one lower hole added,
net zero holes. It leaves only an unsigned combinatorial correspondence, with no
abelian group, function f, coefficients, nonjunction filter, junction-map equality,
or sum identity.
All filter, sign, junction, and summation arguments are proved rather than moved.

Compiled both modules in import order with `lcompile.py --all`; each takes about
2–3 seconds. Exhaustive sandbox-only checks tested all 3,276 tuples over three
values in sizes 2–7 (59,868 matched terms), checking valid filters, inverse
correspondence, both permutation restrictions, junction identity, sign relation,
and opposite coefficients. The checks include p=0, b=0, b=p, constant tuples,
and repeated values. Empty I admits no input t. These checks support the new
statement's edge cases; the correspondence itself still needs a Lean proof.

## No longer needed

None. No original import, dependency node, or module was removed.
`Sheaf.AlgebraicGeometry.AlternatingCechSortingOperators` remains a required
public import for the unchanged statement. No other branch of the unit is bypassed.

## Where the brief, the DAG or earlier work was wrong

The parent node had only the sorting definitions as proof dependencies; it had
no declaration for its nontrivial deletion/insertion correspondence. The delivery
states exactly that structural part as a new node, and proves the remaining steps.

The local literature checkout contains lists but not the Stacks source or the
blueprint text. Read the existing material in the read-only literature tree at
`/home/ubuntu/work-bp/sheaf/literature/`: cohomology.tex, lines 4270–4374,
lemma-alternating-usual and equation-first-homotopy, and the unit's _section.md.
The equation's own Stacks tag is 01FN; the surrounding lemma is 01FM.
LeanSearch returned Internal Server Error and is recorded as unavailable.
`blueprint_refs.py ancestor` returns None for the parent because its creation
record names a module; the new node follows the parent's explicit blueprint
ancestor `lem-pc-projective-space-cohomology-bound` instead. Blueprint searches
for prefix deletion, labelled, and first homotopy found no matching statement.

## New nodes

`lem-pc-alternating-cech-prefix-deletion-bijection`, in
`dag/nodes/sec-picard-framework/`, is the unsigned correspondence between valid
prefix deletions and incoming faces. It relates the prefix lengths and both
restricted permutations. Its real subtype definitions are in
`Sheaf.AlgebraicGeometry.AlternatingCechPrefixDeletionBijection`; its single
unproved public theorem is strictly the sorting correspondence used by the
proved algebraic calculation. No statement or definition was changed, and no
forced adaptations or change records are required.

## Second reading by W4

1. Compared the delivered item module with the repository version. The target
   theorem signature and docstring are byte for byte unchanged; only proof-only
   imports and the proof body were added. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. The target has no
   remaining `sorry`; the only remaining hole is the named theorem
   `cechPrefixDeletionBijection`, with its own node and proof docstring. No
   forbidden declaration or hollow definition was found. Verdict: pass.
3. Repeated the Mathlib/local search for the correspondence under alternate
   wording; no existing declaration matches it. The new theorem is a strict
   unsigned structural reduction, rather than a restatement of the target.
   Verdict: pass.
4. Checked the proof route and imports. The unit's sorting and Cech comparison
   route is retained; the added permutation import is proof-only, and no old
   import or dependency is unused. Verdict: pass.
5. Checked the target and new node records against the Lean declarations. The
   proof dependencies, source, and split theorem agree with the code, and edge
   cases are covered by the docstrings and finite checks. Verdict: pass.

Changed after reading: added this second-reading record only; no Lean or DAG
content required repair.
