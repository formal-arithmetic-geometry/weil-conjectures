## What changed
Replaced the first worker's near-target split `exists_algClosed_smooth_prime_over` with
`Algebra.exists_algClosed_prime_over_finrank_differentials_eq`, in the new module
`Sheaf.RingTheory.AlgClosedDifferentialFiberAtClosedPoint`. Its statement only constructs
an algebraically closed extension and a maximal prime over the original prime with
matching differential-fibre finrank. It has no dimension-bound hypothesis and makes no
smoothness assertion. The witness field is in `Type (max u v)`, matching the residue field.

The unchanged target `Algebra.isSmoothAtPrime_of_finrank_kaehlerDifferential_le` now combines
this geometric fact with three existing declarations: field-extension invariance of
point dimension, the closed-point/local-ring dimension equality, and the algebraically
closed maximal-ideal smoothness criterion, then applies field-extension smoothness
descent. The proof implements tensor symmetry and invariance of point dimension under
a homeomorphism. All original imports are used and retained; the new geometric module
is a plain proof-only import. The first worker's added public import of algebraic-closure
basics in the target module was removed because only the helper's signature needs it.
The new helper exposes only imports needed to state its geometric assertion.

Updated the item's DAG proof and direct proof dependencies to match the actual reduction,
and replaced the deficient draft node with a complete geometric node. No existing
signature, definition, public visibility, unit record, or statement was changed.

## Proved and sorry left
Closed one original hole: `Algebra.isSmoothAtPrime_of_finrank_kaehlerDifferential_le`
(node `lem-weil-pbc-differentials-dimension-bound-smooth-at-prime`). Its proof contains
no `sorry`.

Added one named hole: `Algebra.exists_algClosed_prime_over_finrank_differentials_eq`
(node `new-algclosed-differential-fiber-at-closed-point`), in
`Sheaf.RingTheory.AlgClosedDifferentialFiberAtClosedPoint`. It is exactly `:= by sorry`,
with its source, complete proof in words, and blueprint annotation. There are no other
holes in the delivered files. The first worker's undelivered
`exists_algClosed_smooth_prime_over` and its incomplete node were removed.

This delivery is a decomposition: one hole closed, one strictly smaller geometric hole
added, net zero holes. It does not claim an axiom-free proof of the target. The target
also uses the existing open maximal-ideal criterion and descent theorem. Scratch
`#print axioms` checks for both delivered declarations reported only `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`.

## No longer needed
No original module imports were removed and no modules are pruned. The first worker's
new public algebraic-closure import was removed from the target module.

These old direct proof dependencies moved into the geometric helper's proof and are
therefore absent from the target node's new direct `proof_deps` (they remain necessary
transitively, and are not pruned):
- `def-weil-pbc-localization-at-prime`
- `def-weil-algebraic-closure`
- `def-pc-field-extension`
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`
- `lem-weil-pbc-kahler-differentials-base-change`
- `def-weil-pbc-kahler-differentials`

## Where the brief, the DAG or earlier work was wrong
The first draft split essentially all of the difficult argument into a smooth-prime
existence assertion with the target's dimension-bound hypothesis. It did not apply the
already stated maximal-ideal criterion or the dimension comparison declarations. Its
new theorem lacked a proof docstring and blueprint annotation, its node lacked the
required fields, its report called the reduction a proof, and its local instance
bindings produced style warnings. All of these were repaired. The old source plan and
the unit route remain valid; construction and differential-fibre transport remain open.

Mathlib and upstream/library searches found individual tools (including
`Module.finrank_baseChange`, maximal kernels of surjections, and differential tensor
base change), but no complete geometric helper. LeanFinder and Loogle were available;
LeanSearch returned an internal server error, recorded without a mathematical verdict.

## Second reading by C2
1. Interface: compared the complete delivered target module against the repository and
   asserted byte-for-byte equality of the existing theorem signature. Its old docstring,
   public imports, universe parameters, and namespace were retained. No definition was
   added or altered. Verdict: pass after repairs.
2. Proof: compiled both delivered modules in import order through `lcompile.py`, without
   errors or warnings. Checked the only `sorry` is the named geometric theorem, and
   checked there are no forbidden declarations or hollow definitions. Scratch
   `#print axioms` checks show only the three allowed axioms and `sorryAx` from open
   statements. No data definition chooses an arbitrary witness of an unproved existence
   assertion: the existential is eliminated only inside the target's proposition proof.
   Verdict: valid decomposition, not an axiom-free completion.
3. Split statement: read the construction in Stacks Tag 00TT and the existing base-change
   node, then searched Mathlib, upstream, and `lean/Sheaf` using different terminology.
   The helper is strictly geometric and does not restate the target. Edge cases checked
   mathematically: S=k gives differential rank zero; the generic prime of k[x] gives a
   closed point x=t over an algebraic closure of k(x), preserving rank one; inseparable
   finite field extensions and dual numbers preserve their positive differential rank
   without asserting smoothness. The zero ring has no prime to supply as input. The
   selected field's universe accommodates the residue field. Verdict: true and sufficient.
4. Route and pruning: the target explicitly uses the existing field-extension dimension
   theorem (through tensor symmetry), closed-point dimension theorem, maximal-ideal
   criterion, and descent theorem. The helper isolates only construction and fibre
   transport. Checked `dag/units/sk-thm-p1.json` realized fields: the item is below the
   unit-level nodes; no unit statement, realized step, or chapter route is bypassed or
   changed. Every original import remains needed. Verdict: pass.
5. DAG: the existing node changes only `proof`, `proof_deps`, and `proof_origin`.
   The new node has the required full metadata, the verbatim Lean signature, recorded
   searches, source, steps, and the union of their dependencies. Every removed direct
   dependency is listed above and retained in the helper's plan. Verdict: pass.

Second-reading changes: replaced the near-target split with a smaller geometric lemma
in its own module, implemented dimension transport and the maximal-ideal criterion in
Lean, corrected instance bindings, completed the node metadata, updated the target's
DAG route, and corrected the report to count the result as a decomposition.

## New nodes
`new-algclosed-differential-fiber-at-closed-point`:
`dag/nodes/sec-proper-base-change/new-algclosed-differential-fiber-at-closed-point.json`,
matched to `Algebra.exists_algClosed_prime_over_finrank_differentials_eq` in
`lean/Sheaf/RingTheory/AlgClosedDifferentialFiberAtClosedPoint.lean`. This is the closed
geometric-point construction and differential-fibre comparison from steps 1, 2 and 4
of the old plan. It uses no smoothness criterion, no descent, and no dimension bound.
No change records are needed because all existing signatures and definitions are unchanged.
