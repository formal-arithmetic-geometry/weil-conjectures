## What changed

Revalidated the queued upstream-review #1428 repair of
`Sheaf.Paper.CartierEquality.cartier_equality`. The required finite field-generation
hypothesis `(⊤ : IntermediateField k K).FG` is already present in the repository.
The sandbox differs from the repository by one proof line:
`have hker := hker.trans hlen`. This explicitly converts the kernel/range
rank-nullity equation from `f.length` to `c` before `omega`. Both the original
and delivered proofs compile; this is an explicit dimension calculation, not a
newly closed proof hole. No signature, definition, import or DAG field changes.

The proof chooses a finite transcendence basis and a finite field-generating set,
obtains a complete-intersection fraction-field model, identifies cotangent
homology and differentials with a finite-dimensional kernel and cokernel, and
uses two rank-nullity equations and `n - c = s.card` to derive the untruncated
cardinal equality. For a finite extension it substitutes `trdeg_eq_zero` and
casts back to natural numbers. This follows the three current node proof steps
and preserves the unit route.

## Proved and sorry left

`cartier_equality` (node `lem-weil-pbc-cartier-equality`) is already proved in the
baseline. There are zero direct sorries in the assigned module. Holes closed:
none (0). Holes added: none (0). No split-off statements or new declarations.
The delivered theorem compiles without warnings; a scratch copy with
`#print axioms cartier_equality` reports only `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`. The original repository proof also compiles.

## No longer needed

None. No imports, nodes or modules are removed. All six existing proof dependencies
remain used: the finite transcendence basis, complete-intersection model, cotangent
model, vector-space dimension, transcendence degree, and transcendence basis.
`Mathlib.FieldTheory.FinTrdeg` and both Sheaf model modules are plain proof imports.
The public Mathlib imports expose the notions in the theorem's signature.

## Where the brief, the DAG or earlier work was wrong

The dispatcher brief says the assigned module still contains `sorry`, but the
current module has none. Its node records group T4's accepted proof landing on
2026-10-14. The queue lists this module as a zero-sorry repair because
coord/repairs.txt still contains upstream review #1428. That review requested
finite generation as a field extension rather than `[Algebra.FiniteType k K]`;
the current hypothesis already is exactly `(⊤ : IntermediateField k K).FG`.
Existing change records record the correction. This delivery does not claim new
proof progress or change the hypothesis again. The first report's claim that the
sandbox and repository were byte-identical was inaccurate: the proof line above
was already in the sandbox when the second reader started.

## Second reading by Y3

1. Compared the complete delivered module with the repository using `diff`.
   The sole difference is `have hker := hker.trans hlen` within the proof.
   The existing declaration signature is byte-for-byte unchanged; there are no
   definitions, visibility changes, or changes requiring a change record. Pass.
2. Read the full proof and both imported model theorem statements and proofs.
   The finite-generation hypothesis supplies a genuine finite field-generating
   set; the model supplies `c ≤ n`, `n - c = s.card`, and `f.length = c`.
   The kernel and cokernel equivalences supply finite-dimensionality and both
   dimension identities. The added line is ordinary equality transitivity.
   Compiled the delivery and a scratch axiom probe through lcompile.py, without
   errors or warnings. Only the three permitted axioms occur. No forbidden
   declarations, sorries, or hollow definitions occur. Pass.
3. No statements were split off or added, so no new statement can be a restatement
   or require a new node or search record. The cardinal formula retains its
   untruncated conclusion and covers positive transcendence degree; the finite
   specialization follows by setting transcendence degree to zero, including
   the identity extension. Pass.
4. Checked the existing shortest-route choices and searched project sources for
   `cartier_equality` and the joint transcendence-degree/cotangent formula.
   No replacement theorem was found. Mathlib has
   `LinearMap.finrank_range_add_finrank_ker`, but using it would require an
   additional proof import merely to replace the present short rank-nullity
   argument. Kept the correct argument and its imports. Each proof-only import
   is plain `import`; public imports supply signature notions. No old proof
   dependency is unused. Read `dag/units/sk-thm-p1.json`, including `realized`:
   the proof change bypasses no realized unit statement or step. Pass.
5. Read `lem-weil-pbc-cartier-equality.json`: its three proof steps, six
   `proof_deps`, `proof_origin`, and recorded Lean signature agree with the
   delivered proof. Step 3 already states the conversion to `c` that the
   added line makes explicit, so no DAG change is needed. There are no new nodes.
   Pass.

Second reading changed the report to describe the actual one-line proof diff,
the successful original compile, the axiom result, and zero proof-hole progress.
No Lean changes were necessary; the supplied proof change was retained.
