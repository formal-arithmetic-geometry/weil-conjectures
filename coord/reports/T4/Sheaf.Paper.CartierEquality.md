## What changed

No signature, definition, import, or DAG route changed. The proof now composes `hker` with the
sequence-length equality directly, removing the repeated type annotation of `hker'`. The assigned
repair is already implemented in the supplied repository: `cartier_equality` assumes
`(⊤ : IntermediateField k K).FG`, not `Algebra.FiniteType k K`, and has a complete
proof. This delivery records verification of the existing repair for the second reader.
The sandbox contains this small proof simplification of the assigned module.

The proof follows the recorded route: choose a finite transcendence basis and finite
field generators, apply the complete-intersection fraction-field model and cotangent
comparison, transport finite dimensionality, and combine the two rank-nullity equations.
The equality is stated in Cardinal without truncated subtraction. The finite-extension
case follows from zero transcendence degree. No arbitrary witness is used to define data.

## Proved and sorry left

`cartier_equality` (node `lem-weil-pbc-cartier-equality`) already has no local sorry.
Holes closed by this worker: none. Holes added: none. Holes remaining in the assigned
module: none. This is verification of an already completed repair, not new proof progress.
The original module compiled through lcompile.py with exit code 0 and no warnings.
The delivery dry run additionally checks the declarations with the maintainer's axiom probe.

## No longer needed

None. No imports, nodes, or modules were removed. The two complete-intersection model
modules and the finite-transcendence-basis Mathlib import are used by the existing proof.
The node agrees with these dependencies; the blueprint unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

The assignment says this module still contains sorry, but the supplied version contains
none and compiles. It remains listed in `coord/repairs.txt` for upstream review #1428,
although the weakened `Algebra.FiniteType` hypothesis has already been replaced by finite
field generation. The node also records an earlier accepted proof delivery. The dispatcher
should retire this stale repair after the second reader confirms the current version.

The existing complete-intersection and cotangent-model statements were read in full.
A fresh Lean Finder search found standard-smooth differential-rank lemmas, which require
extra smoothness hypotheses and do not replace the general Cartier argument.

## Second reading by T4

1. I compared the delivered module with `lean/Sheaf/Paper/CartierEquality.lean` in the
repository. The theorem signature, hypothesis `(⊤ : IntermediateField k K).FG`, conclusion,
definitions, and imports are unchanged byte for byte; only the local proof binding was
simplified. The node's statement and the Lean declaration agree clause by clause.

2. I compiled the sandbox module with `lcompile.py`; it exits 0 with no warnings. The proof
uses the finite transcendence-basis, complete-intersection, and cotangent-model declarations
recorded in `proof_deps`, then rank-nullity and the finite-extension zero-transcendence-degree
fact. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definitions.

3. The node has no new split-off statement. Its existing proof steps are strictly smaller than
the target and their cited declarations say the facts used: the model supplies `n - c = d`,
the cotangent model supplies the kernel/cokernel equivalences, and the linear algebra identities
supply the dimension calculation. The Mathlib/project searches recorded in `searches.jsonl`
found no declaration replacing the general Cartier equality.

4. The proof is pruned only by replacing the intermediate `hker'` name with the existing
`hker` name after composing it with `hlen`; no import or dependency is removed. The unit route
is preserved, including both complete-intersection model modules and the finite transcendence
basis step.

5. I checked the finite-extension edge case: `trdeg_eq_zero` reduces the Cardinal equality to
the equality of the two finite ranks, and `exact_mod_cast` transfers it to naturals. No
statement correction or forced adaptation is present in this delivery.

I changed only the proof binding described in point 4 and added this second-reading record.
