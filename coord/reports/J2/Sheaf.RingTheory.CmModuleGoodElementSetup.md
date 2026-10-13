## What changed

Proved `Module.exists_good_sequence_for_cm_element` in the assigned module, without changing
its signature or public imports. Added private proved helpers extracting a maximal regular
sequence from the finite depth supremum and inductively constructing an adapted sequence.
The induction prepends a good auxiliary element to an adapted sequence on its quotient.

Added `Sheaf.RingTheory.GoodElementCuttingParameter`, with the fully proved public theorem
`Module.exists_good_element_cutting_parameter`. Its private helpers show that a module of
positive support dimension cannot have the maximal ideal minimal in its support, and carry
out prime avoidance for a finite family of ideals. The theorem applies Mathlib's dimension
equality to the successive regular quotients and to the quotient by the prescribed element.
The new theorem does not need the prescribed element to belong to the maximal ideal.

Added only proof imports to the assigned module: the new module,
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem`, and `Mathlib.RingTheory.Support`.
Updated the assigned DAG node's proof, proof dependencies and proof origin, and supplied a
node for the new proved theorem. No definitions, existing interfaces or other modules changed.

## Proved and sorry left

Closed one of one original holes:
`Module.exists_good_sequence_for_cm_element`
(`lem-weil-pbc-cm-module-good-element-setup`).

Also proved the new theorem `Module.exists_good_element_cutting_parameter`
(`lem-weil-pbc-good-element-cutting-parameter`) entirely from Mathlib. Its axiom check reports
only `propext`, `Classical.choice`, and `Quot.sound`. All four private helper theorems are proved.
No `sorry` remains in either delivered module; no holes were added or split off.

The assigned theorem uses the existing `Module.isSMulRegular_of_good_sequence`.
The local compiled dependency currently makes the assigned theorem's axiom check include
`sorryAx`, besides the three permitted axioms. This is an existing dependency, not a new hole:
the source version of that dependency was proved during this session and now contains no
`sorry`, but the local compiled baseline used for the check has not incorporated that proof.
This delivery closes the assigned declaration, as stage 3 requires, and does not claim that
the entire target import closure has been axiom-checked without `sorryAx`.

Validation: both modules compiled together in import order through `lcompile.py`; no compiler
warnings remained after cleanup. The new lemma's dimension-two case (`n=0`) and its last
prefix (`i=n+1`) are covered by the dimension-drop proof, with no subtraction at negative
integers. The assigned proof handles dimension one directly and excludes dimension zero
using Nakayama and the nonnegative support dimension of the nonzero quotient by `g`.
All universes and hypotheses of the existing theorem are unchanged.

## No longer needed

None of the original imports was removed. The original node had no explicit proof dependencies
to prune. The good-sequence theorem remains needed for regularity and the depth and dimension
of the quotient by the auxiliary element. No original node or module is claimed pruned.

No associated-prime theory, Ext theory, or depth-drop theorem was added: finite-supremum
attainment, prime avoidance and the existing good-sequence interface suffice. The new module
imports Mathlib's regular-sequence definitions directly and does not import the custom depth
module, since its statement and proof do not use depth.

## Where the brief, the DAG or earlier work was wrong

The original node's single proof step hides the main gluing argument. Stacks Tag 00N5 chooses
an auxiliary element good for an already chosen maximal regular sequence, and cutting the
support modulo `g`; it does not assert that `g` is good for that arbitrary sequence. For
example, in the two-dimensional regular local ring obtained by localizing `k[u,v]` at `(u,v)`,
`g=u` cuts dimension by one but is not good for the regular list `[u,v]` at prefix length one.
The delivered induction constructs a suitable new list: choose auxiliary `x`, apply Tag 00N4,
induct on `M/xM`, and prepend `x`. This proves the original statement unchanged.

The cited local `literature/stacks-project/algebra.tex` was absent on this machine. Read the
official Stacks pages for Tags 00N5 and 00N4 online instead:
https://stacks.math.columbia.edu/tag/00N5 and https://stacks.math.columbia.edu/tag/00N4.
The node source remains the same document and tags. The new proof uses Tag 00DS prime
avoidance and the Mathlib implementation of the Tag 0B52 equality case.

Searches were run through `msearch.py` and recorded in `searches.jsonl`. LeanFinder returned
regular-sequence interfaces, Loogle located the exact support-dimension equality used here,
and grep located `support_quotSMulTop`. LeanSearch returned an internal server error and is
recorded as unavailable, not as a negative search result. Blueprint searches for “good element”
and “prime avoidance” found no blueprint nodes stating the auxiliary lemma.

The unit `sk-thm-p1` and its realized statements and proof steps are unchanged. No unit-level
route is bypassed. No forced adaptations or change records are needed.

## New nodes

`lem-weil-pbc-good-element-cutting-parameter` records the fully proved prime-avoidance step,
not a restatement of the assigned theorem. It starts from a fixed maximal regular sequence,
chooses one auxiliary element, and proves its goodness and the additional support cut.
It has no Cohen--Macaulay hypothesis, no depth conclusion, and does not construct an adapted
regular sequence for `g`; those are assembled by the assigned module's induction.
Its Lean module is `Sheaf.RingTheory.GoodElementCuttingParameter`. The proof follows the
auxiliary-element paragraph of Stacks Tag 00N5 using already proved Mathlib results, and all
its cases, including dimension two, are covered by the compiled proof. No new sorry node.

## Second reading by J2

1. **Interfaces: pass.** Compared the assigned module with the repository by `diff`
and checked the existing theorem signature byte for byte. Its universes, hypotheses,
and conclusion are identical. The only existing public import is unchanged; added
imports are private proof imports. The new module exposes only its stated mathematical
theorem and its required Mathlib interfaces. No definition or target statement changed.

2. **Proof and axioms: pass.** Both delivered modules compiled in import order through
`lcompile.py` without errors or warnings. Read all four private helper proofs and both
public proofs. Neither module contains `sorry`, forbidden declarations, or definitions
choosing arbitrary data from an unproved existence theorem. Scratch-copy `#print axioms`
confirmed only `propext`, `Classical.choice`, and `Quot.sound` for
`Module.exists_good_element_cutting_parameter`. The assigned declaration additionally
uses the existing baseline `sorryAx` through `Module.isSMulRegular_of_good_sequence`,
as already reported. No new hole accounts for this axiom. Removed the scratch sources.

3. **New statements: pass; no split-off holes.** The new proved theorem is strictly
an auxiliary prime-avoidance step, not a restatement of the assigned theorem. Checked
the positive dimensions of every prefix quotient and the prescribed-parameter quotient,
the exclusion of the maximal ideal from their minimal primes, and the exact dimension
drop. In particular n = 0 and the last prefix i = n + 1 both give dimension zero
after the cut; no empty support or truncated subtraction is silently substituted.
The assigned proof treats d = 1 directly and excludes d = 0 by Nakayama. Read the
new theorem's source and full docstring proof, and its matching node. Independently
searched with LeanFinder for simultaneous avoidance of minimal primes of finite
modules, Loogle for finite-set prime avoidance, and grep/rg for existing avoidance
and regular-sequence existence results in Mathlib, upstream, and `lean/`. Found the
Mathlib building blocks used, including the exact dimension-drop lemma, but no
existing simultaneous good-element theorem to replace the new lemma.

4. **Route and pruning: pass.** Read the actual induction against
[Stacks Tag 00N5](https://stacks.math.columbia.edu/tag/00N5) and
[Tag 00N4](https://stacks.math.columbia.edu/tag/00N4). It constructs an adapted
sequence rather than incorrectly declaring g good for an arbitrary maximal sequence.
Finite-supremum attainment and the proved Mathlib support, dimension, and prime-avoidance
lemmas give the reductions directly. The existing good-sequence theorem supplies the
quotient depth and dimension. All imports have a statement or proof role; proof-only
imports are private. The old node's `proof_deps` was empty, so `No longer needed`
omits no former dependency. Read `dag/units/sk-thm-p1.json`, including `realized`: this
auxiliary result is below the unit's realized steps and alters none of their route.

5. **DAG agreement: pass.** Compared the existing node with the repository: only
`proof`, `proof_deps`, and `proof_origin` changed. Checked the new node's source,
statement dependencies, creation provenance, searches, blueprint origin, chapter,
unit, and verbatim Lean signature. For both nodes, `proof_deps` is exactly the union
of the proof steps' `uses`; each dependency resolves to its existing Lean declaration
or recorded Mathlib match. The four-step proof records follow the actual proofs.

**Second-reader changes:** Corrected the assigned theorem's stale module comment
and docstring: removed the claim that its construction is postponed, added the
source tags, and described finite dimension, the dimension-one base case, auxiliary
prime avoidance, quotient induction, and prepending. No proof, signature, import,
node, or definition needed repair. Added this review with the independent checks.
