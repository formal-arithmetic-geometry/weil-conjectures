## What changed

In `lean/Sheaf/Paper/CartierEquality.lean`, removed the proof-only import
`Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`. Expanded its rank-nullity invocation
into the quotient-kernel/range linear equivalence and the quotient dimension formula,
which are already available from the retained imports. The theorem signature, public
imports, docstrings and complete-intersection argument remain unchanged.

The existing proof constructs a finite transcendence basis and a complete-intersection
fraction-field model, identifies cotangent homology with the kernel and differentials
with the cokernel of a finite-dimensional linear map, then combines the two dimension
formulas. The natural-number equality is cast to Cardinal; finite extensions have
zero transcendence degree. No unit statement or realized unit step is bypassed.

## Proved and sorry left

`cartier_equality` was already proved in the supplied checkout. There were zero direct
holes before this work and zero afterward: zero holes closed and zero holes added.
No new declarations or modules were introduced. The updated proof compiles cleanly
with the required `lcompile.py` wrapper.

## No longer needed

Removed the proof-only import `Mathlib.LinearAlgebra.FiniteDimensional.Lemmas` and the
invocation of `LinearMap.finrank_range_add_finrank_ker`. Its short argument now follows
from `LinearMap.quotKerEquivRange.finrank_eq` and
`Submodule.finrank_quotient_add_finrank`. Both complete-intersection dependency modules
remain needed. Removed `lem-weil-pbc-idempotent-charpoly-rank-nullity` from the item's
`proof_deps` and from step 3's `uses`: its Mathlib declaration is no longer
invoked. No Sheaf module is pruned. The elementary dimension step remains,
with its justification written directly in Lean.

## Where the brief, the DAG or earlier work was wrong

The brief says this module still contains `sorry`, but the supplied module has none
and compiles before any edit. Its node records a previous proof landing. The repair
queue still cites upstream review #1428 about `[Algebra.FiniteType k K]`; the supplied
signature already uses `(hfg : (⊤ : IntermediateField k K).FG)`, and the previous
change records document the correction. This delivery makes no further signature
change and claims no new proof progress. The second reader corrected the stale rank-nullity dependency in the DAG.

## Second reading by B4

1. PASS: compared the only delivered module with the repository using `diff -u`.
   The complete `cartier_equality` signature, docstring, visibility, and public
   imports are byte for byte unchanged. No definitions, declarations, hypotheses,
   or conclusions were changed or introduced; no change record is required.
2. PASS: the module compiles cleanly through `lcompile.py` (2.1 seconds).
   A scratch copy with `#print axioms cartier_equality` compiled and printed exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   The delivered source contains no `sorry`, forbidden declarations or attributes,
   or data definitions. The model witnesses are used inside a theorem proof.
3. PASS (not applicable): there are no split-off statements or new nodes.
   Independently searched `lean/Sheaf` and `lean/WeilConjectures` for the dimension
   formula and `cartier_equality`; only this declaration and its caller were found.
   A differently worded `msearch.py` grep search confirmed the quotient-kernel/range
   equivalence and quotient dimension formula used for the local rank-nullity step.
4. PASS: checked the complete-intersection and fraction-field cotangent declarations,
   the finite-basis Mathlib match, and `dag/units/sk-thm-p1.json` including `realized`.
   Both model lemmas are applied with the required regularity and domain hypotheses.
   Coordinate-space finiteness transports across the kernel/cokernel equivalences;
   the two dimension formulas and `c ≤ n`, `n-c=d` give the untruncated equality.
   The final finite-extension argument uses zero transcendence degree and injectivity
   of natural-number casts. The zero-dimensional case and positive transcendence
   degree require no extra hypotheses. The removed proof-only import is unnecessary;
   the retained public imports supply statement types and the retained proof imports
   supply the finite basis and both model steps. No realized unit step is bypassed.
5. PASS after repair: the node's steps match the Lean argument, and its remaining
   `proof_deps` are exactly the union of its step `uses`. The document origin remains
   valid. Removed the unused rank-nullity node from both fields and rewrote step 3
   to name the actual Mathlib equivalence and quotient formula.

Second reading changed the DAG dependency bookkeeping and this report only; the Lean
proof was already correct. There are no new holes and no newly closed holes: the
single theorem was proved before this delivery and remains proved.
