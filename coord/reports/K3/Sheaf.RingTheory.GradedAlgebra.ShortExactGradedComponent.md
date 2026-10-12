## What changed

Proved `DirectSum.shortExact_graded_component` without changing its signature,
docstring, or imports. A fully proved private helper `homogeneous_preimage` extracts
a homogeneous preimage for a degree-preserving additive map. It constructs the
componentwise direct-sum map, proves that it commutes with recomposition by
`DirectSum.induction_on`, and uses injectivity of target recomposition to identify
the required component. The main theorem follows the original three-step plan:
injectivity by subtype extensionality, exactness by homogeneous extraction, and
surjectivity by homogeneous extraction.

Searched with LeanFinder (homogeneous preimages), Loogle (`DirectSum.map`), and
Mathlib grep (`graded.*exact|exact.*graded|coeAddMonoidHom.*map`), plus local library
search. The direct-sum API provides all necessary tools; no matching full theorem
was found. Both existing public imports remain necessary for the statement.

## Proved and sorry left

Closed the sole hole in `DirectSum.shortExact_graded_component`
(node `lem-sc-p1-graded-degree-component-exact`). One of one original sorries
proved; zero holes added or split off; no sorry remains in this delivery.
The private helper `DirectSum.homogeneous_preimage` is fully proved.
Single-file compilation passed cleanly using the required `lcompile.py`.

## No longer needed

None. No imports removed and no planned dependency nodes bypassed. The existing
node has empty `proof_deps`; the proof realizes its three elementary steps using
Mathlib's direct-sum constructions. No additional Sheaf modules are imported.

## Where the brief, the DAG or earlier work was wrong

None. The statement and original proof route are unchanged. The proof only uses
additivity and the module decompositions; the ring grading and scalar grading
hypotheses remain unchanged in the signature. The argument also covers zero
components, zero modules, and arbitrary negative degrees: extraction is a direct
sum coordinate argument with no nonzero or positivity assumption.


## Second reading by K3

1. Compared the complete delivered module with the repository using `diff -u`.
   PASS: the existing theorem signature, docstring, public imports, and all other
   exposed text are byte-for-byte unchanged. The only additions are a private
   proved helper and the replacement of the theorem's `sorry` by its proof.
   There are no definition changes, change records, or other delivered modules.
2. Compiled the module cleanly with `lcompile.py`, and compiled a scratch copy
   with `#print axioms` for both declarations. PASS: each uses exactly
   `propext`, `Classical.choice`, and `Quot.sound`; neither uses `sorryAx`.
   Read every proof step: recomposition commutes with the componentwise map by
   direct-sum induction; target recomposition is injective; evaluation at the
   chosen degree produces the lift. Subtype extensionality then gives all three
   short-exactness clauses. No forbidden declaration or hollow definition occurs.
3. PASS: zero statements split off and zero holes added. The private helper is
   fully proved, strictly the homogeneous-lifting part of the argument, and
   requires no arbitrary choice of data from an unproved theorem. Checked zero
   components, the zero map with zero target element, sequences concentrated in
   one degree, and negative degrees: coordinate evaluation works uniformly.
   Independently searched Loogle for `DirectSum.IsInternal` and the local library
   and Mathlib for graded exactness and homogeneous lifting/preimages. The
   available internal-direct-sum API supplies the constructions used here;
   no shorter existing theorem matching this restriction result was found.
4. PASS: both public imports are needed by the existing signature
   (`IsInternal` and `Function.Exact` respectively); no proof-only public import
   was added. The old `proof_deps` is empty, so `No longer needed: None` is
   complete. Read `dag/units/sk-thm-picard-duality.json`: this subordinate lemma
   bypasses no realized unit statement or step, and follows its own original
   three-step plan without changing the unit route.
5. PASS: read `lem-sc-p1-graded-degree-component-exact` in full. Its statement,
   three elementary proof steps, empty `proof_deps`, source, and `proof_origin`
   agree with the Lean proof. No new nodes or node repairs are necessary.

Second reading changed only this report by recording the independent checks;
no mathematical or Lean repair was needed. One original hole closed, zero holes
added, zero split off, and no modules pruned.
