## What changed

Proved `Ring.projectiveDimensionLE_of_shortExact` using the bounded projective
resolution/Ext characterization and Mathlib's `ShortExact.hasProjectiveDimensionLT_X₁`.
Added a proof-only import of `Mathlib.CategoryTheory.Abelian.Projective.Dimension`.
Updated the sandbox node proof and proof dependencies to record this route.

## Proved and sorry left

Closed the only local hole, `Ring.projectiveDimensionLE_of_shortExact`; added no holes.
No sorries remain in the delivered module. The proof still depends on the existing
unproved `ModuleCat.hasProjectiveResolutionLE_iff_ext_vanishing`
(`lem-weil-pbc-projective-dimension-ext-characterization`), so its axiom check includes
`sorryAx`; this is a reduction to an existing dependency, not an axiom-free proof.

## No longer needed

The proof does not use the planned standalone short-exact Ext long-exact node
(`lem-weil-pbc-ext-long-exact-first-variable`) directly; Mathlib's projective-dimension
lemma packages that argument. No imports beyond the proof-only Mathlib import were
removed. The old proof dependency `def-weil-pbc-exact-sequence` is also no
longer used as a standalone proof node; short exactness remains a hypothesis,
provided by the retained public Mathlib import. Neither removed proof dependency
is a claim that an entire module leaves the targets’ import closure.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan was valid but unnecessarily expands the long exact Ext argument:
Mathlib already provides the exact projective-dimension bound for a short exact
sequence. The existing node statement and target signature are unchanged.


## Second reading by M3

1. PASS: diffed the only delivered module against the repository. The existing
   theorem signature is byte-for-byte identical; no definitions or visibility
   changed, and no change record is needed. Restored the original docstring.
2. PASS: locally compiled the module and an axiom-check scratch copy. No local
   sorry, axiom, unsafe, opaque, implemented_by, extern, or hollow definition.
   The axiom list is `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`,
   from the existing Ext-characterization dependency named above. Replaced
   `haveI` with `have` to remove style warnings and used `↦` in the lambdas.
3. PASS: no new declarations, split-off statements, or nodes. Checked the degree
   shifts at `m = 0`: the assumptions give Ext vanishing from degrees 1 and 2,
   and the conclusion is degree-1 vanishing, hence a projective resolution of
   length zero. Zero modules and arbitrary natural bounds require no exceptions.
4. PASS: read Mathlib's `hasProjectiveDimensionLT_X₁` and its Ext exact-sequence
   proof, and searched the upstream and Sheaf declarations for bounded-resolution
   and kernel-dimension alternatives. The upstream projective-middle-term lemma
   is a narrower Ext-form statement, not a replacement for this theorem. All
   imports are used: GlobalDimension and ShortExact supply the signature;
   ProjectiveResolutionExtCharacterization and Projective.Dimension supply the
   proof. The two removed old proof dependencies are listed above. The item is
   below the unit level; neither it nor the removed proof nodes realizes a step
   of `dag/units/sk-thm-p1.json`, whose realized route is unchanged.
5. PASS: compared parsed node records; only proof, proof_deps, and proof_origin
   changed. The single retained proof dependency is exactly the characterization
   used in Lean. The Mathlib candidate records the short-exact dimension lemma.
   No new-node obligations apply. Normalized JSON back to literal Unicode to
   avoid unrelated textual churn.

Second reading changed only proof style, restoration of the original docstring,
JSON formatting, and the report's pruning and axiom-dependency accounting.
