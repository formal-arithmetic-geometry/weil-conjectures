## What changed

Replaced the sole sorry in `MvPolynomial.graded_kernel_finite` with a proof following the
existing two-step DAG plan. A componentwise additive map on the direct sums commutes with
`q`, by decomposing into a finite sum and using degree preservation. Comparing components
when `q x = 0` proves that `q.ker` is homogeneous. Applying
`MvPolynomial.graded_submodule_finite` then supplies the finite homogeneous generators.
The theorem signature, docstrings, imports, and DAG route are unchanged.

## Proved and sorry left

Closed the one direct hole: `MvPolynomial.graded_kernel_finite`
(node `lem-sc-p1-graded-kernel-finite`). No direct sorry remains in the item; no holes were
added or split off. This proof uses the existing sorry-bearing declaration
`MvPolynomial.graded_submodule_finite` (node `lem-sc-p1-graded-submodule-finite`), which is
not changed by this delivery. It is a proof from the existing planned dependency, rather
than an axiom-free proof of the whole transitive closure.

Compilation with the prescribed local compiler succeeds without warnings. The kernel
argument uses only the internal decompositions and degree preservation, and therefore also
handles the zero map, identity map, and zero modules. Surjectivity and finiteness of the
codomain are unnecessary to this argument, but their existing binders are preserved.

## No longer needed

None. The sole proof dependency `Sheaf.RingTheory.GradedSubmoduleFinite`
(node `lem-sc-p1-graded-submodule-finite`) is used. All three public Mathlib imports remain
needed by the existing statement. No nodes or modules of the planned route are bypassed.

## Where the brief, the DAG or earlier work was wrong

None. The DAG's elementary kernel-grading step is implemented directly with
`DirectSum.sum_support_decompose`, `DirectSum.decompose_of_mem`, and `DirectSum.map`.
The second step uses exactly the stated graded-submodule finiteness lemma.

## Second reading by K2

1. PASS — Compared the entire delivered module with the repository by `diff -u`.
   Only the body of `MvPolynomial.graded_kernel_finite` changes. Its signature,
   all binders (including surjectivity and codomain finiteness), conclusion,
   docstrings, module header and imports are byte-for-byte unchanged. There are
   no other delivered modules, definitions, new statements or change records.
2. PASS — Recompiled the module with the prescribed `lcompile.py`: exit 0,
   no warnings, about 2 seconds. Scanned the delivered Lean for `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, `extern` and kernel-check bypasses:
   none occur. A scratch copy with `#print axioms MvPolynomial.graded_kernel_finite`
   compiles and reports exactly `propext`, `Classical.choice`, `Quot.sound`,
   and `sorryAx`. The last is expected from the unchanged imported theorem
   `MvPolynomial.graded_submodule_finite`; this is not an axiom-free closure.
   Read the component map `g`, the finite decomposition identity `hmap`, and
   the componentwise kernel argument `hK`: degree preservation places each
   image in the correct summand, uniqueness of the codomain decomposition
   forces every image component to vanish, and the chosen source decomposition
   is exactly the one in the unchanged conclusion. The final application
   supplies precisely the finite homogeneous set and span equality required.
3. PASS — No statements were split off and no holes were added, so there are
   no new statement docstrings or nodes to validate. The existing dependency
   is strictly more general than this item's finite-generation part and is
   applied with `N = F`, `K = q.ker`, `_hsmulF`, `_hfiniteF` and `hK`.
   Checked zero modules, identity map (zero kernel), and the zero map with
   zero codomain (whole source kernel): neither the component argument nor
   the finite-generation application excludes these cases or any shifts.
4. PASS — Searched again using LeanFinder for a degree-preserving map commuting
   with homogeneous projections, and `rg` for homogeneous kernels and grading
   maps in Mathlib and both library roots. Results concerned projections in
   graded rings/algebras, not an exact shorter theorem for these additive
   subgroup gradings. Read the Mathlib decomposition and homogeneous-submodule
   definitions and component-map lemmas. The current elementary argument is
   direct and uses the existing planned dependency. Each public Mathlib import
   supplies statement vocabulary: internal decompositions, polynomial
   homogeneous submodules, and homogeneous module submodules respectively.
   The Sheaf import is proof-only as required. Nothing in the old `proof_deps`
   is unused, so `No longer needed: None` is complete. Read
   `dag/units/sk-thm-picard-duality.json`: its `realized` fields are unchanged;
   no unit statement or step is bypassed.
5. PASS — Read `lem-sc-p1-graded-kernel-finite.json` and its dependency node.
   The Lean implements the existing elementary kernel-grading step and then
   invokes exactly `lem-sc-p1-graded-submodule-finite`. Thus the existing
   `proof`, sole `proof_deps`, and `proof_origin` already describe the delivered
   route; no node edit is needed. The node's integer-shift-compatible Lean
   statement agrees with the preserved theorem signature.

Changes by the second reader: appended this independent review and axiom-check
results to the report. No repair to the proof, imports, statements or nodes was
needed. One original direct hole closed, zero holes added, zero split off;
no imported modules pruned.
