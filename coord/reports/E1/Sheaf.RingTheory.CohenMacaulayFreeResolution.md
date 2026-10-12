## What changed

The existing declaration
`IsLocalRing.exists_finite_free_resolution_to_maximalCohenMacaulay` keeps its signature
byte for byte. Its proof now first proves the finite depth bound using
`IsLocalRing.depth_le_supportDim` and Mathlib's
`Module.supportDim_le_ringKrullDim`, extracts the natural number e, constructs a
sequence of length d-e, and applies the first-term depth lemma.

The new construction declaration `IsLocalRing.exists_finite_free_resolution_data`
is now a generic arbitrary-length finite free sequence statement: it has no local,
nontrivial, dimension or Cohen--Macaulay hypothesis and makes no depth assertion.
The new declaration `IsLocalRing.first_term_is_maximalCohenMacaulay` now requires
ringKrullDim R=d, depth R≥d, depth M=e and e≤d. The first worker omitted all four
conditions, making that statement false. The caller now passes all four proofs.
Both new theorem docstrings give sources and complete natural-language proofs.
Both new nodes now have self-contained statements, dependency-bearing proof steps,
proof origins, and recorded searches. There are no changes to definitions and no
change records are needed for these previously undelivered new declarations.

The proof-only import `Sheaf.RingTheory.DepthInSES` was removed from the parent
module; it remains imported by the new depth-shift module. All new imports in the
parent are plain `import`, because they are used only in the proof. Public imports
are the original imports needed by its signature.

## Proved and sorry left

Upper hole closed, by a decomposition:
`IsLocalRing.exists_finite_free_resolution_to_maximalCohenMacaulay`
(node `lem-weil-pbc-cm-local-free-resolution-to-mcm`). No sorry remains in this module.

Two lower holes added:

- `IsLocalRing.exists_finite_free_resolution_data`
  (node `lem-weil-pbc-cm-local-free-resolution-construction`), generic finite free
  sequence construction for any prescribed length.
- `IsLocalRing.first_term_is_maximalCohenMacaulay`
  (node `lem-weil-pbc-cm-local-free-resolution-mcm`), depth estimate for an already
  given exact sequence.

Each remaining sorry is the whole proof of a public named theorem, in its own new
module. There is no sorry inside a definition and no data construction from an
arbitrary witness of an unproved existence theorem. The existential witnesses in
this proof are used only to prove another proposition.

This is a decomposition, not a fully proved module or positive net proof progress:
one upper hole closed minus two lower holes added gives net -1 holes. The original
combinatorial and depth arguments are separated into strictly different tasks.
Neither helper restates the parent theorem. Neither remaining task can be closed
by a direct library lemma found in the searches; the categorical finite truncation
and the induction on syzygies remain to be formalized.

## No longer needed

Removed direct import: `Sheaf.RingTheory.DepthInSES` from the parent module only.
No module is claimed globally pruned: this module remains needed by the MCM helper.

The old parent proof_deps not present in its new direct proof_deps are all listed
here, with their destination in the decomposition:

- `def-weil-finitely-generated-module`: construction's finite generators.
- `def-weil-pbc-depth`: MCM helper's free-module bound and depth induction.
- `def-weil-pbc-exact-sequence`: both helpers' exactness arguments.
- `def-weil-pbc-free-module`: both helpers' finite free modules.
- `def-weil-pbc-regular-sequence`: MCM helper's componentwise regularity argument.
- `lem-weil-pbc-noetherian-submodule-finite`: both helpers' kernel finiteness.
- `lem-weil-pbc-depth-in-ses`: MCM helper's depth induction.

These dependencies are moved below the parent, not removed from the proof route.
`lem-weil-pbc-depth-le-support-dimension` and
`def-weil-pbc-krull-dimension-ring` remain direct parent proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The first worker's first-term lemma was false. Take a field R and M=R with d=e=1:
there are no free terms, and the sequence 0 → M → M → 0 with identity map meets
all its old hypotheses. Its nonzero first term has depth zero, not one. There was
no relationship between d and dim R, no Cohen--Macaulay condition on R and no
relationship between e and depth M. Supplying those missing assumptions in the
new helper repairs it without changing any existing declaration.

The initial new-node records were not reviewable: their statements referred to
"the same hypotheses", their searches were empty, their proofs had one unspecified
step with no dependencies, and their docstrings had no complete proof in words.
These defects were repaired. The initial report also counted an upper proof
without saying that two new lower holes were added; the accounting above corrects
that description.

The source algebra.tex is not present in this machine's read-only project.
The second reader checked the official source pages instead:
[00LP](https://stacks.math.columbia.edu/tag/00LP),
[00NG](https://stacks.math.columbia.edu/tag/00NG) and
[00NE](https://stacks.math.columbia.edu/tag/00NE).
The existing DAG's 00LX and 00LK declarations supply the depth inequalities and
upper bound. LeanSearch returned Internal Server Error; this is recorded as
unavailable, and the LeanFinder, Loogle and local grep searches were still made.

## New nodes

`lem-weil-pbc-cm-local-free-resolution-construction`, in
`Sheaf.RingTheory.CohenMacaulayFreeResolutionConstruction`, is the finite
successive-surjection construction of Tag 00LP, for any length, with no depth claim.
Its induction is fully described in its docstring and node. At length zero it uses
an identity map; the construction also allows M=0.

`lem-weil-pbc-cm-local-free-resolution-mcm`, in
`Sheaf.RingTheory.CohenMacaulayFreeResolutionMCM`, applies the 00NE/00LX depth
induction to a given sequence and the 00LK upper bound to its final nonzero kernel.
Its docstring handles zero syzygies and zero free terms explicitly. At e=d the
sequence identifies K with M; at d=0 all nonzero finite modules have depth zero.

## Second reading by E1

1. Compared the delivered parent module with the repository using diff and a
   byte-for-byte signature comparison. PASS: its existing declaration is unchanged;
   only its proof and proof imports change. Both other modules and their declarations
   are new. No definition, target statement or public import was changed. Searched
   coord/changes for the module and declarations; no applicable record was found.
2. Compiled all three modules through lcompile.py in import order. PASS: no errors
   or warnings. Scanned for forbidden declarations/attributes and counted the holes:
   zero in the parent, one whole-theorem sorry in each new module. Scratch copies
   with #print axioms check all three declarations; only the three permitted axioms
   and sorryAx from the reported open statements occur. No hollow definition exists.
3. REPAIRED: the original first-term lemma failed the length-zero field example.
   Added precisely the dimension, ring depth, module depth and e≤d assumptions used
   by the caller. Separated depth selection from generic sequence construction.
   Checked k=0, e=d, d=0, zero intermediate kernels and rank-zero free terms.
   Repeated searches with different wording via msearch.py (LeanFinder, Loogle,
   grep, and unavailable LeanSearch), and rg on Sheaf and upstream Lean. The existing
   Module.exists_finite_free_resolution is an infinite linear-map sequence, not this
   categorical finite truncation; Mathlib's Module.exists_finite_presentation is one
   surjection. Neither directly proves the construction statement. No existing
   theorem proves the corrected syzygy depth estimate. Both helpers are true strict
   parts, with complete proof docstrings and nodes; neither restates the original.
4. PASS after repair: the shortest available depth bound is now used in the parent.
   Construction and depth shifting still follow the original node's finite-surjection
   and depth-lemma route. Read dag/units/sk-thm-p1.json: this auxiliary ring-theory node
   is not a statement or step listed in its realized fields. No unit realization was
   removed or changed; no chapter or unit route was replaced. Imports are minimal
   for the unchanged public signature and the proof/dependency plans; every old
   dependency removed from the parent's direct list is accounted for above.
5. REPAIRED: updated the parent's proof, proof_deps and proof_origin to its actual
   three-step reduction; no other existing-node field changed. Rewrote both new-node
   statements and proof steps, made proof_deps exactly the union of uses, supplied
   all required searches and creation/source/blueprint/Lean fields, and synchronized
   lean.statement with the actual new signatures. Verdict: a valid decomposition
   with two reported lower holes and no claim of positive net hole progress.

Second reading changed: false helper assumptions, generic construction statement,
explicit parent depth-bound proof, dependency imports, both new node records and
proof docstrings, and report/accounting. No existing signature changed.
