## What changed

Replaced the sole proof hole in `Sheaf.RingTheory.GradedNakayamaFree` with a complete Lean
reduction. The existing theorem signature and docstring are unchanged. Construct a minimal
presentation, apply `exists_minimalPresentationTor_equiv` to `hTor`, apply
`graded_kernel_finite`, inherit the internal grading on the kernel, apply
`subsingleton_of_graded_quotient_subsingleton`, and transport the source basis along the
resulting linear equivalence. The internal kernel grading is proved by a private helper:
componentwise inclusion proves independence, and ambient homogeneous component sums prove
surjectivity. No helper has a hole.

Added `Sheaf.RingTheory.MinimalGradedPresentationExists` with the strictly earlier construction
of a minimal graded presentation, without any Tor assumption or freeness conclusion for N.
Updated the existing node's proof, proof dependencies and proof origin. The new construction
module imports the existing graded generation theorem for its planned proof. Mathlib searches
found finite-dimensional basis and ungraded/local-ring tools, but no exact graded presentation
constructor. LeanSearch returned HTTP 500, recorded as unavailable.

Both modules compile locally in import order without warnings. Tested the construction in
words on N=0 (empty basis), S with any integer shift (rank one identity presentation), and
N=k (rank one evaluation presentation with nonzero kernel). Thus the new statement does not
assume or assert the Tor vanishing or target freeness conclusion.

## Proved and sorry left

Closed: `MvPolynomial.graded_nakayama_free` (node
`lem-sc-p1-graded-nakayama-free`). This is a decomposition, not an unconditional proof:
one upper hole is closed and one lower hole is added, net zero holes for this delivery.

Added and left: `MvPolynomial.exists_minimal_graded_presentation` (node
`lem-sc-p1-minimal-graded-presentation-exists`). Its proof is exactly `by sorry`, with a
complete construction in its docstring and node. No sorry remains in the item's module.
The existing imported dependencies `MvPolynomial.exists_minimalPresentationTor_equiv`,
`MvPolynomial.graded_kernel_finite`, and
`MvPolynomial.subsingleton_of_graded_quotient_subsingleton` retain their existing holes;
this delivery does not change their modules.

## No longer needed

Removed the proof-only import
`WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules` and its direct proof
edge `def-weil-pbc-proj-twisting-sheaf`. The conclusion is explicitly a homogeneous module
basis, so transporting a basis needs no sheaf twist construction. The definition node stays
in stmt_deps, unchanged, because it is still cited by the existing natural-language statement.
No unit statement or realized unit proof step is bypassed.

All three previous genuine proof dependencies remain: graded generation (the zero-quotient
clause), minimal-presentation Tor, and finite graded kernels. No other DAG node is pruned.
The second reading made `Sheaf.RingTheory.MinimalPresentationTor` proof-only, removed
the redundant explicit `Mathlib.Algebra.Category.ModuleCat.Basic` import and the unused
explicit `Mathlib.LinearAlgebra.Quotient.Basic` import. Quotient operations used only by
the proof remain available through its private dependencies. Added proof-only imports for
the new construction and Mathlib finiteness tools. In the new construction module, replaced
the unused public `MinimalGradedPresentation` import with the Mathlib modules its statement
actually needs. This does not prune that definition module from the target closure: the Tor
calculation still uses it. No other proof edge or unit route changes.

## Where the brief, the DAG or earlier work was wrong

The DAG's step 1 requires a minimal presentation, but the existing library supplies only its
data structure and the graded generation criterion, not an existence theorem. The new node
states that missing construction. `FiniteHomogeneousGenerators` supplies a surjection, but
neither a minimality clause nor an internal source grading; it cannot directly fill this gap.
The kernel theorem gives homogeneous components and ambient spanning elements; it does not
supply an internal grading of the kernel as a type. That glue is fully proved here.

The blueprint source document is not present in this read-only clone. The parent DAG retains
its original blueprint statement: it cites graded Hilbert syzygy rather than spelling out this
minimal-presentation argument. The new node therefore identifies its proof as the standard
agent-written expansion of step 1 of the existing freeness node, not a quotation from that
unavailable blueprint file. No existing statement or definition was changed.

## New nodes

`lem-sc-p1-minimal-graded-presentation-exists`, in
`dag/nodes/sec-picard-framework/lem-sc-p1-minimal-graded-presentation-exists.json`, records
`MvPolynomial.exists_minimal_graded_presentation` in
`lean/Sheaf/RingTheory/MinimalGradedPresentationExists.lean`. Its parts are finite residue
basis selection, the shifted coordinate grading on a finite free module, surjectivity via
existing graded Nakayama, and minimality via residue-basis independence. It needs no Tor
hypothesis. The target proof combines it with independent existing Tor and kernel-vanishing
statements. Import visibility corrections from the second reading are recorded in
`coord/changes/GradedNakayamaFree-imports.md`; all existing signatures and definitions
are unchanged.

## Second reading by P2

1. PASS. Read the full diff against the repository. The existing
   `MvPolynomial.graded_nakayama_free` signature is byte-for-byte identical (checked by
   extracting the text before `:= by`), and its docstring is unchanged. No existing
   definition or statement changes. The import-interface change record is
   `coord/changes/GradedNakayamaFree-imports.md`, as required by the dry-run preflight.
2. PASS. Both delivered files compile locally in import order without warnings. Scratch
   copies with `#print axioms` show only `propext`, `Classical.choice`, and `Quot.sound`
   for the private inherited-grading helper; the freeness theorem and the construction
   additionally use `sorryAx`, exactly as expected from the listed open statements.
   There is one new named theorem hole and no hole in a definition or partial proof.
   No axiom, unsafe, opaque, implemented_by, or extern declaration occurs. The existential
   presentation is eliminated only inside a theorem proof, never used to define data.
3. PASS. Independently checked the minimal-presentation statement and its full docstring
   proof. For N=0 use rank zero; for a shift of S use the identity with rank one; for
   N=k use constant-coefficient evaluation, whose inverse image of IN=0 is IF. Arbitrary
   positive and negative shifts are allowed, and finite generation bounds degrees below.
   The quotient basis can be extracted from images of the original homogeneous generators;
   hence each basis element retains a homogeneous lift. Minimality follows from their
   residue-class independence, with no freeness or Tor hypothesis imposed on N. This is
   strictly the presentation-construction part of the original argument, not a restatement
   of the freeness criterion. Independent LeanFinder search for homogeneous generators,
   residue bases, and minimal free covers found graded algebra generation results, not this
   graded module constructor. Loogle search for `DirectSum.IsInternal, Submodule` and grep
   for internal comaps and free covers found no shorter matching restriction lemma: the
   Mathlib biSup restriction result concerns scalar submodules and a restricted index set,
   not a homogeneous submodule with additive degree pieces. Searches of both source roots
   likewise found no minimal graded presentation constructor. The new hole requires a
   substantial quotient-basis and shifted-coordinate construction, not a few-minute repair.
4. PASS after import corrections. The target reduction follows the existing top-down route:
   minimal presentation, Tor kernel quotient, finite homogeneous kernel, graded Nakayama,
   and basis transport. Read `dag/units/sk-thm-picard-duality.json`: its realized statement
   and step lists are empty; this delivery changes neither the unit route nor any realized
   node. The removed twisting-sheaf proof edge is the only old proof dependency not used.
   All other old proof dependencies remain, and `No longer needed` now also records the
   redundant imports removed in this reading. Import pruning does not assert that any
   entire module has become unreachable from all targets.
5. PASS. Existing node changes are confined to proof, proof_deps, and proof_origin, matching
   the actual Lean reduction and the four nodes it uses. Read every field of the new node:
   its declaration and verbatim statement agree with Lean; its source honestly identifies
   the agent expansion of the parent proof step; its proof steps and dependency union,
   searches, status, creation record, blueprint provenance, chapter, and unit are present.

Changes in this reading: corrected proof-only and redundant imports in both delivered
modules, updated the import-pruning report, added the required import change record and verified the unchanged direct importer
`Sheaf.RingTheory.GradedSyzygy` against the sandbox module (clean compile), and added this
independent review. No mathematical
proof body, declaration signature, or new node statement needed repair. One upper hole closed
and one strictly earlier hole added remains a decomposition, with net zero holes.

The import change record lists every one of the 182 transitive downstream modules reported
by the read-only dependency tool; the sole direct importer uses a private import, so the
visibility change does not propagate through it. No downstream adaptation is necessary.
