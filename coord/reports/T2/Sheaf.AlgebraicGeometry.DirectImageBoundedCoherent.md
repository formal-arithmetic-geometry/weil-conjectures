## What changed

Proved `AlgebraicGeometry.Scheme.directImage_isBounded_coherent` in the assigned
module, with its statement unchanged. The proof uses the truncation spectral
sequence, coherent higher direct images with proper support, and the finite maximum
of the individual cohomology-sheaf vanishing bounds. Coherence and zero-object
properties pass through the finite abutment filtration by a proved private induction.
Proper support is transported along the representative's homology isomorphism by
comparing its stalks. Updated the existing node to match these elementary inductions.
The support import uses the compatibility module, whose current source publicly
re-exports the original upstream module; see the change record.

## Proved and sorry left

Closed 1 original hole: `AlgebraicGeometry.Scheme.directImage_isBounded_coherent`
(node `lem-pc-direct-image-bounded-coherent`). Added 0 holes. There are no remaining
`sorry` declarations in the delivery, and no split-offs. Both private helpers are proved.
The statement retains independent source and target derived-category universes.

The assigned module compiles without warnings through `lcompile.py` in about 20 seconds.
The upper-bound argument also covers an empty source cohomology interval: the finite
supremum is then zero and every coefficient vanishes. No ordering of the input bounds
is assumed. The filtration induction includes length zero.

## No longer needed

Removed proof imports `Sheaf.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh`
and `Sheaf.CategoryTheory.HalfPlaneWeakConvergence`, and removed their nodes
`lem-pc-derived-direct-image-bounded-below-qcoh` and
`lem-sp-half-plane-weak-convergence` from this node's proof dependencies.
Their quasi-coherence and weak-convergence theorems are not used. The short generic
filtration induction and pointwise zero-page induction are proved directly here.
Removed the redundant public import
`Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`: it is already publicly
re-exported by the derived-category statement dependency. All remaining proof imports are used: in particular the direct-image Basic
module supplies `Scheme.Modules.isGrothendieckAbelian`.
No unit statement or unit proof step is bypassed; no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The shared source's QCoh helper is commented out as taken out by the upstream sync,
so the planned `import all` reuse cannot be relied on in current source. Its elementary
argument is proved locally for antitone subobject families, independently of the
filtration structure's upstream name. The weak-convergence module is now a re-export;
its private helper is unnecessary once the elementary kernel/quotient induction is
written at the point of use.

The original file also failed against the published build with duplicate support
constants: a direct upstream support import meets dependencies compiled with the
compatibility module. Replacing it by that compatibility module compiles and retains
the same public upstream export in current source. No definition or signature changes.

Change record: `coord/changes/T2-directImage-bounded-coherent-support-import.md`.


## Second reading by T2

1. Compared the complete delivered module with the shared repository using `diff`.
   The signatures of both existing theorems, including the private page helper, are
   byte for byte identical; no definition changes. The support public-import replacement
   is declared in the existing change record. Read both source modules: the compatibility
   module publicly re-exports the original, with only public imports already present there.
   Verdict: statements and exported meanings preserved.
2. Compiled the delivered module with `lcompile.py`, without warnings. Compiled a scratch
   copy with `#print axioms` for the main theorem and both private helpers: all three show
   only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   There are no `sorry`, axioms, unsafe declarations, opaque declarations, implementation
   overrides, or data definitions in the delivered module. The local existential choices
   occur only within a theorem proof. Verdict: one original hole closed, zero added.
3. There are no split-off statements or new public declarations. Checked the proved
   filtration induction at length zero and at its successor step, the empty interval
   case `b < a`, negative cohomological indices, and the finite-supremum bound.
   The choice of `N(q)` is a numerical bound inside a proof, not arbitrary object data
   installed in a definition. Verdict: no hidden decomposition or false edge case.
4. Read the higher-image coherence and vanishing declarations, the convergence source,
   and the retired QCoh helper. Searched upstream/Sheaf filtration and vanishing results,
   and used leanfinder and loogle for extension-closed object properties. No shorter exact
   result replaces this spectral-sequence argument. The old QCoh helper is commented out;
   the upstream private zero-page induction would add an unnecessary proof import.
   Removed redundant `HomologySequence` and recompiled the entire proof without it.
   Both removed DAG proof dependencies are listed under No longer needed. The unit record
   `sk-thm-picard-duality.json` has empty realized statement/step lists; it is unchanged,
   and no realized unit step is bypassed. Verdict: route and pruning checked.
5. Compared the existing node against its repository version. Only `proof`, `proof_deps`,
   and `proof_origin` change; the four remaining dependencies match the actual proof.
   Its statement, Lean declaration record, approved tool uses, chapter and unit stay intact.
   The node describes the coherence induction, homology/support transport, lower bound,
   finite upper bound and zero-page induction used in Lean. Verdict: metadata agrees.

Second-reading changes: removed the redundant public `HomologySequence` import,
recorded that removal and its unchanged public export, and appended this audit.
No mathematical proof or signature required repair.
