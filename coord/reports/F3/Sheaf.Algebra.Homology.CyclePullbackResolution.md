## What changed

Preserved the signature and docstring of
`CochainComplex.exists_functorial_cyclePullback_construction`. Its complete Lean proof now
unpacks a recursive construction, proves the comparison epic using the cover hypothesis,
and applies a proved local lifting theorem at or below the bound. Above the bound it directly
uses zero targets to supply the identity cover and zero lift. Added two proof-only imports:
`Sheaf.Algebra.Homology.CyclePullbackCore` and `Sheaf.Algebra.Homology.CyclePullbackLifting`.

The core interface does not require hpi and does not assert either epimorphicity or local
lifting. It identifies each constructed term at or below N with T applied to the actual
pullback of the target differential and next kernel. The cover followed by the projections
defines the augmentation and differential. The final proof uses the missing hpi hypothesis to
make that comparison epic. This separates the purely recursive assembly from the epimorphic
lifting argument; the core is not the original theorem with its lifting clause renamed.

The lifting module proves the local step from an epic comparison and its two projection
equations: factor the cycle through its kernel, form the compatible pair's map to the
pullback, and pull back the epic comparison along it. Mathlib proves the new projection epic;
its pullback equation gives both required lift equations. No data definition chooses arbitrary
witnesses from an unproved existence theorem: witnesses are unpacked only in theorem proofs.

The original node's proof and proof dependencies now follow this route. All three modules
compile together without warnings using lcompile.py. All Lean lines have at most 100 characters.
There are no interface changes to existing modules and no forced adaptations.

## Proved and sorry left

Closed one original hole:
`CochainComplex.exists_functorial_cyclePullback_construction`
(node `lem-pc-functorial-cycle-pullback-construction`).

Added one hole:
`CochainComplex.exists_functorial_cyclePullback_core`
(node `lem-pc-functorial-cycle-pullback-core-stage3`). This theorem still needs the descending
recursive construction and its functorial assembly, for an arbitrary natural transformation
pi without epimorphicity. Its exact whole proof is `:= by sorry`; the docstring gives the source
and complete construction argument.

Proved without sorry:
`CochainComplex.cyclePullback_lifting_pointwise`
(node `lem-pc-functorial-cycle-pullback-lifting-stage3`). This lemma requires an epic comparison
to the explicit kernel-pullback and proves the generalized-element local lifting consequence.

This is a decomposition: one hole closed and one added, net zero, with a complete proof of the
original plan's local lifting step and of the zero case above the bound. The full construction
is not yet proved without sorry.

## No longer needed

No original imports, nodes or modules are pruned: the original node had no proof dependencies,
and its three public Mathlib imports remain needed by its signature. Both added proof-only
imports are used.

The earlier arbitrary-Q lifting theorem and weak core interface are rejected and unused.
Their files remain only in scratchpad/rejected-decomposition; neither is delivered. The
construction, local lifting and functoriality parts of the original plan all remain: the first
and third are the remaining core item, and the second is proved here. The unit record has empty
realized statement and step lists, and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier lifting theorem is false because boundedness and membership in S alone give no
relation between Q and the target. This delivery supplies an actual term identification with
T of the kernel-pullback and the projection equations, without assuming the lifting result.
For the earlier zero-Q/nonzero-F counterexample, the comparison to the degree-zero pullback
would have to be zero. Its factorization as an isomorphism followed by epic pi forces it to be
epic, which is impossible. The proved lifting theorem is valid for arbitrary E,F precisely
because it explicitly assumes an epic comparison and both projection equations.

The core works even with non-epic pi: assembly and square-zero need only factorization through
the kernel and the pullback condition. It says nothing about lifting or quasi-isomorphisms.
Above N, there is no asserted identification with T of a zero pullback: T need not preserve
zero. Instead the final proof uses the two bounds directly. Neither additivity nor exactness
of T is assumed. The term property S is not assumed invariant under isomorphisms; the actual
recursive construction uses terms T(P), so hT applies before its indices are assembled.

The original node's proof steps have empty uses, so no stated recursive dependency lemma was
available to import. The source TeX is absent from this checkout. Read the primary sources at
https://stacks.math.columbia.edu/tag/05T7 and https://stacks.math.columbia.edu/tag/06YS.
The former gives the descending kernel-pullback induction; a fixed functorial cover gives its
natural variant via kernel/pullback uniqueness. LeanFinder returned eight related hits with no
exact construction match. Loogle's queried short identifier was unknown. LeanSearch returned
Internal Server Error and is recorded as unavailable. Local Mathlib searches found the kernel
and pullback lemmas used in the local proof.

## New nodes

`lem-pc-functorial-cycle-pullback-core-stage3`, realized by
`Sheaf.Algebra.Homology.CyclePullbackCore`, states the recursive construction and term
identifications without any epimorphism hypothesis or lifting conclusion. This is the one
new proof item, with an exact signature, source, complete prose proof and search records.

`lem-pc-functorial-cycle-pullback-lifting-stage3`, realized by
`Sheaf.Algebra.Homology.CyclePullbackLifting`, states and completely proves the strictly local
consequence of an epic comparison, using Mathlib. No change record is necessary: all existing
signatures and visibility are preserved; the assigned module's new imports are proof-only.

## Second reading by F3

1. PASS. Compared the delivered resolution with the repository using diff, then compared
   the existing theorem signature as bytes. Only its proof and the two plain proof imports
   change; its docstring, visibility, hypotheses and conclusion are identical. The other
   two modules are new and have their own nodes. There are no definition changes or forced
   adaptations and no change record is required.
2. PASS, as a decomposition. Compiled all three files in import order through lcompile.py
   without errors or warnings. Scratch copies with explicit #print axioms show only
   propext, Classical.choice and Quot.sound for cyclePullback_lifting_pointwise; the core
   and resolution also use sorryAx from the single remaining named core theorem. Inspected
   every declaration: no forbidden axiom/unsafe/opaque/extern/implemented_by, no definitions
   choosing arbitrary witnesses, and no hidden proof holes. The remaining hole has source,
   construction proof in words and a matching node.
3. PASS. Read both new statements against their nodes and the actual kernel/pullback proof.
   The core is the recursive assembly step, with no epic-cover hypothesis and no local
   lifting conclusion; it is not a renamed target. It remains true when pi is zero, when T
   does not preserve zero, and when S is not invariant under isomorphism: set terms literally
   to T of the pullbacks below N and to a zero object above N. In degree N the next terms
   vanish, so the construction still applies. Functoriality uses naturality of pi and the
   universal properties; additivity of T is unnecessary. The lifting statement now requires
   an epic map to the actual cycle-pullback, excluding the earlier zero-Q/nonzero-F
   counterexample. Its proof explicitly constructs the required cover by pulling back e.
   Repeated semantic search with the different query "Construct a functor on bounded above
   cochain complexes by descending induction using a functorial cover of a fiber product
   with cycles": LeanFinder returned eight nonmatching hits (single functors, mapping
   cones, t-structure support and cm5b.I). Read CM5b: it requires enough injectives and does
   not provide this fixed-T descending assembly. Loogle query pullback.lift was unresolved
   by the service; local rg located the genuine pullback.lift/lift_fst/lift_snd declarations.
   Searched lean/Sheaf and lean/WeilConjectures for kernel-pullback and descending/functorial
   resolution constructions; no exact existing theorem supplies the remaining core.
   Read Stacks 05T7 directly for the descending pullback argument; 06YS is broader context.
4. PASS. Read the proof top down: assembly, epic comparison, proved pointwise lifting;
   above N use the two zero targets and the identity cover. Both new imports are plain
   proof imports and both are used. Existing public imports provide the original signature.
   Old proof_deps was empty, so No longer needed correctly lists no removed dependency.
   Checked dag/units/sk-thm-picard-semicon.json: its realized statement and step lists are
   empty; this reduction retains the original construction/lifting/functoriality route and
   bypasses no recorded unit step. The difficult assembly cannot be closed in a few minutes.
5. PASS after metadata repair. The original node depends on exactly the core and local
   lifting nodes, and its two proof steps agree with the final Lean proof. Both new nodes
   have source, prose proof, searches, creation and blueprint metadata. Corrected their
   lean.statement fields to the exact multiline Lean signatures, and corrected the lifting
   proof_origin place to the local lifting step rather than the unrelated functorial assembly.

Second reading changed metadata and this report only; the three Lean modules were sound
and did not need rewriting. Archived stale nested rejection reports under scratchpad so
that report.md is the unambiguous current delivery report. One original hole is replaced
by one strictly structural hole: net zero, a decomposition, not a completed construction.
