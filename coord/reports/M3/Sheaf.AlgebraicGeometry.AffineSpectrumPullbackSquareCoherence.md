## What changed

Replaced the first worker's unfolded restatement with a proof of
`AlgebraicGeometry.affineSpectrum_pullback_square_coherence` from the selected composition
isomorphisms and their associativity law. Private helpers establish equality transport,
compatibility of forward comparisons with composition, the commutative-prism calculation,
and naturality for the arbitrary morphism `k`. No public signature, definition, import,
or file-level option changed.

Identifying the forward comparison first as an isomorphism, then taking its component,
avoids expensive repeated conversion of the choice-based definitions. The final file compiles
within the single-file limit, with no warnings. No heartbeat or time limit is increased.

Updated the existing node's proof, proof_deps, and proof_origin to match this calculation.

## Proved and sorry left

Closed: `AlgebraicGeometry.affineSpectrum_pullback_square_coherence` (one of one original holes).

Added holes: none. Holes remaining in delivered Lean: none.

Removed the undelivered `affineSpectrum_pullback_square_coherence_core` restatement and its
node `lem-pc-affine-spectrum-pullback-square-coherence-core`; they were introduced by the first
worker and are not present in the repository. This is a proof, not a decomposition.

A scratch copy with `#print axioms AlgebraicGeometry.affineSpectrum_pullback_square_coherence`
compiled and reported exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## No longer needed

No import or module is pruned: both public imports supply declarations in the unchanged
statement. The old direct proof dependency `def-pc-affine-spectrum-derived-coordinates` is
unused by the calculation and removed from proof_deps; it remains a statement dependency
and is still available transitively. Added `lem-pc-scheme-derived-mate-evaluation` to
proof_deps because its canonical composition and square-comparison definitions are used.

The first worker's undelivered core node is deleted, not a pruned library module.

## Where the brief, the DAG or earlier work was wrong

The first worker's core identity was exactly the original statement after unfolding
`canonicalDerivedSquareComparison`, with identical hypotheses. Its one-line application
was not a genuine reduction and closed no mathematical obligation. It also lacked the
required complete natural-language proof in its docstring. The replacement uses the
existing associativity theorem and proves all intermediate calculations.

The original DAG proof dependency list omitted the canonical square-comparison definitions
actually used and included a direct dependency unused by this proof; the list is corrected.

## Second reading by M3

1. Compared the delivered module with the repository by diff and checked the original theorem
   signature byte for byte. Verdict: unchanged hypotheses, conclusion, universes, visibility,
   imports, and existing definitions. No target statement or other module is edited.
2. Compiled the final file through lcompile.py using a scratch copy with an axiom print.
   Verdict: clean compilation; no sorry or forbidden declaration; the target
   uses only propext, Classical.choice, and Quot.sound. The private forward comparison is
   constructed from the existing canonical isomorphisms, with no arbitrary existence witness.
3. Checked the first worker's split-off identity and rejected it as a restatement. It and its
   node are removed. There are no split-off statements left. Searches by equality transport,
   pseudofunctor composition coherence, and forward-comparison terminology found generic
   Mathlib building blocks, not a shorter existing theorem for this selected scheme comparison.
   The generic prism calculation allows arbitrary scheme maps and uses only its stated face
   equalities: identity maps, zero objects, and noncartesian commutative squares are not excluded.
4. Checked the top-down route and imports. Verdict: associativity of the existing selected
   composition gives the proof, followed by naturality; no lower hole or alternate coordinate
   construction is introduced. Both imports occur in the signature. The unit
   dag/units/sk-thm-picard-semicon.json has empty realized statement and step lists; no realized
   unit step is bypassed or changed.
5. Read the original node and its dependency declarations against the Lean calculation.
   Verdict: updated proof, proof_deps, and proof_origin agree with the code; existing statement,
   stmt_deps, and lean signature fields are unchanged. No new nodes or change records are needed.

Second reading changed: removed the unfolded core restatement and its node; supplied the full
coherence proof with proved private helpers; corrected the original node's proof metadata;
replaced the report with accurate hole accounting and this independent review.

The delivery dry run passed: the only CODEX classification reason is the changed node file.
The temporary private section and diagnostic options were removed before that passing run.
