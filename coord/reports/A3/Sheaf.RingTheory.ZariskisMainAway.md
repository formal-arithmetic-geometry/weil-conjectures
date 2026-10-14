## What changed

No Lean signature, import, definition, or DAG record changed. The sandbox
replaces the repository proof
`exact e.isOpen_image.mp (by simpa only [Set.image_singleton, IsQuasiFiniteAtPrime] using hq)`
by `rw [← e.isOpen_image, Set.image_singleton]; exact hq`. Both transport the
same canonical singleton. The assigned interface repair has already landed as
K2's conversion-only repair; this delivery retains the sandbox proof simplification.

## Proved and sorry left

`Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime` is already proved.
The sandbox copy compiles cleanly with lcompile.py. There are zero textual sorries
in the assigned module; holes closed in this delivery: none; holes added: none;
split-off statements: none. This is verification of a stale repair assignment,
not new proof progress.

## No longer needed

None newly pruned. All current imports remain necessary: QuasiFinite.Basic for
the public result, QuasiFiniteAtPrime for the public hypothesis, and
ZariskisMainTheorem privately for the singleton-fibre criterion. The localization
node is realized by the conversion helper together with Mathlib's
ZariskisMainProperty.of_finiteType in the existing callers. No unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The brief says this module still contains sorry, but the assigned baseline has
none. coord/repairs.txt still lists upstream review #1428, whose duplicate-wrapper
repair is already recorded as landed in
coord/changes/zariskisMainProperty-wrapper-removal.md and the K2 report.
The DAG's localization node now records Mathlib's of_finiteType, so searching for
this Sheaf module in lean.module correctly finds no node: the helper realizes
only its first proof step. The current proof transports exactly the canonical
singleton along preimageHomeomorphFiber and applies the finite-type criterion.
Its hypotheses match the definition for arbitrary commutative rings; zero rings
have no prime-spectrum inputs. No correction or forced adaptation remains.

## Second reading by A3

1. Compared the only delivered module with the repository using `diff -u`.
   Only the final two proof lines differ; all existing signatures, visibility,
   imports and docstrings are byte for byte unchanged. No change record is needed.
   Verdict: pass. The first report's claim of no Lean change was inaccurate.
2. Compiled the delivered file with lcompile.py: clean, no warnings or errors.
   Scanned the source: no sorry, axiom, unsafe, opaque, implemented_by or extern;
   no new definition or witness choice. Compiled a scratch copy with
   `#print axioms Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime`:
   exactly propext, Classical.choice and Quot.sound. Verdict: pass.
3. No split-off statements, new declarations or new nodes exist. Read
   IsQuasiFiniteAtPrime and Mathlib's QuasiFiniteAt.of_isOpen_singleton_fiber:
   the hypothesis is precisely openness of the homeomorphism image of the
   canonical singleton, so the conversion is valid over arbitrary commutative
   rings. A zero source or target ring admits no relevant prime input; for the
   identity of a field the singleton fibre is open and the result holds.
   No duplicated localization conclusion remains. Verdict: pass.
4. The proof is already a direct application of the existing Mathlib criterion
   after transporting openness; no new intermediate result is needed.
   QuasiFinite.Basic and QuasiFiniteAtPrime supply public types;
   ZariskisMainTheorem supplies only the proof and is a plain import.
   No import was removed and no old proof dependency became unused.
   Read sk-thm-p1.json, including realized: this helper is below the unit's
   steps, and the existing callers still use it followed by Mathlib's
   ZariskisMainProperty.of_finiteType. No unit route is bypassed. Verdict: pass.
5. Read lem-weil-pbc-integral-closure-zariski-main-away.json and the landed
   wrapper-removal change record. The node's first proof step describes exactly
   this conversion; its Lean record correctly names the Mathlib localization
   result, not this helper. Its proof_deps and proof_origin agree with that
   two-step route. There are no delivered node changes. Verdict: pass.

Second reading changed only this report: corrected the proof-diff description
and recorded independent compile, axiom, interface, import and DAG checks.
No additional Lean repair was necessary. Net holes closed: 0; added: 0.
