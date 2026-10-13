## What changed
Proved `AlgebraicGeometry.Scheme.Modules.coefficientTarget_generator_scalar` with the original
signature and imports. A proved private helper establishes the structure-sheaf scalar identity
by cancelling the canonical chart, rewriting restriction maps as appLE, and using the commuting
square. The main proof applies support-isomorphism injectivity, restriction scalar transport,
pullback-unit linearity, and section-restriction linearity.

## Proved and sorry left
Closed `AlgebraicGeometry.Scheme.Modules.coefficientTarget_generator_scalar`: one original hole.
No sorry remains in the delivered module, and no new holes are added. The private helper
`coefficientTarget_generator_scalar_ring` is proved entirely from Mathlib ring-map identities.
The imported support isomorphism and scalar formula are already proved declarations.

## No longer needed
None. The original import is required by the unchanged statement and the proof.
The attempted auxiliary ring-identity module and its new node were removed after its proof
was completed; neither is part of the delivery.

## Where the brief, the DAG or earlier work was wrong
No discrepancy found. The existing natural-language proof plan is implemented directly.
The purely structural calculation requires no affineness, flatness, or cartesian-square
hypothesis beyond the displayed equality of composites, including for empty opens and zero rings.

## Second reading by G4

1. Compared the delivered module with the repository version. The theorem signature, visibility,
   definition bodies, and public import are unchanged; only the proof was filled in and a private
   proof helper was added.
2. Compiled the delivered module with `lcompile.py` (the compile was queued behind the shared
   compiler slot); the source contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`,
   `implemented_by`, or hollow definition. The helper and theorem are ordinary proofs.
3. The helper is private and introduces no split-off statement or node. The theorem statement is
   unchanged and the proof uses the existing coefficient comparison declarations; no duplicate
   library theorem was added.
4. The route follows the existing unit plan: support-isomorphism injectivity, linearity of the
   pullback unit, restriction-map linearity, and the commuting square. The only import remains
   necessary for the stated declarations, so no pruning is available.
5. The DAG node statement and proof dependencies remain consistent with the theorem and its
   imported coefficient comparison infrastructure; the unit realization is untouched.

Changed after reading: added this review record only. No Lean source, DAG statement, or import was
changed.
