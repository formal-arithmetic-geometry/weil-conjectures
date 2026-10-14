## What changed

Audited the queued repair of Sheaf.RingTheory.ZariskisMainAway against the current
module, the Zariski-main DAG node, Mathlib's finite-type criterion, and the two
landed change records. The original duplicate localization conclusion has already
been removed. Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime now supplies only
the separate conversion from the project's open singleton in the fibre-ring
spectrum to Mathlib's QuasiFiniteAt instance. Kept that signature and all imports.
Simplified the final two proof lines to a single rwa; compiled the original and
simplified versions separately through lcompile.py, each successfully in 1.7 seconds.

Loogle search through msearch.py confirmed
Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber in
Mathlib.RingTheory.ZariskisMainTheorem. Its finite-type hypothesis is available;
the fibre homeomorphism transports precisely the singleton in the definition of
Algebra.IsQuasiFiniteAtPrime. No localization conclusion is duplicated here.

## Proved and sorry left

Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime is proved, and was already
proved on the supplied baseline. Holes closed: 0. Holes added: 0. Sorries left: none.
This is a verification and proof simplification of a listed repair, not new proof
progress or a decomposition. The module's only theorem realizes step 1 of
lem-weil-pbc-integral-closure-zariski-main-away; its remaining step is the already
proved Mathlib declaration Algebra.ZariskisMainProperty.of_finiteType.

## No longer needed

None newly pruned. All three imports remain needed: QuasiFinite.Basic supplies
the public result type, QuasiFiniteAtPrime supplies the public hypothesis, and
ZariskisMainTheorem supplies the proof-only isolated-fibre-point criterion.
The DAG already records the shorter Mathlib route, so no node changes are needed.
No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The dispatcher brief says this module still contains sorry. The supplied module
contains no sorry, and coord/queue.md reports zero holes for this repair item.
The duplicate warning was already addressed by the landed records
coord/changes/zariskisMainProperty-duplicate.md and
coord/changes/zariskisMainProperty-wrapper-removal.md. The latter explicitly notes
that this repair is not a proof of a formerly open hole. The queue nevertheless
still lists the module in coord/repairs.txt, which allows this repair dry run.

The same upstream review line also mentions Scheme.Hom.IsQuasiFinite and
IsLocallyQuasiFinite. Those declarations are in the separate module
Sheaf.AlgebraicGeometry.QuasiFiniteMorphism. This delivery makes no interface
change that would force adapting that module, and does not claim to resolve that
separate review issue.

## Second reading by V1

1. **Visibility and statements — pass.** I compared the delivered module with
   the repository version. The theorem signature and all existing declarations
   are byte-for-byte unchanged; the only edit is a proof-line simplification.
   No definition, target statement, or public import was changed.
2. **Proof and axioms — pass.** The module compiles cleanly with
   `lcompile.py`. It contains no `sorry`, `axiom`, `unsafe`, `opaque`,
   `extern`, `implemented_by`, or hollow definition. The proof uses the stated
   fibre homeomorphism and Mathlib's `QuasiFiniteAt.of_isOpen_singleton_fiber`;
   the resulting theorem is exactly the conversion claimed by its docstring.
   A scratch-copy `#print axioms` returns only `propext`, `Classical.choice`,
   and `Quot.sound`, with no `sorryAx`.
3. **Statements and split-offs — pass.** No new statement or node was added,
   and no split-off theorem remains. The existing helper is strictly weaker than
   the Zariski-main localization conclusion and is needed by the unit route.
   The DAG node and its proof dependencies agree with the Lean code.
4. **Pruning and route — pass.** The two-step unit route is preserved: this
   helper supplies `QuasiFiniteAt`, then Mathlib's
   `Algebra.ZariskisMainProperty.of_finiteType` supplies the localization
   theorem. All three imports are used; no import or proof dependency can be
   pruned.
5. **Nodes agree with Lean — pass.** I read
   `lem-weil-pbc-integral-closure-zariski-main-away.json`: its first step
   describes this exact singleton-openness conversion and its second step is
   the direct Mathlib theorem. Its `proof`, `proof_deps`, and `proof_origin`
   remain accurate. I also checked `sk-thm-p1.json` and its `realized` route;
   this proof-only simplification changes none of it. No new nodes, forced
   adaptations, or change records are required. The dry run passes as AUTO.

The first reader changed the final proof from two commands (`rw` followed by
`exact`) to the equivalent single `rwa`. I retained that correct change and
added this second-reading record; I made no further Lean change. No theorem,
node, import, or interface was changed.
