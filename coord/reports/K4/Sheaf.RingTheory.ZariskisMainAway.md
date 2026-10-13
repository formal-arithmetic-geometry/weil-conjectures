## What changed

Checked the existing repair of `Sheaf.RingTheory.ZariskisMainAway` against its source,
its callers, and Mathlib. The module already proves
`Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime`; its result is only
`Algebra.QuasiFiniteAt R q.asIdeal`, not a duplicate of Zariski's main conclusion.
Added the standard copyright header, moved the module docstring before the public
section, and supplied source, blueprint-step and complete proof documentation.
Made the unfolding of `IsQuasiFiniteAtPrime` explicit with a `change` at `hq`.
No signature, visibility, definition or import changes. No forced adaptations.

Mathlib's `QuasiFiniteAt.of_isOpen_singleton_fiber` (ZariskisMainTheorem.lean:742)
needs precisely the open singleton obtained by transporting `hq` through
`PrimeSpectrum.preimageHomeomorphFiber` (ResidueField/Fiber.lean:212).
The rewritten image is the singleton of the same canonical point, so the
conversion does not assume any additional property of the rings or their primes.
Compiled both the original and the documented proof with `lcompile.py` cleanly.

Searches actually run with `msearch.py`: leanfinder for quasi-finiteness from an
isolated fibre point (eight related results); loogle for
`Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber` (the exact criterion); grep for
`of_isOpen_singleton_fiber|preimageHomeomorphFiber` (eleven hits, source read).
Also searched both library roots for the conversion and the criterion.

## Proved and sorry left

The sole theorem `Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime` is proved,
and was already proved in the starting checkout. The initial module has zero
`sorry`s. Holes closed by this delivery: none. Holes added: none. Holes left: none.
This is verification and documentation of an already landed repair, not proof
progress or a decomposition. The dry-run axiom probe checks the delivered theorem.

## No longer needed

None newly pruned: all three existing imports remain necessary for the public
types or the proof. No new module or node is introduced. The localization
conclusion remains attached to Mathlib's `Algebra.ZariskisMainProperty.of_finiteType`
in `lem-weil-pbc-integral-closure-zariski-main-away`; this delivery does not recreate
that removed wrapper or reopen the old fifteen-step localization proof.
The existing DAG proof already records exactly this conversion as step 1 and
Mathlib's Zariski-main theorem as step 2, so no route update is needed.
The realized statement and proof steps of unit `sk-thm-p1` are preserved.

## Where the brief, the DAG or earlier work was wrong

The dispatched brief says this module still contains `sorry`, but the supplied
checkout has no `sorry` and its theorem compiles. No node currently has this
module as its `lean.module`: the original localization node now correctly points
to Mathlib. Its proof text records this module as the hypothesis conversion.
`coord/repairs.txt` still lists upstream review #1428, although
`coord/changes/zariskisMainProperty-wrapper-removal.md` records the K2 repair as
landed at `20261013T215607-L-899022`. That repair is already present in the module
and its callers. The dispatcher should retire the stale repair assignment rather
than count this verification as closing a hole. The request for a long proving
session has no remaining proof obligation in this version of the assigned module.

## Second reading by K4

1. **Statements and interfaces.** Compared the delivered module with the repository
   version. The theorem signature, visibility, imports, and all existing declarations
   are unchanged; the added `change` only makes the existing hypothesis unfolding
   explicit. Verdict: unchanged statement.
2. **Proof correctness.** Compiled the delivered file with `lcompile.py`; the proof
   transports the open singleton through the fibre homeomorphism and applies
   `QuasiFiniteAt.of_isOpen_singleton_fiber`. No `sorry`, forbidden declarations, or
   hollow definitions occur. Verdict: proof is valid.
3. **New statements.** No statements, split-off theorems, or DAG nodes were added.
   The existing theorem is exactly the needed hypothesis conversion and is strictly
   weaker than the removed duplicate localization wrapper. Verdict: no new statement
   review required.
4. **Pruning and dependencies.** Checked the three imports and the theorem's callers;
   each import is needed by a public type or the proof. The existing DAG proof route
   and `sk-thm-p1` realized steps remain intact, with no stale dependency introduced.
   Verdict: imports and route are minimal and preserved.
5. **Axioms and delivery checks.** The theorem's dry-run axiom probe is limited to the
   permitted axioms, and the delivery preflight is the final check. Verdict: ready to
   deliver.

Changed only documentation and the explicit hypothesis unfolding in the sandbox.
