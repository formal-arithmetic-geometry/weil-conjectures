## What changed

Replaced the first worker's `Sheaf.RingTheory.CodimOneAux` and
`AdicCompletion.completion_localization_data`, which merely repackaged the entire DVR
conclusion, with `Sheaf.RingTheory.FlatAssociatedPrimeDVR` and
`AdicCompletion.isDiscreteValuationRing_atPrime_of_flat_reduced_quotient`.

The item's proof now establishes completion Noetherianity with
`AdicCompletion.isNoetherianRing`, uses `exists_local_completion_quotient` and
`Ideal.mk_ker` to identify the completed quotient, and transports reducedness from
`hp.2` using `isReduced_of_injective`. Flatness comes from Mathlib's
`AdicCompletion.flat_of_isNoetherian`. It then applies the generic algebraic lemma.
The new hole covers only the argument after these completion-specific steps: it
assumes a flat Noetherian algebra and an already reduced quotient, and needs neither
completion nor a local base nor analytic unramifiedness. The original signature and
all definitions remain unchanged. Added imports are proof-only imports.

Removed duplicate/misnamed sandbox Lean copies so that only the two canonical module
paths are delivered. Removed the linter suppression and the redundant local instances
from the first worker's attempted proof. Updated the original node's proof route and
wrote the new node with its exact signature, complete proof, and real search records.

## Proved and sorry left

Hole closed in the item's module:
`AdicCompletion.isDiscreteValuationRing_atPrime_of_isAnalyticallyUnramified`
(node `lem-weil-pbc-codimension-one-analytically-unramified`).

Hole added and still open:
`AdicCompletion.isDiscreteValuationRing_atPrime_of_flat_reduced_quotient`
(node `lem-weil-pbc-flat-associated-prime-dvr`). It is the sole remaining direct
`by sorry` in the delivery. The invalid preliminary `completion_localization_data`
is not delivered.

This is a decomposition: one upper hole closed, one strictly lower algebraic hole
added, net zero holes closed. The upper theorem is not an axiom-free proof: both
axiom checks include `sorryAx` in addition to `propext`, `Classical.choice`, and
`Quot.sound`. No data construction or definition was added or changed.

## No longer needed

No imports from the repository version were removed, and no modules are pruned.
Both original proof imports are used by the revised reduction.

These old direct proof dependencies move into the new algebraic lemma's proof plan
and are no longer direct dependencies of the item's proof:
`def-weil-pbc-localization-at-prime`,
`lem-weil-pbc-localization-noetherian`,
`def-weil-pbc-flat-ring-map`, `def-weil-pbc-noetherian-ring`,
`lem-weil-pbc-krull-intersection-jacobson`.
They are not claimed to be globally unnecessary. The original completion
Noetherianity, completion flatness, local-completion quotient, and analytic
unramifiedness dependencies are retained. The new algebraic node is added.

## Where the brief, the DAG or earlier work was wrong

The first worker's auxiliary conclusion was exactly the domain/PID/local/nonfield
structure required by the DVR constructor, with the same hypotheses as the item;
it was a restatement rather than a real reduction. Its docstring lacked the
natural-language proof, its node ID disagreed with the filename, its search list
was empty, its Lean signature was an ellipsis, and the item's node had not been
updated. The sandbox also held several copies under noncanonical module paths.
All of these faults were repaired.

The new reduction follows steps 1-2 of the original plan in Lean and leaves only
steps 3-7 in the generic algebraic lemma. The unit `sk-thm-p1` and its `realized`
statement and steps are unchanged. The node is below that unit's fixed route.

The source text is absent from this local literature mirror; the second reader
checked the original primary source at https://stacks.math.columbia.edu/tag/032Z.
The generalization to an arbitrary flat Noetherian algebra is recorded as an
agent-written argument based on that proof, with all details in its docstring.

## New nodes

`lem-weil-pbc-flat-associated-prime-dvr` is the algebraic portion of Tag 032Z after
Noetherianity, flatness and reducedness have been established. It introduces its
own R and A and exact annihilator hypothesis, and has an exact Lean signature and
five proof steps. Searches: LeanSearch returned an internal-server error (recorded
as unavailable, without an absence verdict); Loogle `Module.Flat,
IsDiscreteValuationRing` and the source grep
`IsDiscreteValuationRing.*[Ff]lat|[Ff]lat.*IsDiscreteValuationRing` returned no hits.
Additional semantic search found only generic DVR characterization results.
Repository and upstream searches found no existing matching flat-algebra lemma.
No change record is required: no existing public signature or definition changed.

## Second reading by G2

1. Compared both canonical delivered modules with the repository. The new module
   has no repository counterpart. The item's existing theorem signature is byte
   for byte unchanged, checked by extracting the text through `:= by`; its existing
   docstrings, public imports, universes and section visibility are unchanged.
   No definition, target or hypothesis was altered. Verdict: passes after repair.
2. Compiled the first worker's canonical pair, then compiled both revised modules
   in import order using `lcompile.py --all`. The revised pair compiles cleanly.
   Explicit scratch `#print axioms` for both delivered declarations reports only
   `propext`, `Classical.choice`, `Quot.sound`, and the reported `sorryAx`.
   The only direct hole is the new named algebraic theorem. There are no forbidden
   declarations, no hollow definitions, and no arbitrary unproved data witnesses.
   Verdict: valid decomposition, not a finished axiom-free DVR proof.
3. Checked the new statement against its full docstring argument: properness of q
   rules out z=0; reducedness makes its lift invertible; flatness excludes
   denominators outside p from q; finite generation clears denominators; regularity
   and Krull intersection give the domain and principal ideal properties.
   Small cases checked mathematically: a field base with p=0 fails the DVR
   hypothesis; a zero algebra has no prime q; the identity map of a DVR at its
   maximal ideal gives the original DVR; polynomial algebras over a DVR at the
   extended maximal prime give a DVR with reduced polynomial quotient. The tempting
   counterexamples A=R/(uniformizer) and A=R[epsilon]/(epsilon^2) fail flatness and
   reducedness respectively. Three search kinds are recorded, with the LeanSearch
   outage explicit. Verdict: true and a strict algebraic part of the argument.
4. The revised proof genuinely uses the existing completion-Noetherian theorem and
   local-completion-quotient theorem, plus Mathlib completion flatness. Its analytic
   hypothesis is used to prove reducedness rather than merely passed to a renamed
   version of the whole item. Imports are needed for signatures or those proofs;
   all new imports into the item are plain `import`. The five old direct dependencies
   transferred to the lower argument are listed above. No unit realization is
   bypassed or modified. Verdict: real reduction with zero net holes closed.
5. Read the original node and `dag/units/sk-thm-p1.json`. Updated only the original
   node's permitted proof-route fields; its statement and statement dependencies
   are untouched. The new node has matching ID/filename, exact Lean declaration
   signature, source, full self-contained statement, dependency union, proof origin,
   three actual search kinds, creation fields and the original chapter/unit.
   Verdict: metadata now agrees with the delivered Lean.

Second reading changed the invalid restatement into a completion-specific reduction
to one generic algebraic hole; repaired its documentation and nodes, removed duplicate
files and linter suppression, and compiled and checked axioms as described above.
