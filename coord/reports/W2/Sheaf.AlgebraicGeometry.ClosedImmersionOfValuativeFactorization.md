## What changed

Replaced the proof of
`AlgebraicGeometry.isClosed_range_and_isClosedImmersion_of_valuativeFactorization`
in `Sheaf.AlgebraicGeometry.ClosedImmersionOfValuativeFactorization`.
For each closure point, the existing valuation-probe theorem supplies a square centred
there. Apply the assumed factorization to its bottom map and evaluate the factorization
at the closed point. This gives a preimage under `j`. Thus the closure is contained in
the range; `isClosed_of_closure_subset` proves closedness, and
`IsClosedImmersion.of_isPreimmersion` gives the closed immersion.

The signature, visibility, docstrings and imports are unchanged. The proof follows
all three steps of `lem-sc-picard-locus-closed-valuation-criterion`, so its node requires
no update. No unit route is bypassed.

Searches through msearch.py: Lean Finder for the valuative closed-immersion statement,
Loogle for `AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion`, and grep for
`of_isPreimmersion|exists_valuativeCommSq_of_mem_closure_range`.
The standard Mathlib closed-range criterion was found and used. The existing probe
statement is the exact dependency needed; no new theorem is necessary.

## Proved and sorry left

Closed 1 of 1 local holes:
`AlgebraicGeometry.isClosed_range_and_isClosedImmersion_of_valuativeFactorization`
(node `lem-sc-picard-locus-closed-valuation-criterion`).
No local holes remain and no holes were added or split off.
The proof uses the pre-existing, still unproved declaration
`AlgebraicGeometry.exists_valuativeCommSq_of_mem_closure_range`
(node `lem-sc-picard-valuation-probe-closure`) from its unchanged dependency module.
This is a complete proof from an existing stated dependency, not a sorry-free
transitive proof of the geometric result.

The item compiled cleanly through lcompile.py (exit code 0, 2.0 seconds).

## No longer needed

None. Both existing imports are needed: the public Mathlib import provides the
statement's valuative squares and morphism properties, and the private Sheaf import
provides the valuation probe used in the proof. Both planned proof-dependency nodes
are used, with the closed-image criterion supplied directly by Mathlib.
No nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

None. The existing signatures suffice exactly as planned. The bottom-map
factorization is enough: no compatibility with the generic map is used when
evaluating at the closed point. The argument covers empty sources and arbitrary
closure points without extra hypotheses.

## Second reading by W2

1. Compared the entire delivered module with the repository using `diff -u` and
   checked the prefix through `:= by` byte for byte. Only the former `sorry` is
   replaced. The scheme universe, quasi-compactness and immersion assumptions,
   quantification over all valuative squares, bottom-map factorization assumption,
   and both conclusions are identical. No definitions, visibility, imports or
   public interfaces changed. Verdict: pass.
2. Compiled the delivered file independently through `lcompile.py`: exit 0, no
   warnings (2.1 seconds). Inspected its whole proof: no `sorry`, forbidden
   declarations or data definitions. A scratch copy with `#print axioms` compiled
   and reported exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The latter comes from the existing imported valuation-probe theorem, explicitly
   listed above; the delivery does not claim a transitively closed result.
   The existential witnesses are eliminated inside a theorem proving a proposition;
   no definition chooses arbitrary data from an unproved existence theorem.
   Verdict: pass.
3. No statements were split off, no new modules or nodes were introduced, and no
   new holes were added. Read the full signature of the existing probe theorem:
   its hypotheses are exactly available here, and its centre equality is exactly
   what the rewrite needs. The proof also covers empty source and target: closure
   of an empty range is empty, so no probe is requested without a closure point.
   Verdict: pass; no split-off statement to repair.
4. Read the proof from its conclusion back to its hypotheses, the imported probe
   module, and Mathlib's `IsClosedImmersion.of_isPreimmersion` implementation.
   Searched locally for alternative valuative closedness results and independently
   queried Loogle for `IsClosedImmersion, ValuativeCommSq` (zero hits). Mathlib's
   universal-closedness criterion requests a compatible lift, whereas the stated
   hypothesis here only supplies bottom-map factorization; the existing direct
   pointwise argument is already short and preserves the planned probe route.
   Both imports are needed: the public Mathlib import supplies signature types;
   the private Sheaf import supplies the probe. Read `sk-prop-av-cube.json`, whose
   `realized` arrays are empty; this delivery changes none of the unit's statement
   or steps. Both old proof dependencies are used, so `No longer needed: None`
   is complete. Verdict: pass.
5. Read the item's node and both dependency nodes. Step 1 is the application of
   `exists_valuativeCommSq_of_mem_closure_range`; step 2 applies `h`, evaluates
   `l ≫ j = sq.i₂` at the closed point using `Scheme.Hom.comp_apply`, and rewrites
   with the centre equation; step 3 applies the Mathlib closed-image criterion,
   which is precisely the second dependency node's recorded Mathlib match.
   Thus the existing `proof`, `proof_deps`, and document-based `proof_origin`
   already describe the delivered proof accurately. No node update is required.
   Verdict: pass.

Second reading changed only this report, recording independent verification and
its inherited-axiom limitation. The Lean proof needed no repair. Holes closed: the
one declaration named above. Holes added: none. Split off: none. Pruned: none.
