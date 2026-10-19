1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-minimal-primes-dense-spectrum.json`: statement split, no new nodes, Mathlib ingredient searches recorded.
- `citations.json`: verbatim statement excerpts for both cited nodes.

2. Attachments:

None.

3. WANTED:

None.

4. What was wrong or incomplete:

The imported item was unsplit and had no proof. I kept its statement and dependencies unchanged. The source's density sentence is abbreviated, so I expanded the standard argument: a nonempty open contains a basic open `D(f)`, and a prime in that basic open contains a minimal prime that still avoids `f`. Searches found Mathlib ingredients (`PrimeSpectrum.isTopologicalBasis_basic_opens` and `Ideal.exists_minimalPrimes_le`) but no single declaration of the exact statement, so no Mathlib leaf or new node was appropriate. A DAG search found the existing minimal-prime and basic-open leaves; I cited those rather than duplicating them.

5. What I could not finish, and why:

Nothing remains for this stage-1 split.

## Review by Q84

I read the item, the unit `sk-i-curve-zero`, the chapter `sec-trace-formula`, and the source passage at `literature/stacks-project/algebra.tex`, Tag 00RG. The item’s hypotheses and conclusion are unchanged. The sole proof step uses `lem-weil-pbc-spec-localization-away-basic-open` exactly for its basis assertion and `lem-weil-pbc-prime-contains-minimal-prime` exactly for the existence of a minimal prime below the chosen prime; both statements were opened and the quoted sentences in `citations.json` were copied verbatim. The containment check is explicit: if `f` avoids the larger prime, it avoids every smaller prime, so the resulting minimal-prime point remains in `D(f)`. I checked the edge cases of a field (`Spec A` has the zero minimal prime), the zero ring (no nonempty open exists), and a nonreduced example such as `k[ε]/(ε²)` (the unique minimal prime is still in every nonempty principal open). The blueprint ancestry and `from.place` identify the field-fibre density sentence used by the parent route. No new node, duplicate, source error, or unrecorded non-elementary fact was introduced.
