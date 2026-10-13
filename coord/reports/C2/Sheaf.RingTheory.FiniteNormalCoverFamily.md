## What changed

Replaced the entire proof of `exists_finite_normal_cover_family` in
`Sheaf.RingTheory.FiniteNormalCoverFamily`, keeping its signature and all existing imports.
The proved private helper `normal_away_intermediate` constructs the localization of A
inside K, shows C lies in it by integral closedness, and verifies the same ring is a
localization of C. It needs no finiteness hypothesis.

The main proof follows all three existing DAG steps: the maximal-local criterion makes
A_f normal; each finite C is Noetherian and has a normal principal open; normal-locus
openness and the integral closed-map theorem make Z_C closed. A maximal ideal above each
prime witnesses an open covering member, because Z_C is specialization-closed. Compactness
extracts finitely many indexing subalgebras, and their image finset has exactly the required
properties. The existing proof dependencies and node plan remain applicable unchanged.

Read the full module, its node and three proof dependencies, the unit's realized route,
and the relevant Mathlib signatures. The local Stacks source is not installed on this
machine; checked the official source pages instead:
[Tag 0333](https://stacks.math.columbia.edu/tag/0333) and
[Tag 0332](https://stacks.math.columbia.edu/tag/0332).
Ran LeanFinder, Loogle and grep through msearch.py; found the Mathlib local-normality,
closed-map and compactness ingredients, but no exact finite-family theorem.

## Proved and sorry left

Closed 1 hole: `exists_finite_normal_cover_family`
(node `lem-weil-pbc-finite-normal-cover-family`).
Added 0 holes. No sorry remains in the delivered module. The private helper
`normal_away_intermediate` is fully proved.

This is a proof from the existing `AlgebraicGeometry.normal_locus_isOpen` declaration,
not a new decomposition. Its existing upstream proof dependencies remain; this delivery
does not claim to close their holes. Compilation uses lcompile.py and the delivery dry run.

## No longer needed

None. No original import was removed and no planned dependency was bypassed.
The three existing nodes remain needed: `lem-weil-pbc-normal-domain-of-local-normal`
(Mathlib `IsIntegrallyClosed.of_localization_maximal`),
`lem-weil-pbc-finite-algebra-noetherian` (Mathlib `IsNoetherianRing.of_finite`), and
`lem-weil-pbc-normal-locus-open` (`Sheaf.Paper.NormalLocusOpen`).
No new dependency module or node was introduced.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface fault found. Step 1 can be implemented without explicitly
proving integrality of C_f: each element of C is integral over the realized A_f subalgebra
of K and thus already belongs to it. Verifying its localization universal property over C
then proves the same normality assertion. This implements the existing route.
The unit's statement and realized steps are preserved, and no targets or definitions changed.

## Second reading by C2

1. Interface: PASS. Compared the complete delivered module with the repository using
   `diff -u`. The existing theorem's signature, docstring, visibility and imports are
   byte for byte unchanged. The only additions are its proof and the proved private
   helper. There are no delivered definitions, new public statements, other modules,
   node changes or change records.
2. Proof: PASS. Independently compiled the module with lcompile.py, with no errors or
   warnings. No `sorry` or forbidden declaration occurs in the delivered source. A
   scratch copy's `#print axioms` shows only propext, Classical.choice and Quot.sound
   for `normal_away_intermediate`. The main theorem additionally uses sorryAx through
   the existing normal-locus theorem and its open dependencies; it closes this module's
   one hole, not those upstream holes. The localized subalgebra T is explicitly
   constructed. Integral closedness supplies elements uniquely determined by their
   images in K; no arbitrary data is selected from an unproved existence theorem.
3. Split statements: PASS, none were added. Checked the helper for C equal to the base,
   f a unit, and arbitrary integral intermediate C without a finiteness assumption:
   integral closedness of A_f forces C into A_f, and the localization universal
   property then identifies C_f with A_f. A=0 and f=0 are excluded by the original
   hypotheses. Repeated LeanFinder, Loogle and grep searches with different wording;
   read related principal-localization helpers in IsN1AdjoinSingleton and the
   integral-image argument in NormalFiniteTypeSubalgebraExtension. Neither gives a
   shorter existing theorem applicable to this item. No restatement hole is present.
4. Route and pruning: PASS. Checked the inclusion C <= T, the localization equivalence,
   finiteness-to-Noetherian step, closed image of the nonnormal locus, specialization
   direction from p to a maximal m, and finite-subcover extraction. Proof-only imports
   are plain imports; the public imports provide the statement's integral closure and
   localization vocabulary. Every old proof dependency is used, so the list under
   No longer needed is complete. Read sk-thm-p1's realized statement and four steps;
   this implementation changes none of that route.
5. DAG: PASS. Read lem-weil-pbc-finite-normal-cover-family and its three proof dependency
   nodes. Its three proof steps and proof_deps match the actual proof, with the first
   two leaves realized by their recorded Mathlib matches and normal-locus openness by
   its recorded Sheaf declaration. The existing source proof_origin remains accurate.
   No new split statement needs a node.

Changes by this second reader: appended this independent review and its validation
results to report.md. No Lean repair was needed; the proof was retained unchanged.
