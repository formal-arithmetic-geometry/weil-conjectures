## What changed

Proved `IsLocalRing.bijective_away_lift_fractionRing_of_ringKrullDim_eq_one` in
`Sheaf.RingTheory.LocalDomainDimOnePrincipalLocalization`, with its signature and existing
visibility unchanged. Added the proof-only import `Mathlib.RingTheory.KrullDimension.LocalRing`.
Updated the node's proof, proof dependencies and proof origin to the shorter route.

Mathlib's `ringKrullDim_eq_one_iff_of_isLocalRing_isDomain` gives that each nonzero `b` divides
some power of `f`. `IsLocalization.of_le_of_exists_dvd` then identifies the existing away
localization as a fraction ring; `IsLocalization.bijective` and `Away.lift_comp` finish.
The instance supplies only proofs of localization properties for the explicitly constructed
ring: no object is chosen from an existence theorem. All original public imports are retained
because they provide the signature's notions. No interface change or forced adaptation.

## Proved and sorry left

Closed the only hole:
`IsLocalRing.bijective_away_lift_fractionRing_of_ringKrullDim_eq_one`
(node `lem-sc-local-domain-dim-one-principal-localization-fraction-field`).
No sorries remain and no holes were added. This is a proof, not a decomposition.
The single-file compile succeeds without warnings. The required delivery dry run also checks
all introduced constants for forbidden axioms.

## No longer needed

Removed `lem-weil-pbc-primes-of-localization` from this node's proof dependencies. Its general
prime correspondence (`Mathlib.RingTheory.Localization.Ideal` and
`Mathlib.RingTheory.Localization.AtPrime.Basic`) is not used by this proof. Neither module was
an explicit import in the original item, so no import line was removed. This is pruning of
this node's route, not a claim that these Mathlib modules disappear from the global closure.
No other nodes or modules are pruned. The unit `sk-thm-curveestimate` has no realized proof
steps involving this tool node; its own statement and route remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The original prime-correspondence proof is valid but unnecessarily long for Lean: Mathlib's
radical characterization and localization comparison give a complete shorter argument.
No erroneous statement, unusable interface or tool failure was encountered. No new nodes.

## Second reading by X2

1. PASS: compared the complete delivered Lean file with the repository using `diff -u`.
   The existing theorem signature, visibility, module header, docstrings and public imports
   are byte-for-byte unchanged. Only its proof and one plain proof-only import were added.
   There are no other delivered modules, definitions, interface changes or change records.
2. PASS: independently compiled the delivered file through `lcompile.py`, without errors
   or warnings. A scratch copy with `#print axioms` reports exactly `propext`,
   `Classical.choice` and `Quot.sound` for
   `IsLocalRing.bijective_away_lift_fractionRing_of_ringKrullDim_eq_one`.
   The delivered module contains no remaining `sorry` or forbidden declarations.
   The local fraction-ring instance proves a property of the existing concrete localization;
   it chooses no ring or other data from an unproved existence theorem.
3. PASS: no statements, nodes or holes were split off. Checked the used Mathlib theorems
   directly: the dimension-one radical characterization needs neither Noetherianity nor
   a discrete valuation hypothesis. For a unit denominator the power can be zero; zero
   denominators are excluded by non-zero-divisor membership. The assumptions exclude both
   the zero ring and the field case, and `f = 0` is explicitly excluded.
4. PASS: read the proof from the target downward, inspected the localization comparison
   and uniqueness lemmas, and independently searched LeanFinder with a divisibility-based
   query and searched both source roots with `rg`. No shorter general result was found;
   the search hits require stronger DVR or factorization assumptions. The added LocalRing
   import is plain and is used by the proof; the original public imports supply the public
   interface. The report lists the sole removed old proof dependency,
   `lem-weil-pbc-primes-of-localization`. The unit `sk-thm-curveestimate` realizes only
   `thm-sc-proper-cohomology`, with no realized steps; this auxiliary-node reduction does
   not bypass or alter its route.
5. PASS: compared the complete node JSON with the repository. Only `proof`, `proof_deps`
   and `proof_origin` differ; the two recorded steps match the radical/divisibility proof
   and localization uniqueness proof. Their `uses` union equals `proof_deps`. The node's
   statement and Lean record are unchanged, and no new nodes require validation.

Second reading changed only this report by adding the independent review and verification
results. The Lean proof and node changes were correct and were retained without rewriting.
