## What changed

Proved `Int.prime_localizations_dvr` with the unchanged statement in
`Sheaf.RingTheory.IntegerPrimeLocalizations`. Added proof-only Mathlib imports for
Dedekind localizations, integer prime classification and PID dimension. Updated the node proof and proof dependencies to this route.

## Proved and sorry left

Proved `Int.prime_localizations_dvr` (lem-weil-pbc-z-localizations-dvr), all six clauses.
No sorry remains and no new sorry is introduced. Local compilation passed.

## No longer needed

Removed proof imports `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso` and
`WeilConjectures.AlgebraicGeometry.Regular`. The second reading also removed the
redundant new proof import `Mathlib.Algebra.Ring.Int.Field`; `Int.not_isField` is
already available through the retained imports.
This proof no longer needs the planned proof dependencies:
- lem-weil-pbc-localization-prime-residue-field-iso
- def-weil-pbc-localization-at-prime
- def-weil-pbc-normal-ring
- lem-weil-pbc-localization-normal-domain
- lem-weil-pbc-localization-noetherian
- lem-sc-normal-dim1-dvr

Their project declarations and modules are not needed by this proof; the localization
and DVR notions in the unchanged signature are supplied by Mathlib. No unit realization
is bypassed: this node is not among the unit's realized statement or steps.
Other targets may still need the listed nodes; this reports pruning of this proof only.

## Where the brief, the DAG or earlier work was wrong

The earlier Mathlib search incorrectly reported that no integer Dedekind instance or
nonzero-prime localization DVR theorem existed. Mathlib provides
`IsPrincipalIdealRing.isDedekindDomain`,
`IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`, and
`Ideal.isPrime_int_iff`; these close the full theorem without project sorry dependencies.


## Second reading by E1

1. Compared the complete delivered module with the repository version. The existing
   theorem signature is byte-for-byte identical; definitions and public imports are
   unchanged. The only Lean changes are its proof and private proof imports. Pass.
2. Independently compiled the module without warnings. Compiled a scratch copy with
   `#print axioms Int.prime_localizations_dvr`: exactly `propext`, `Classical.choice`,
   and `Quot.sound`. No sorry, axiom, unsafe declaration, opaque declaration,
   implemented_by or extern occurs in the delivery. All six clauses are proved. Pass.
3. No statement is split off and no new declaration or node is introduced. Checked the
   arithmetic cases: zero is treated separately by the fraction-ring equivalence;
   nonzero prime ideals have a positive rational-prime generator; units and composite
   generators are excluded by `Ideal.isPrime_int_iff`. No restatement reduction. Pass.
4. Read the Mathlib PID-dimension, integer-prime classification and Dedekind-localization
   APIs and searched the project for alternative existing arithmetic/DVR declarations.
   The direct Mathlib route is short and has no project sorry dependencies. Checked
   `dag/units/sk-thm-p1.json`: neither this node nor any pruned dependency realizes a
   statement or proof step of the unit. All six old proof dependencies are listed under
   No longer needed. Tested removal of each new proof import: the three retained imports
   are needed; `Mathlib.Algebra.Ring.Int.Field` was redundant and has been removed. Pass.
5. Compared the old and delivered node JSON. Only `proof`, `proof_deps` and `proof_origin`
   change. The three proof steps accurately describe the six Lean clauses, and empty
   project `proof_deps` matches the direct Mathlib proof. The statement, source, unit,
   Lean signature record and other fields are unchanged. Pass.

Second reading changed only the redundant proof import and this report; the proof and
node update were correct as written. The original docstring remains unchanged; its
historical project-dependency route is superseded by the delivered node proof and report.
