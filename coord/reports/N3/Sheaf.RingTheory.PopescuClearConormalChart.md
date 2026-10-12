## What changed

Proved `Algebra.exists_popescu_cleared_conormal_chart` with its signature unchanged.
Added the proved general ring lemma `Ideal.exists_conormal_span_clearing` in
`Sheaf.RingTheory.ConormalSpanClearing`. It assumes only conormal spanning and
proves exact finite-ideal relations and a positive-power quotient identity.
The original module lifts these equations through polynomial reduction, proves
principal-kernel divisibility, and transports smoothness, the prescribed conormal
basis, and the differential basis. All helper definitions are local constructions;
no arbitrary existence theorem supplies data to a public definition.

The generalized clearing proof lifts selected conormal combinations, clears their
localization equalities, uses Mathlib's quotient form of Nakayama, and clears a
common positive exponent. The two ring/module localization helpers and the chart
transport helper are private and fully proved. Updated the original node's proof
route. Compiled both modules together through lcompile.py with no warnings.

## Proved and sorry left

Closed the one original hole: `Algebra.exists_popescu_cleared_conormal_chart`.
Added and fully proved `Ideal.exists_conormal_span_clearing`
(node `lem-weil-pbc-conormal-span-clearing`). No holes added and no `sorry` remains
in either delivered module. This is a proof, not a decomposition.

## No longer needed

Removed the redundant proof import `Mathlib.RingTheory.Localization.Module` from
`PopescuClearConormalChart` (available through `Mathlib.RingTheory.Etale.Kaehler`)
and `Mathlib.RingTheory.Nakayama` from `ConormalSpanClearing` (publicly imported by
`Mathlib.RingTheory.Ideal.Cotangent`). Existing public statement imports stay.
The old direct proof dependency `lem-weil-pbc-nakayama-one-plus-ideal-annihilator`
is now used transitively through `lem-weil-pbc-conormal-span-clearing`; it is not
pruned. The other two old proof dependencies remain direct dependencies. No Sheaf or WeilConjectures module is
claimed globally unreachable. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The DAG classified most denominator clearing
and chart transport as elementary; they required substantial explicit Lean glue.
The Stacks local source file is absent on this machine, so the source was read at
https://stacks.math.columbia.edu/tag/07CP. The parent node's corrected numerator
x^N+b is essential: the annihilator is 1+b/x^N. This delivery preserves that
correction and avoids forming a second localization by directly clearing ideal
membership after Nakayama. LeanSearch returned Internal Server Error; recorded
as unavailable, not as a negative search result.

Edge cases: K=1+sup(k_l) is positive even when m=0; sums and coefficient extension
work for E empty; no nontriviality or domain instance is used, so the zero ring,
x=0, and pi zero or invertible are all covered by the compiled proof.

## New nodes

`lem-weil-pbc-conormal-span-clearing` records the strictly more general ring-level
finite-ideal argument used by the original theorem. It is fully proved, has no
smoothness or differential-basis hypothesis, and introduces no remaining work.
Blueprint searches for conormal and 07CP found no duplicate chart-clearing unit
statement. No change record or forced adaptation is needed.


## Second reading by N3

1. **Interfaces: pass.** Read the complete diff against the repository module and
   compared the theorem signature byte for byte, including the three antecedents,
   the positive exponent, the prescribed basis equalities and every polynomial
   identity. The signature is identical. There are no existing definitions to
   alter, no change record, and no forced adaptation. The new helper module exposes
   only the general clearing theorem; all chart transport helpers are private.
2. **Proof and axioms: pass.** Compiled both delivered modules in import order with
   `lcompile.py`; no errors or warnings. A scratch module importing the sandbox
   artifacts reports exactly `propext`, `Classical.choice`, `Quot.sound` for both
   `Ideal.exists_conormal_span_clearing` and
   `Algebra.exists_popescu_cleared_conormal_chart`. Read every proof: the lift of
   conormal combinations lies in the selected ideal, both localization equality
   denominators are cleared, Nakayama applies to the finitely generated mapped
   ideal, and the final principal-kernel divisibility gives the required sign and
   coefficient order. No sorry, forbidden declaration, hollow definition, or data
   chosen from an unproved existence theorem occurs. Polynomial and coefficient
   witnesses are chosen only inside the proved existential theorem.
3. **New statement: pass.** No unfinished statement is split off. The one new,
   fully proved lemma isolates only the finite-ideal argument; smoothness and the
   two basis transports remain in the original module. Read its docstring and
   matching node. Independently searched with Loogle `Ideal.Cotangent,
   Submodule.span`, grep `Cotangent.*span|span.*Cotangent|exists.*span.*clearing|
   exists.*cotangent.*generat`, and LeanFinder for selected generators and a
   multiplier congruent to a power modulo the ideal. Also searched the repository
   and upstream ring-theory sources. The local-ring cotangent spanning criterion
   assumes a maximal ideal and Noetherian local ring; the presentation-basis
   construction changes the presentation; neither proves these exact identities.
   `LocalizedConormalBasisJacobian` stops at membership modulo the square for a
   different presentation interface. No duplicate was found. Small cases checked:
   m=0 gives K=1 from the empty supremum; E empty gives zero selected sums; x=0
   permits a=0 and a positive exponent; I=0 and E containing all generators admit
   a=x and diagonal coefficients. The proof never assumes nontriviality, so the
   zero ring is included. Reduction also covers pi=0 and invertible pi.
4. **Route and pruning: pass after repairs.** Read
   [Stacks 07CP](https://stacks.math.columbia.edu/tag/07CP), the passage from (2)
   to (4), and [Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV), (1) and
   (3). The quotient version of Nakayama used by the code is proved from the
   existing one-plus-ideal annihilator result in Mathlib. The numerator x^N+b
   preserves the quotient chart, and directly clearing mapped-ideal membership
   avoids the extra localization described in the old docstring. No shorter
   matching theorem was found. Removed two redundant proof imports and compiled
   again. `## No longer needed` now accounts for the removed direct Nakayama edge
   as a transitive dependency. Read `dag/units/sk-thm-p1.json`, including `realized`:
   this below-unit clearing argument changes none of its statement or step nodes.
5. **DAG: pass.** Compared the old and delivered item JSON: only `proof`,
   `proof_deps` and `proof_origin` change. Its steps now match conormal spanning,
   reduced-ring clearing, lifting through polynomial reduction and chart transport.
   Read the new node's source, self-contained statement, proof steps, union of
   dependencies, searches, provenance, blueprint ancestry, chapter, unit, creation
   record and verbatim Lean statement. The Nakayama dependency remains below the
   new lemma; no old proof dependency becomes globally unnecessary.

Second-reading changes: corrected the original theorem's proof docstring to the
actual direct clearing argument, removed the two redundant proof imports above,
and clarified dependency accounting in this report. No proof body or statement
needed repair. One original hole closed, zero holes added, zero unfinished lemmas
split off, and no Sheaf or WeilConjectures module pruned.
