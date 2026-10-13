## What changed

Proved `KaehlerDifferential.exists_finite_subring_nonzero_differential` without changing
its signature, visibility, or any definition used by a target. Added only proof imports
for the coefficient family, intersection theorem, perfect-field differential criterion,
and characteristic transfer.

Added the proved module `Sheaf.RingTheory.PowerSeriesFiniteSubfieldFamily`. Its public
theorem `RingTheory.exists_powerSeries_finite_subfield_family` constructs the subrings
needed by the existing `RingTheory.powerSeriesRingSubfields`, proves the exact quotient
condition for their fraction subfields, and transports finiteness through the given
ring isomorphism. The private `coefficientSubring` is real data with proved closure
under ring operations, using the two coefficient convolution formulas. No data is
chosen from an unproved existence theorem in a definition.

The main proof uses the finite-extension intersection clause and then the differential
kernel clause, proves downward directedness of the composita, and constructs the
compatible A-to-T algebra tower. Applying `KaehlerDifferential.map_D` proves that a
nonzero differential over T remains nonzero over A. Updated the item's proof route
and dependencies to match the Lean proof. The unit's route is unchanged.

Both delivered modules compile cleanly using `lcompile.py --all` (about four seconds
each). Checked the empty-variable cases n=0 and m=0: coefficient convolutions and the
p-basis family require no nonempty variable set. For a perfect coefficient field and
no variables the family can be the singleton C,K, and in a finite extension M the
non-pth-power hypothesis is impossible. No characteristic-zero case is admitted.

## Proved and sorry left

Closed the original one of one holes:
`KaehlerDifferential.exists_finite_subring_nonzero_differential`
(node `lem-weil-pbc-power-series-polynomial-nonzero-differential`).

Also proved `RingTheory.exists_powerSeries_finite_subfield_family`
(node `lem-weil-pbc-power-series-finite-subfield-family`) and the private coefficient
subring construction. Zero holes split off; zero holes added; zero sorries remain
in either delivered module. The proofs use the existing planned library lemmas;
their inherited proof obligations are unchanged. This is one hole closed, not a
one-for-one decomposition.

## No longer needed

None of the original imports or planned mathematical dependencies is pruned.
The p-basis and power-series-subfields nodes are used by the new construction lemma;
the intersection and differential-zero nodes are used by the main theorem. All five
original proof dependencies remain reachable. Removed the exploratory, unnecessary
proof import `Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors` from the new module
before delivery; it is already an internal dependency of the existing subfields proof.
No existing library module becomes unreachable.

## Where the brief, the DAG or earlier work was wrong

The planned `powerSeriesRingSubfields` declaration assumes explicit coefficient
subring and quotient-subfield families rather than supplying them. Its caller must
construct those families and prove their exact defining conditions. This missing
glue is now proved in the new module, rather than left as another hole.

The local literature checkout contains only its tracked lists. Read the source at
https://stacks.math.columbia.edu/tag/07P5 and the surrounding argument at Tags 07P4
and 07PH. WANTED: local `literature/stacks-project/more-algebra.tex`, Tags 07P5,
07P4 and 07PH, for these two nodes. The detailed Lean construction is marked as
agent-written in `proof_origin` and follows the cited Stacks construction.

LeanSearch returned HTTP 500 and is recorded as unavailable. LeanFinder, Loogle,
and source grep ran and are recorded honestly. Blueprint searches for subfields
and power series found no equivalent construction node. The ancestor script returns
None for this module-valued `created.item`; the new node preserves the item's existing
nearest blueprint ancestor and prepends its node id to the existing via chain.

## New nodes

`lem-weil-pbc-power-series-finite-subfield-family`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-power-series-finite-subfield-family.json`,
records the proved `RingTheory.exists_powerSeries_finite_subfield_family` in
`lean/Sheaf/RingTheory/PowerSeriesFiniteSubfieldFamily.lean`. It is strictly step 1 of
the original argument: it has no finite extension M, element z, or differential
conclusion. Its proof uses the existing p-basis and subfields declarations, with real
coefficient and quotient constructions. No statement/interface change record or
forced adaptation is needed.

## Second reading by D3

1. PASS: compared the existing module with the repository using diff. The only
   differences are four plain proof imports and replacement of the theorem's
   proof. The existing signature, visibility, docstring and all definitions are
   byte-for-byte unchanged. The other delivered module is new; there are no
   statement changes or forced adaptations.
2. PASS: both modules compile without errors or warnings using lcompile.py --all.
   Searched their sources for sorry, axiom, unsafe, opaque, implemented_by and
   extern: none occur. Scratch copies with #print axioms show propext,
   Classical.choice, Quot.sound and inherited sorryAx for the two public theorems;
   the private coefficientSubring uses only the three permitted axioms. Thus the
   original hole is closed relative to the existing library dependencies; this
   does not claim that the entire dependency closure is already axiom-clean.
   The subring data is constructed explicitly, and no arbitrary data is selected
   from an unproved existence theorem in a definition.
3. PASS: no statements are split off with sorry. Read the new family theorem
   and its node in full: it proves only the coefficient-family construction,
   contains no M, z or differential conclusion, and is strictly below the item.
   Checked zero-variable cases, the perfect-field/no-variable case, and the
   zero-denominator branch (zero is represented as 0/1). Products satisfy the
   support condition because a nonzero convolution has a nonzero summand; both
   factors then have divisible exponents. Repeated LeanFinder with the distinct
   query "p-power supported coefficients subring fraction field intersection
   Frobenius image finite module", plus rg searches of Mathlib, upstream and
   lean/Sheaf. No duplicate family theorem or shorter complete proof was found.
   Mathlib toSubring handles coefficient restriction only, not the simultaneous
   exponent support and polynomial-family construction needed here.
4. PASS: read the proof from its conclusion through map_D, differential-kernel
   detection, finite-extension intersection and the coefficient construction.
   The A-to-T-to-M tower uses exactly the composite required in the unchanged
   statement. Every added import is a plain proof import in the existing module;
   the new module's public imports supply its signature and instances. All five
   old proof dependencies remain used, two through the new family lemma; none
   is abandoned. The No longer needed section is complete. Read sk-thm-p1.json
   including realized: this construction stays below its steps and changes
   neither the unit route nor any realized node.
5. PASS: compared the existing node with the repository: only proof, proof_deps
   and proof_origin changed. Their steps match the Lean construction, intersection
   applications and differential map. Both proof_deps lists are exactly the
   unions of their steps' uses. The new node has its source, full proof, searches,
   provenance, chapter/unit and verbatim Lean signature.

Changes by the second reader: appended this review and recorded the independent
duplicate search; no Lean or DAG repair was needed. Temporary axiom-check copies
were removed before delivery.
