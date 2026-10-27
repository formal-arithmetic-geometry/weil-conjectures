## What changed

Proved `Algebra.essentiallySmooth_rationalPoint_completion` with its entire signature
unchanged, including every completion-coordinate, residue, maximal-ideal,
completeness and homogeneous representative clause. All edits are under `Sheaf`;
no adopted source declaration or target was modified.

The proof takes the ring-level Mathlib smooth normal form, centers its variables
using the specified residue-field identifications, and computes the differential
rank from the polynomial differential basis and formally etale base change.
`Ideal.formallyEtale_powerQuotient_associatedGraded` then supplies the actual
power-quotient isomorphisms and graded comparison with S. A coordinatewise inverse
limit construction identifies completions. Three new, fully proved polynomial-model
modules supply the coefficient criterion, combined-ideal completion, and combined-ideal
associated graded calculation. The latter constructs the polynomial evaluation map,
proves injectivity using homogeneous coefficient extraction, and proves surjectivity
by finite monomial sums. None chooses arbitrary data from an unfinished existence proof.

All five delivered Lean modules compile through `lcompile.py`, with no warnings
on their final versions. The new comparisons include zero variables; the coefficient
and graded statements additionally allow arbitrary ideals and the zero ring.
The main theorem's residue comparison is proved using the actual rR, rS and hres,
not a separately chosen field isomorphism. The n=0 quotient is handled explicitly.

The existing generic infinitesimal-neighbourhood theorem is used as a black box;
its own unfinished proofs remain in their existing module. The new route preserves
the unit's realizations (this support node realizes no unit step). The DAG copy
records the actual ring-level route and all three polynomial-model modules.

The returned head `cac493bc5a5` was refused for two duplicate private helper
proofs. This repair removes both copies from both consumers and places the
inverse-limit comparison once in
`Sheaf.RingTheory.CompletionEquivPowerQuotients`, as
`AdicCompletion.equiv_of_powerQuotient_bijective`. Both consumers import and apply
that theorem. Its signature uses Mathlib's canonical quotient map and requires
only the adic-completion public import. Evaluation compatibility is private to
this shared module; the polynomial truncation proof instead uses its existing
completion-kernel criterion and ideal-power inclusion. This is a code repair,
not an unchanged resubmission. The current shared item still has its original
single `sorry`; its public statement and the retained theorem signatures agree.

## Proved and sorry left

Closed the item's one hole:
`Algebra.essentiallySmooth_rationalPoint_completion`
(node `lem-trf-smooth-rational-point-completion`).

Added zero holes. Proved, rather than left split off:

- `MvPolynomial.mem_combined_ideal_pow_iff`
  (`lem-trf-polynomial-combined-ideal-coefficients`).
- `MvPolynomial.combinedIdeal_completion`
  (`lem-trf-polynomial-combined-completion`).
- `MvPolynomial.combinedIdeal_associatedGraded`
  (`lem-trf-polynomial-combined-associated-graded`).

Also proved `AdicCompletion.equiv_of_powerQuotient_bijective`
(`lem-trf-completion-equiv-power-quotients`), the single shared inverse-limit
comparison used by both completion arguments.

Every private helper and constructed map in these five modules is complete.
There is no `sorry` in any delivered Lean file. This closes one existing hole;
it is not a decomposition into new unfinished statements. Existing holes in
`Sheaf.RingTheory.FormallyEtaleAssociatedGraded` are unchanged.

## No longer needed

Removed the original proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`
- `Sheaf.AlgebraicGeometry.EtaleLocalNormalForm`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.RingTheory.Smooth.Flat`
- `Mathlib.RingTheory.Flat.Localization`
- `Mathlib.RingTheory.Unramified.LocalRing`
- `WeilConjectures.RingTheory.FlatLocalCompletionIso`

The old direct proof dependencies no longer used by this route are:
`lem-weil-pbc-smooth-ring-map-iff-smooth-affine`,
`sbc-thm-etale-local-normal-form`,
`lem-weil-pbc-etale-ring-map-iff-etale-affine`,
`lem-weil-pbc-kahler-differentials-localization`,
`pqf-lem-locnoeth-lft`, `pqf-def-locnoeth`,
`lem-weil-pbc-localization-noetherian`,
`lem-weil-pbc-etale-algebra-flat`, `lem-weil-pbc-localization-flat`,
`lem-weil-pbc-flat-over-localization`,
`lem-weil-pbc-etale-prime-generates-maximal`, and
`lem-weil-pbc-flat-local-completion-iso`.

The smooth chart is obtained directly from
`Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial`, and localizations
are formally etale. The formally etale quotient theorem replaces the flatness,
Noetherian-localization and flat-local completion steps. Some old dependencies
may remain transitively needed by the reused generic theorem; no declaration or
module is withdrawn. The old definition dependencies for power series and associated
graded rings remain statement dependencies, while completion-mod-power is now
used within the proved polynomial-model completion theorem.

Removed the obsolete top-level tool approvals for
`lem-weil-pbc-smooth-ring-map-iff-smooth-affine`,
`sbc-thm-etale-local-normal-form`, `pqf-def-locnoeth`, and
`lem-weil-pbc-flat-local-completion-iso`. The essentially-smooth definition remains.
The generic `lem-sfb-augmented-etale-associated-graded` theorem is newly used
for its stated infinitesimal quotient and graded isomorphisms, not merely for
a definition from its module. It replaces a generic commutative-algebra tool;
no unit route is bypassed.

The repair also removes the duplicated private declarations
`Algebra.completion_eval_factor`,
`Algebra.completion_equiv_of_powerQuotient_bijective`,
`MvPolynomial.completion_eval_factor`, and
`MvPolynomial.completion_equiv_of_powerQuotient_bijective` from the returned
packet. No existing library module or public declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The returned packet duplicated the two inverse-limit helper proofs. The
maintainer's duplicate check was correct; the repair now shares the comparison
through a separate module, avoiding a cycle between the two consumers.

The mathematical statement and original plan are valid. Mathlib already has the
ring-level normal form needed here, so the scheme conversion in Step 1 and the
flat-local completion detour in Steps 4–5 are unnecessary. Original Steps 6–9
contain genuine polynomial coefficient/completion/graded calculations; they are
now fully formalized in the three new proved modules rather than hidden as glue.

The resumed sandbox contained a substantial partial implementation. Its polynomial
completion proof needed an explicit polynomial type annotation on a coerced
constant. Its graded comparison was still unfinished; this delivery proves it.
The assembled main proof needed an explicit quotient subtype and the private import
of AdicCompletion.Topology for completeness transport. No statement was repaired
or weakened, and no consumer adaptation or change record is required.

## New nodes

`lem-trf-polynomial-combined-ideal-coefficients` records the proved coefficient
criterion for (I,X)^n, using the existing power-series criterion and a finite
monomial decomposition. Its module is
`Sheaf.RingTheory.PolynomialCombinedIdealCoefficients`.

`lem-trf-polynomial-combined-completion` records the proved completion comparison
with all constant-coordinate and residue compatibilities. Its proof identifies
finite quotients by truncation and coefficient lifting, takes compatible inverse
limits, and uses completeness of formal series over the completed base. Its module
is `Sheaf.RingTheory.PolynomialCombinedCompletion`.

`lem-trf-polynomial-combined-associated-graded` records the proved polynomial
tangent-cone comparison, constructed from homogeneous constants and degree-one
variables, with its injectivity and surjectivity established explicitly. Its module
is `Sheaf.RingTheory.PolynomialCombinedAssociatedGraded`.

Each inherits the item's chapter and unit, carries its exact Lean signature and
source calculation, and records actual searches. Whole-blueprint searches for
polynomial associated graded, polynomial completion, combined ideal, and polynomial
tangent cone returned no equivalent blueprint statement. There are no change records. The repair also searched the current blueprint
for `completion quotient`; no blueprint node matched that query.

`lem-trf-completion-equiv-power-quotients` records the fully proved generic
inverse-limit comparison extracted from the two consumers, with its actual Lean
signature and searches. Its module is
`Sheaf.RingTheory.CompletionEquivPowerQuotients`. The zero ideal, unit ideal,
zero ring and exponent zero require no extra assumptions. It is used by both
the main theorem and the polynomial completion theorem. No change record is
needed: the moved helpers were private additions in the unlanded packet, and
all existing public statements and definitions stay unchanged.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
