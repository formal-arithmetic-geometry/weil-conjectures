## What changed

Replaced the hole in `Algebra.relativeGlobalCompleteIntersection_partial_local_flat` by a
complete reduction with its original signature. A proved private helper
`Algebra.noetherian_prefix_flat` takes prefix flatness from Grothendieck's existing
closed-fibre lifting theorem, using the existing complete-intersection closed-fibre
regularity theorem, and restricts scalars from the localized base. The upper proof
constructs coefficient-model equalities, supplies every Noetherian stage through base
change, and proves the equality between prefix list ideals and the displayed image-set
ideal, including repeated equations.

Added `Sheaf.RingTheory.PolynomialLocalFlatQuotientDescent` for the finite-coefficient
quotient-colimit step. Updated the item's DAG proof, dependencies and proof origin to
match this reduction. Every new proof-only import is non-public; public imports and
existing signatures are unchanged.

## Proved and sorry left

Closed the one original hole in
`Algebra.relativeGlobalCompleteIntersection_partial_local_flat`
(node `lem-weil-pbc-relative-global-complete-intersection-partial-local-flat`).
The private helper `Algebra.noetherian_prefix_flat` has no hole.

Added one hole:
`RingTheory.flat_polynomial_local_quotient_of_finiteType_subrings`
(node `lem-weil-pbc-polynomial-local-flat-quotient-descent`). This is a decomposition,
not a net reduction of one hole: the outstanding statement covers only the general
finite-coefficient descent step, assumes stage flatness, and makes no
complete-intersection assumption or conclusion. Its full proof in words constructs
compatible quotient maps and checks representations and eventual vanishing before
applying the existing directed-union-subrings flat-module theorem.

Existing imported holes, including Noetherian approximation and Grothendieck lifting,
are unchanged. No hole remains in the item's own module; no definition was introduced
and no arbitrary data was selected from an unproved existence theorem.

Edge cases checked: the new descent statement permits empty equation lists, zero
quotient modules, `i=0`, and `i≥c`; it imposes no containment condition on the prime.
The upper proof keeps `i≤c`, treats repeated equations by existential list-index
membership, and derives prime containment from the quotient map. The zero original
quotient has no prime and so needs no separate construction.

## No longer needed

Removed direct proof imports:

- `Mathlib.RingTheory.MvPolynomial.Basic`: removed during the second reading; the
  retained imports already provide the polynomial flatness and Noetherian instances.

- `Sheaf.RingTheory.DirectedUnionSubringsFlatModule`: used by the new generic descent
  module instead of by the upper proof.
- `Sheaf.RingTheory.FibreLocalRingNaturalIso`: the existing closed-fibre regularity theorem
  packages the fibre identification needed by the upper proof.
- `Sheaf.RingTheory.GlobalCompleteIntersectionLocalRegularSequence`: likewise packaged
  by that existing closed-fibre regularity theorem.

The item's direct DAG dependencies no longer include
`def-weil-pbc-noetherian-ring`, `def-weil-pbc-free-module`,
`def-weil-pbc-localization-at-prime`, `def-weil-pbc-regular-sequence`,
`lem-weil-pbc-polynomial-scalar-extension`, `lem-weil-pbc-fibre-ring-primes-bijection`,
`def-weil-pbc-relative-global-complete-intersection`,
`lem-weil-pbc-global-complete-intersection-local-regular-sequence`,
`lem-weil-pbc-fibre-ring-local-ring-natural-iso`,
`def-weil-pbc-finite-type-algebra`, and
`lem-weil-pbc-directed-union-subrings-flat-module`.
Their required content stays under the existing closed-fibre theorem or the new descent
node. These are removals of direct dependencies, not claims that the corresponding
modules leave the targets' entire import closure. No blueprint unit realization is
bypassed and no whole transitive module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The DAG plan is mathematically sound. Its steps 1–3 can use the already landed
`Algebra.isRegular_closedFiber_of_relativeCompleteIntersection`; they do not need a
second formalization of the fibre geometry in this module. Steps 5–7 lacked a ready
interface for the finite-coefficient polynomial prefix-quotient system; that interface
is the new generic descent statement.

LeanSearch returned Internal Server Error, recorded as unavailable. Loogle found
fixed-module localization tests, not the varying-coefficient descent theorem. The
Mathlib grep and searches of both project roots and the imported blueprint found no
exact generic descent theorem. The source was read at the Stacks pages for Tags 00SV
and 05UU, since the cited local `literature/stacks-project/algebra.tex` is absent here.

The earlier attempt was blocked because the shared last-green cache lacked
`Sheaf.RingTheory.RelativeCompleteIntersectionClosedFiberRegularSequence.olean`.
That dependency is now available. On resumption, `lcompile.py --all` compiled the
actual generic descent module in 2.6 seconds and the actual upper module in 4.2
seconds, with exit code zero. No dependency was copied, restated or modified.

The resumed review checked the existing closed-fibre theorem and lifting theorem
signatures, the coefficient approximation and base-change interfaces, the new
statement's edge cases, and the unit's `realized` list. The reduction stays below the
unit level and bypasses none of its realized steps. The source argument was checked
again against [Stacks 00SV](https://stacks.math.columbia.edu/tag/00SV) and
[Stacks 05UU (2)](https://stacks.math.columbia.edu/tag/05UU).

The resumed `deliver3.py --no-push` dry run printed `OK`: compilation and preflight
passed except for the second reading, which is reserved for the second reader.
Nothing was pushed. The item is ready for that independent reading.

## New nodes

`lem-weil-pbc-polynomial-local-flat-quotient-descent`, in
`dag/nodes/sec-proper-base-change/`, states the generic passage from flat prefix
quotients at all finite type coefficient subrings to the full coefficient ring.
Its source is the displayed quotient colimit in the second paragraph of the proof
of Stacks 00SV and the application of 05UU (2). Its statement needs no dimension,
regularity or complete-intersection theory and is strictly the descent part of the
argument. It inherits `sec-proper-base-change` and `sk-thm-p1` from the item.
There are no interface changes, forced adaptations or change records.

## Second reading by R3

Independent second reader, 2026-10-13:

1. **Visible interfaces — PASS.** Diffed the delivered upper module against the repository
   version and compared the existing theorem signature programmatically: byte for byte
   unchanged. Both existing public imports and declaration visibility are unchanged.
   There are no altered definitions, target statements, forced adaptations or change records.
2. **Kernel proof — PASS as a decomposition.** Compiled both modules with `lcompile.py --all`.
   Scratch copies with `#print axioms` for the upper theorem, its private Noetherian helper,
   and the new descent theorem show only `propext`, `Classical.choice`, `Quot.sound` and
   `sorryAx`. The latter comes from the named new theorem and existing imported holes.
   The only delivered `sorry` is the public descent theorem's complete `by sorry` body.
   There are no new definitions or forbidden declarations. The approximation witnesses are
   eliminated inside a proof of a proposition, not used to define arbitrary data.
3. **Split statement — PASS.** Read the new signature, docstring and node together with
   `directedUnionSubrings_flat_module`. Checked the fraction representation, common-denominator
   ideal-membership identity and eventual-zero argument. Polynomial subring inclusions are
   injective, so enlarging by the identity's coefficients suffices. Empty equations, `i=0`,
   `i>c`, repeated equations and zero quotients are covered; containment in `Q` is unnecessary.
   This is only the finite-coefficient passage, with stage flatness as a hypothesis, and
   strictly separates it from the Noetherian complete-intersection argument already proved
   in the upper module. It is not the original theorem renamed. Independent LeanFinder
   search for compatible semilinear flat-module systems, Loogle search for flat direct
   limits, and Mathlib grep for flat colimits/subrings found no direct replacement.
   Project-root searches found generic colimit criteria and weak-regularity descent, whose
   signatures do not supply this flatness conclusion without constructing the same system.
   The remaining construction is substantial, not a hole closable in a few minutes.
4. **Route and pruning — PASS after one import repair.** Checked the Noetherian local map,
   closed-fibre theorem and lifting theorem interfaces, and the base-change and coefficient
   equalities. Compared the proof with [Stacks 00SV](https://stacks.math.columbia.edu/tag/00SV)
   and [05UU (2)](https://stacks.math.columbia.edu/tag/05UU). Read `sk-thm-p1.realized`: this
   reduction is below its realized unit steps and keeps that route. Every removed old
   `proof_deps` entry is named under No longer needed. Removed the redundant new proof-only
   import `Mathlib.RingTheory.MvPolynomial.Basic` after the entire upper proof and axiom
   probes compiled without it. No whole-closure module pruning or net hole reduction is
   claimed.
5. **DAG agreement — PASS.** Both nodes' `proof_deps` are exactly the unions of their
   proof-step uses. The upper node describes the helper, approximation, stage proof and
   descent application actually written. The new node has source, complete proof steps,
   searches, creation/blueprint/chapter/unit records and a verbatim Lean signature. Its
   docstring identifies that node and supplies the complete natural-language proof.

Second reading changed only the redundant proof import and this report; the mathematical
reduction and split statement needed no repair. One original hole closed, one new hole
added: decomposition, net zero.
