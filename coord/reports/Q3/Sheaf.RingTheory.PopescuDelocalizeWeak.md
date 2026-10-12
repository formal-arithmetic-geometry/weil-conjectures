## What changed

Replaced the sole `sorry` in `Sheaf.RingTheory.PopescuDelocalizeWeak` with a complete
Lean reduction following Stacks Tag 07F9 (`lemma-delocalize-weak`, lines 2162–2227).
The source was read in the available local Stacks checkout at
`/home/ubuntu/work-bp/sheaf/literature/stacks-project/smoothing.tex`.

The main proof opens the resolution, proves its extended singular ideal is the unit
ideal using locality and `Ideal.radical_eq_top`, and applies the existing final-solve,
standard-smooth-retract, and include-generators declarations. It combines the two new
polynomial statements below with the existing localization-smoothness declaration.
It explicitly constructs the quotient by the relations of `A` and the homogenized
relations, constructs both algebra maps through quotient lifts and the presentation
isomorphism, proves their composite is the original map, proves finite presentation,
and exhibits a singular-ideal element whose image lies outside the prime. A universe
lift puts the explicitly constructed quotient into `Type (max u v)`; the existing
proved `singularIdeal_map_equiv_le` transports its witness.

Added proof imports of `Sheaf.RingTheory.PopescuWeakClearPresentation`,
`Sheaf.RingTheory.PopescuWeakHomogenize`, and
`Sheaf.RingTheory.SingularIdealMapEquiv`. Existing signatures, visibility, public
imports, definitions, and docstrings are unchanged. No other existing module is adapted.
The item's node now records the implemented route and the two polynomial steps.

## Proved and sorry left

Closed the original hole in
`Algebra.exists_factorization_singularIdeal_not_le_of_local_popescu_resolution`
(node `lem-weil-pbc-popescu-delocalize-weak`): its entire combining proof compiles.
No `sorry` remains in the item's module.

Added two holes, each a public theorem whose whole proof is `:= by sorry`:

- `Algebra.exists_cleared_submersive_presentation`, node
  `lem-weil-pbc-popescu-weak-clear-presentation`, module
  `Sheaf.RingTheory.PopescuWeakClearPresentation`.
- `Algebra.exists_homogenized_local_equations`, node
  `lem-weil-pbc-popescu-weak-homogenize`, module
  `Sheaf.RingTheory.PopescuWeakHomogenize`.

This is a decomposition: one upper hole closed and two lower holes added, net -1.
It is not a claim of a fully sorry-free delocalization theorem. Existing imported
statement holes remain with their own nodes. Each new theorem has its source and a
complete proof in words. The first concerns only a submersive polynomial presentation
over the localized base; the second concerns polynomial evaluation in a localized
target and has no smoothness or resolution hypothesis. Neither states the original
factorization conclusion. The main module performs the quotient construction and
all the assembly; no new data definition chooses an arbitrary unproved witness.

All three delivered modules compile together without errors or warnings using
`lcompile.py --all`. The completed proof also compiles without any additional Lean
options. Edge cases checked against the statements and their construction: empty
relation families (empty determinant and denominator product are `1`), no extra
variables (common target denominator `1`), no original generators, zero equations
(empty support degree `0`), and rings with zero divisors (the localization kernel is
killed by an extra denominator, never by assuming localization injective). The target
prime ensures the target is nonzero; the auxiliary construction need not assume an
integral domain. The two new nodes retain the item's chapter and unit and its
blueprint ancestor; no unit-level step is bypassed.

## No longer needed

Removed the redundant proof import `Sheaf.RingTheory.SingularIdeal`, whose declarations
are already visible through the retained public import `PopescuResolution`.
This removes an import line, not a module from the target closure.
The second reader also removed redundant imports of
`Mathlib.Algebra.MvPolynomial.Rename` from `PopescuWeakClearPresentation` and
`Mathlib.Algebra.BigOperators.Fin` from `PopescuWeakHomogenize`: both are already
publicly imported by retained statement dependencies.

Removed from the main node’s direct `proof_deps`:

- `lem-weil-pbc-polynomial-scalar-extension`;
- `lem-weil-pbc-localization-base-change`;
- `def-weil-pbc-module-localization`.

These remain indirect dependencies of
`lem-weil-pbc-popescu-weak-clear-presentation`; no corresponding module is claimed
as pruned from the target import closure. Target denominator clearing occurs below
`lem-weil-pbc-popescu-weak-homogenize`. All other planned lemmas are retained.
The retained public imports support the original signature and its required instances.

## Where the brief, the DAG or earlier work was wrong

The existing detailed argument is usable, but steps 6–9 and 10–11 did not have
standalone Lean conclusions carrying their polynomial data. The two new nodes make
those conclusions explicit. Their existing dependencies alone do not directly
supply the needed certificates or the partially homogenized evaluated equations.

As the original docstring already observes, minimality is unnecessary: any ideal of
the local target which is not contained in its maximal ideal is the unit ideal.
The original `hminimal` binder is retained exactly; no hypothesis or conclusion changes.

LeanSearch was attempted for both new statements and returned an Internal Server
Error. This is recorded as unavailable, without a negative verdict. LeanFinder,
Loogle, Mathlib/source grep, and blueprint searches supplied ingredients but no
complete existing statement. The source checkout's dehomogenization equivalence is
for degree-zero homogeneous localization, not the partial homogenization and common
annihilator needed here.

## New nodes

`lem-weil-pbc-popescu-weak-clear-presentation`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-popescu-weak-clear-presentation.json`
and `lean/Sheaf/RingTheory/PopescuWeakClearPresentation.lean`. It packages original
steps 6–9: clearing the equations, inverse-determinant certificate, and source
relation certificates. It does not refer to a target factorization.

`lem-weil-pbc-popescu-weak-homogenize`:
`dag/nodes/sec-proper-base-change/lem-weil-pbc-popescu-weak-homogenize.json`
and `lean/Sheaf/RingTheory/PopescuWeakHomogenize.lean`. It packages original steps
10–11: partial homogenization, common denominators, and a common annihilator.
It requires neither smoothness nor a presentation of the source algebra.

No interface change record is needed: every existing signature and public import
is unchanged, and the only new declarations are in new modules imported for the proof.

## Second reading by Q3

1. Compared the main module with the repository using `diff -u`. Its sole existing
   declaration's signature, visibility, docstring, and all public imports are byte
   for byte unchanged; only its proof and proof imports differ. The other two
   modules are new. No definition or target statement changes. Verdict: pass.
2. Independently compiled all three delivered modules in dependency order. Scratch
   copies with `#print axioms` for each declaration reported only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The main module has no `sorry`;
   the two new modules each have exactly the named whole-theorem hole listed above.
   Checked for forbidden declarations and hollow definitions; none occur. The
   quotient algebra, evaluation maps, and universe lift are real constructions
   inside the theorem proof, not data definitions choosing arbitrary unproved
   witnesses. Verdict: pass as a decomposition, not a sorry-free result.
3. Read both new statements against Stacks `smoothing.tex` lines 2179–2211 and
   checked their finite-family arguments. The cleared relations differ from the
   localized relations by scalar units; the determinant changes by their product.
   Clearing ideal-membership certificates requires a further kernel annihilator,
   which the supplied proof explicitly includes. Partial homogenization shifts
   old indices by one, leaves the initial variables fixed, and uses a separate last
   variable; its exponent bound counts only the last `m` old variables. Checked
   `n=m=c=t=0`, empty relations, zero polynomials, and noninjective localization:
   empty products/determinants are one and kernel annihilators handle zero divisors.
   Both conclusions are strictly smaller polynomial steps, with no factorization
   or singular-ideal conclusion. Repeated LeanFinder, Loogle, and grep searches
   with different wording: `MvPolynomial.isLocalization`, `pderiv_map`, and finite
   integer multiples supply ingredients, but no complete replacement for either
   statement; upstream dehomogenization addresses a different graded localization.
   Neither remaining hole has a short existing-lemma proof. Verdict: pass.
4. Read the combining proof from its conclusion back through singular-ideal
   transport, localization smoothness, the explicitly constructed quotient/maps,
   homogenization, coefficient clearing, and the existing local smooth reduction.
   The route agrees with Tag 07F9 and retains the relevant nodes below the fixed
   `sk-thm-p1` unit; inspected its `realized` statement and steps, which need no
   change. Proof-only Sheaf imports remain plain imports; retained original public
   imports support the signature and its localization instances. Removed two
   redundant imports from the new modules. Expanded `No longer needed` to list
   every removed direct dependency and distinguish them from modules pruned out
   of the target closure (none). Verdict: pass after those corrections.
5. Compared old/new JSON records: the main node changes only `proof`, `proof_deps`,
   and `proof_origin`; the union of step dependencies is the recorded dependency
   list. Both new nodes have matching Lean statements, source, full proof steps,
   search records, chapter/unit, blueprint ancestry, and creation/Lean records.
   Corrected stale step numbers in the main node and replaced its inaccurate
   reference to total degree with the actual extra-variable degree bound used by
   Lean. The auxiliary `n ≤ c` fact is not used by the implementation; the node's
   presentation description now records only the consumed bound `c ≤ n+m`.
   Verdict: pass after those documentation corrections.

Second reading changed the DAG proof descriptions, the direct-dependency pruning
report, and two redundant new-module import lines. The combining Lean proof and
all theorem statements were retained.
