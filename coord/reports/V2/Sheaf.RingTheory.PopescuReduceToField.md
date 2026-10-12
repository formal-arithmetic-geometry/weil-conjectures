## What changed

Replaced the sole `sorry` in `Sheaf.RingTheory.PopescuReduceToField.popescu_reduce_to_field`
with a compiling proof following Stacks Tag 07F5. Its signature is unchanged.
The proof combines three strictly smaller intermediate statements: a maximal bad quotient,
a standard nonzerodivisor obtained from the field case, and a compatible smooth lift
from the eighth-power quotient. Each intermediate has its own module, DAG node, source,
and complete proof in words.

The combining proof itself establishes reducedness using the existing nilpotent lifting
statement, establishes preservation of the nonzerodivisor using Mathlib flatness, proves
that the eighth-power ideal is nonzero, derives the annihilator conditions, applies the
existing strictly-standard desingularization and final-solve declarations, composes their
factorizations, and packages the factorization criterion's cocone as `ObjectProperty.ind`.
Added proof-only Mathlib imports for Noetherian nilpotence and flat torsion freeness.
Updated the parent's proof and dependencies to match this argument.

All four modules compile through `lcompile.py`; no warning is suppressed. The three new
statements were checked against Stacks Tag 07F5 and the stated dependency signatures.
Edge cases: a zero base cannot be a bad quotient; zero targets are permitted; the
nonzero reduced base ensures the total fraction product is nonempty; a unit denominator
has a zero eighth-power quotient and is still covered; all annihilator arguments work
also for zero targets. Universes remain `u` for the base and `max u v` for algebras,
targets, and filtered indices. Existential witnesses are used only in theorem proofs;
no definition chooses arbitrary data from an unproved existence statement.

## Proved and sorry left

Closed: `popescu_reduce_to_field` (node `lem-weil-pbc-popescu-reduce-to-field`).
There is no `sorry` left in the item module.

Added three holes:

- `exists_popescu_maximal_bad_quotient` in `Sheaf.RingTheory.PopescuMaximalBadQuotient`,
  node `lem-weil-pbc-popescu-maximal-bad-quotient`: original steps 1–2, with no field-case
  hypothesis and no conclusion asserting the main theorem.
- `exists_popescu_standard_nonzerodivisor` in
  `Sheaf.RingTheory.PopescuStandardNonzerodivisor`,
  node `lem-weil-pbc-popescu-standard-nonzerodivisor`: original steps 5–7; concludes a
  finite-presentation factorization with a strictly standard element, not a smooth
  factorization, and does not assume ind-smoothness of any nonzero quotient.
- `exists_popescu_smooth_lift_modulo_eight` in
  `Sheaf.RingTheory.PopescuSmoothLiftModuloEight`,
  node `lem-weil-pbc-popescu-smooth-lift-modulo-eight`: original step 9; assumes only
  ind-smoothness modulo the specified eighth power and concludes a compatible lift
  modulo the fourth power, without the field hypothesis or a smooth factorization
  of the original map.

This is a decomposition: one original hole closed, three lower holes added, net −2.
The existing `sorry` declarations used through imported dependencies remain their own
items; none was copied, changed, or proved here.

## No longer needed

Removed direct proof imports from the item:

- `Sheaf.RingTheory.FilteredColimitSmoothProduct`
- `Sheaf.RingTheory.PopescuDelocalizeBase`
- `Sheaf.RingTheory.PopescuLifting`
- `Sheaf.RingTheory.ReducedNoetherianTotalRingFractions`
- `Sheaf.RingTheory.RegularBaseChange`
- `Sheaf.RingTheory.SingularIdeal`
- `Sheaf.RingTheory.StrictlyStandardElement`

The first five belong to the three intermediate statements' proofs and their imports;
the last two are already provided by declarations the combining proof needs.
Corresponding original nodes moved below the intermediates in the DAG:
`lem-weil-pbc-regular-base-change`, `lem-weil-pbc-noetherian-ideal-set-maximal`,
`lem-weil-pbc-noetherian-finitely-many-minimal-primes`,
`lem-weil-pbc-reduced-noetherian-total-ring-fractions`,
`def-weil-pbc-localization-at-prime`, `lem-weil-pbc-popescu-product`,
`lem-weil-pbc-filtered-colimit-algebras-elementwise`,
`lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit`,
`lem-weil-pbc-popescu-delocalize-base`, and `lem-weil-pbc-popescu-lifting`.
They are still needed transitively. No globally unneeded mathematical module or node
is claimed as pruned, and no blueprint unit's statement or proof step is bypassed.

The second reader also removed the unused public `Sheaf.RingTheory.GRing` import
from the new `PopescuSmoothLiftModuloEight` module.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the item statement was found. Mathlib's `Ideal.map_top` must be
used explicitly here; `simp` alone did not rewrite it. The generic total-fraction and
quotient transport steps require additional Lean glue, so their conclusions have been
isolated rather than left as anonymous holes. LeanSearch returned HTTP 500; each new
node records this as unavailable, while LeanFinder and source searches found no direct
match. The local literature checkout lacks the TeX bodies, so the source proof was
checked on the official Stacks page for Tag 07F5, alongside the detailed existing DAG
proof and the imported declarations.

## New nodes

`lem-weil-pbc-popescu-maximal-bad-quotient`, module
`Sheaf.RingTheory.PopescuMaximalBadQuotient`: isolates Noetherian maximization, regular
quotient transport, and quotient-of-quotient transport. The parent proves reducedness.

`lem-weil-pbc-popescu-standard-nonzerodivisor`, module
`Sheaf.RingTheory.PopescuStandardNonzerodivisor`: isolates the product-of-fields,
finite-presentation factorization, delocalization, and elementary-to-strictly-standard
conversion. The parent proves flat preservation of the nonzerodivisor.

`lem-weil-pbc-popescu-smooth-lift-modulo-eight`, module
`Sheaf.RingTheory.PopescuSmoothLiftModuloEight`: isolates factorization modulo π⁸,
application of `popescu_lifting` with π⁴, quotient compatibility, and the unit singular
ideal. The parent applies desingularization and the final solve.

No statement or definition was changed, and no change record is required.

## Second reading by V2

1. Compared the item module with the repository using `diff -u`, and checked the
   existing theorem signature byte for byte with a Python slice: unchanged. The
   only existing node fields changed are `proof`, `proof_deps`, and `proof_origin`.
   The other three modules and nodes are new. No definitions or existing statements
   changed, and no change record is required. Verdict: pass.
2. Compiled all four modules in import order with `lcompile.py --all`; each compiled
   without warnings. A scratch module printed axioms for all four declarations:
   only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`, the latter from
   the named open dependencies. The scratch module was removed before delivery.
   Scanned the whole delivery: exactly the three reported named theorem holes, no
   forbidden declarations, no definitions selecting data from existence holes.
   The parent uses existential witnesses solely inside its theorem proof. Verdict: pass.
3. Read each split statement and its complete docstring proof against the official
   Stacks Tag 07F5 page (https://stacks.math.columbia.edu/tag/07F5), the original
   DAG plan, and the signatures of regular base change, total fractions,
   delocalization, lifting, strictly standard elements, and the singular ideal.
   Each isolates a strict part of the argument: maximal quotient selection,
   generic-fibre factorization, or lifting a specified quotient factorization.
   None concludes the parent theorem. Checked zero base/target, unit denominator,
   empty minimal-prime product, and the zero-variable initial minor. In particular
   a zero base cannot satisfy the bad-map premise; a zero target is allowed; a
   unit denominator permits a zero quotient and a vacuous quotient compatibility;
   nonzero reduced bases have a nonempty minimal-prime set; the initial minor
   conversion also works for c = 0. Checked universe bounds against the existing
   delocalization and lifting statements. Fresh LeanFinder searches used
   'ascending chain condition ideals maximal element of any nonempty set of ideals',
   'reduced Noetherian total quotient ring finite product of fields ind smooth
   factorization', and 'lifting smooth algebra factorization modulo a power of a
   nonzerodivisor'. Fresh Mathlib grep used quotient/lift terminology restricted
   to RingTheory/Smooth; also searched both library roots. The hits provide
   ingredients, not any of the split statements. The existing
   PopescuDesingularizeLiftingApply proves a different resolution statement and
   does not supply the required unit singular ideal or this factorization. None
   of the three holes can be closed by a short application of a found theorem.
   Verdict: pass, as a decomposition (one hole closed, three added, net −2).
4. Read the combining proof top down: it proves reducedness, flat preservation of
   nonzerodivisors, nonvanishing of the eighth-power ideal, the annihilator
   equivalences, unit singular ideal after desingularization, and the final
   composition, then packages the factorization criterion's colimit. These are
   real proof steps between the three narrower holes and existing dependencies.
   Compared old and new `proof_deps`: all ten removed direct dependencies appear
   in `## No longer needed`; they remain transitively needed. No global module
   pruning is claimed. Read `dag/units/sk-thm-p1.json`, including all `realized`
   statements and steps: this decomposition stays below the unit level and
   bypasses none of them. Removed the unused public `Sheaf.RingTheory.GRing`
   import from PopescuSmoothLiftModuloEight; its signature does not mention
   regularity. Other proof-only imports are plain imports. Verdict: pass.
5. Checked all four nodes: each `proof_deps` is exactly the union of the proof
   steps' `uses`; statements and Lean signatures agree; sources and proof origins
   follow 07F5. All three new nodes have the required source, searches, creation,
   blueprint, chapter/unit, and Lean records. Replaced their compressed
   `lean.statement` strings with the exact multiline declaration signatures
   from the delivered files, as required by the brief. Verdict: pass.

Second-reading changes: removed one unused public import and repaired three
verbatim Lean-signature records; added this review and fresh search evidence.
No mathematical proof, statement, or hole count changed.
