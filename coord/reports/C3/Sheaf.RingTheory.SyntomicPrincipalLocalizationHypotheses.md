## What changed

The existing theorem `Algebra.exists_completeIntersection_fibre_away` now proves the
prime-existence step directly using Mathlib's
`PrimeSpectrum.localization_away_comap_range`, then applies the fixed-prime fibre
transport substep. Its signature and public imports are unchanged.

Added `Sheaf.RingTheory.SyntomicPrincipalLocalizationFibreTransport`, containing
`Algebra.exists_completeIntersection_fibre_transport`. Its statement fixes the prime
and asks only for transport of the fibre witness. Its docstring gives the full
natural-language proof, including equality of the base primes, base change, compatibility
of canonical fibre primes, commuting the two principal localizations, and preservation
of the presentation and dimension under algebra equivalence.

The proof-only imports of `GlobalCompleteIntersectionPrincipalLocalization` and
`LocalizationPrimeResidueFieldIso` moved from the main module to the unresolved fibre
substep, whose recorded plan needs them. All new proof imports are plain imports.

## Proved and sorry left

Hole closed: `Algebra.exists_completeIntersection_fibre_away`, node
`lem-weil-pbc-syntomic-principal-localization-hypotheses`.

Hole added and left: `Algebra.exists_completeIntersection_fibre_transport`, node
`lem-weil-pbc-syntomic-principal-localization-fibre-transport`.

This is a decomposition: one original hole closed and one strictly smaller fibre
transport hole added, for net zero holes closed in the target import closure. The
prime-existence step is fully proved by Mathlib. The resulting main theorem still
has `sorryAx` through the fibre substep; it is not an axiom-clean completed result.
No definitions or arbitrary data witnesses were added.

## No longer needed

Removed direct proof imports from the main module:
`Sheaf.RingTheory.GlobalCompleteIntersectionPrincipalLocalization` and
`Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`. Both remain imported by the new
fibre module, so neither is claimed as a pruned module in the targets' closure.

The main node no longer directly uses these old proof dependencies:
`lem-weil-pbc-localization-prime-residue-field-iso`,
`lem-weil-pbc-localization-tensor-over-base`,
`lem-weil-pbc-localization-of-localization`,
`lem-weil-pbc-global-complete-intersection-principal-localization`, and
`def-weil-pbc-complete-intersection-over-field`. They remain in the fibre node's
proof plan. `def-weil-ring-localization-away` remains in the main node's prime step.
Thus none of the old dependencies is discarded from the overall mathematical route.

Removed the first worker's redundant new prime module, declaration
`Algebra.exists_prime_away_comap`, and node
`lem-weil-pbc-syntomic-principal-localization-prime`: Mathlib already proves its assertion.
These were undelivered sandbox additions, not library modules being pruned.

## Where the brief, the DAG or earlier work was wrong

The first worker's two new node statements accidentally repeated the entire original
statement, rather than their Lean assertions. Their proof plans were placeholders and
copied search queries did not address the new assertions. The main node's proof plan
still described the unsplit argument. The fibre docstring lacked enough detail to take
over its proof. These records and documentation have been corrected.

The original source file is not installed on this machine. The second reader checked
the authoritative Stacks pages instead:
[00SY](https://stacks.math.columbia.edu/tag/00SY) for the replacement by a principal
localization, and [00SA](https://stacks.math.columbia.edu/tag/00SA) for preservation of
global complete intersections. The explicit fibre-transport justification is written
by C3 from these ingredients, not quoted as a standalone Stacks theorem.

## New nodes

`lem-weil-pbc-syntomic-principal-localization-fibre-transport` states only the fixed-prime
fibre-transport substep. Its statement and verbatim Lean signature agree. Its three
proof steps name the base-change, residue-field, iterated-localization, and
complete-intersection dependencies, with their union in `proof_deps`. The node records
new independent LeanSearch (unavailable), leanfinder, loogle, and grep searches and truthful agent proof provenance.
No change record is needed: no existing statement, definition, or public import changed.

## Second reading by C3

1. Compared the main module with the repository using `diff`, and checked its theorem
   signature byte for byte with a script. Verdict: unchanged signature, definitions,
   visibility, and public imports. Only proofs and plain proof imports changed. The
   new fibre assertion is recorded in its own new node and module.
2. Compiled the delivered modules in import order, and compiled scratch copies with
   `#print axioms` for both declarations. Verdict: successful; the only axioms are
   `propext`, `Classical.choice`, `Quot.sound`, and the explicitly reported `sorryAx`.
   The only textual `sorry` is the whole proof of the named public fibre theorem.
   No `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or hollow definition.
3. Read the fibre statement independently and checked its small cases: if `g = 1`
   it is transport along an algebra equivalence; if `S` is the zero ring there is no
   prime; if `g` is nilpotent there is no prime avoiding it. In the general case the
   explicit proof in the docstring constructs `h₁` as the image of `h`; compatibility
   of the residue maps proves nonmembership and commuting localization proves the
   complete-intersection conclusion. Verdict: true, needed, and strictly the fibre
   portion of the argument with the prime already fixed, rather than a restatement
   of prime existence plus fibre transport. Independent leanfinder/loogle/grep searches (LeanSearch was also attempted but unavailable)
   found the tensor-localization ingredients but no public theorem proving this
   assertion. The duplicate Mathlib prime helper was removed.
4. Checked the shortest route: the main proof now uses the Mathlib prime-range theorem
   directly. The remaining fibre transport cannot be discharged just by the imported
   CI-localization theorem: canonical fibre-prime compatibility and the two
   localization equivalences remain to be formalized. Imports supporting statements
   are public; proof-plan imports are plain. The old dependencies are all accounted
   for above. Checked `dag/units/sk-thm-p1.json` `realized`: neither the main node nor
   the helper is a unit statement or realized step, and the mathematical route is
   retained below that level. Verdict: no unit bypass; no target-closure pruning claimed.
5. Checked the main and new node against their Lean declarations. Verdict after repair:
   the main proof plan records Mathlib prime existence and the fixed-prime transport;
   the new node has the correct statement, detailed proof steps, dependency union,
   source, proof provenance, searches, creation and blueprint records, and verbatim
   Lean signature. Removed stale copied review attestations from the new node.

Changed during second reading: removed the redundant prime helper/module/node; inlined
Mathlib's prime-range argument; moved the two old proof imports to the fibre substep;
expanded its proof docstring; corrected both DAG proof records, the new node's statement,
searches, and provenance; and corrected the report's accounting to call this a
one-for-one decomposition with no modules pruned.

The first dry run required a separate LeanSearch record: Loogle and LeanFinder
count as one search kind. Added the newly attempted LeanSearch query and its service
unavailability; no mathematical conclusion is asserted from the failed service.
