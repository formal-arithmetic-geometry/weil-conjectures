## What changed

Proved `RingTheory.dvr_etale_unit_root_diagram` with its original signature and docstring
unchanged. Its proof imports the new, fully proved module
`Sheaf.RingTheory.DvrUnitRootLocalSquare` and Mathlib's integral-subalgebra inverse API.
It constructs the fraction field of the upper DVR, extends the given fraction-field map,
checks both compatibility equations, and proves the algebra-generation equality using
integrality of the root and polynomial quotient representatives.

Added two fully proved theorem modules. `DvrUnitRootLocalSquare` explicitly constructs
the two root algebras, chooses a prime over the closed point by lying over, contracts
that prime, constructs the local square, and proves the polynomial quotient presentation.
`DvrUnitRootAtPrime` proves the DVR, locality, injectivity and residue-separability
properties of a fixed localization of a unit-root algebra. It uses the standard etale
pair API, flatness, the unramified local-ring maximal-ideal theorem, and an explicit
Krull-intersection factorization argument to prove the domain and DVR assertions.

Updated the original node's proof route and recorded both new proved nodes. No existing
statement, definition, visibility or public import changed. No other existing module
was adapted. All three modules compile individually in import order without warnings.

## Proved and sorry left

Closed the original hole:
`RingTheory.dvr_etale_unit_root_diagram`
(node `lem-sbc-dvr-etale-unit-root-diagram`).

Both new declarations are also completely proved:

- `RingTheory.dvr_unit_root_local_square`
  (node `lem-sbc-dvr-unit-root-local-square`);
- `RingTheory.dvr_unit_root_atPrime`
  (node `lem-sbc-dvr-unit-root-at-prime`).

Holes closed: 1. Holes added: 0. No `sorry` remains in any delivered module.
The two private factorization helpers in `DvrUnitRootAtPrime` are fully proved.
This is a proof, rather than a decomposition leaving lower holes.

## No longer needed

None of the original imports was removed: each supports the unchanged public statement.
The original node had no proof dependencies, so no existing dependency node or module
was pruned. Removed the redundant proof import `Mathlib.RingTheory.Flat.Stability` from the new
`DvrUnitRootAtPrime` module: `Flat.TorsionFree` already publicly imports
`Flat.Localization`, which publicly imports `Flat.Stability`. Each remaining proof
import supplies an API or instance used by the proof. No regular-local-domain theorem or
uniformizer-root construction is needed: the unit-root localization's domain property
is proved directly by cancelling powers of its uniformizer.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was corrected. The original plan had no stated proof
inputs; its construction is now made explicit and proved from Mathlib.

A temporary implementation rebuilt a subalgebra over a different scalar field and
caused a kernel deterministic timeout. Profiling and incremental checks located the
problem in that local record construction. Direct algebra-adjoin induction eliminates
it; the final modules compile in roughly three to five seconds each, with the original
compiler limits. No definition or interface needed changing.

Checked the degree-one case: the monic, derivative-unit and factorization arguments
include e=1 without requiring e>1. The root algebra need not be a domain before
localization (for example when the polynomial splits); domainhood is proved only for
the selected local factors. The argument makes no injectivity, ramification or residue
separability assumption on A->T, beyond its stated locality. Invertibility of e is
mapped from A to T for the second application. The unit's route is unchanged.

## New nodes

`lem-sbc-dvr-unit-root-local-square` records the proved theorem in
`lean/Sheaf/RingTheory/DvrUnitRootLocalSquare.lean`. Its source is the local square in
the first claim of Stacks Tag 0BRM. It isolates and proves the ring construction before
any fraction field is introduced. Its only project proof dependency is the next node.

`lem-sbc-dvr-unit-root-at-prime` records the proved theorem in
`lean/Sheaf/RingTheory/DvrUnitRootAtPrime.lean`. Its sources are the unit-root finite
etale construction of Tag 0BRM and the DVR factorization criterion of Tag 00PD. It
uses only Mathlib, and handles an explicit root algebra and an arbitrary prime above
the closed point. LeanSearch was unavailable; LeanFinder and source searches found
the standard-etale, unramified-local-ring, flatness and Krull-intersection APIs used
in the proof, rather than an exact theorem already constructing these objects.

No change record is needed: the only existing module change is its proof and private
proof imports; the two new modules have matching new nodes.

## Second reading by G2

1. **Interface — pass.** Compared the original module with its repository version by
   `diff -u`: only two plain proof imports and the theorem proof changed. The existing
   signature, docstring, visibility, public imports and all definitions are byte for
   byte unchanged. Compared the existing node: only `proof`, `proof_deps` and
   `proof_origin` changed. No change record or forced adaptation is needed.
2. **Proof — pass.** Read all three modules, including both private factorization
   helpers, and compiled all three in import order with `lcompile.py`, without warnings.
   There is no `sorry`, forbidden declaration form or hollow definition. Scratch
   copies with `#print axioms` check all three public theorems; each uses only `propext`,
   `Classical.choice` and `Quot.sound`. In particular the original theorem is closed
   without relying on upstream holes. The existential choices (a lying-over prime,
   uniformizer and polynomial representatives) come from proved theorems; root
   algebras, localizations and the fraction field are explicit constructions.
3. **New statements — pass.** No open statement was split off: both new theorems
   are fully proved and strictly isolate parts of the original construction. Checked
   the degree-one case, split root polynomials, and local maps A->T which need not be
   injective. No domainhood of the unlocalized root algebra is assumed. Positivity
   excludes the constant-polynomial case; invertibility of e excludes inseparable
   residue roots. The statements match their nodes verbatim. Independent LeanFinder
   search for a Noetherian local ring with a regular principal maximal generator and
   Loogle search `IsLocalRing _, IsLeftRegular _` found no directly usable replacement.
   Searched both library roots for unit-root and factorization results. The related
   `regular_principal_prime_dvr` requires a principal prime in the unlocalized ring;
   the general regular-maximal-generator helper there, and the factorization helpers
   in `CohenCompletionDVR`, are private. They do not replace this proof's public API.
4. **Route and pruning — pass after import cleanup.** Read from the top down: the
   fraction-field lift and integral-subalgebra inverse closure give generation; the
   lower square supplies polynomial quotient representatives; the fixed-prime lemma
   proves its DVR assertions by regularity, Krull intersection and factorization.
   Reviewed the source [Stacks Tag 0BRM](https://stacks.math.columbia.edu/tag/0BRM)
   and [Tag 00PD](https://stacks.math.columbia.edu/tag/00PD). The original node had
   empty `proof_deps`, so no original dependency was omitted from `No longer needed`.
   The unit `sk-prop-input-spreading` and its `realized` arrays are unchanged, and the
   same unit-root step of its trait argument is retained. Removed one redundant
   private proof import, `Mathlib.RingTheory.Flat.Stability`, and recompiled the set.
5. **DAG — pass.** Each Lean statement equals its node's recorded signature. Read
   every proof step, checked the union of `uses` equals `proof_deps`, and verified
   the actual dependency chain diagram -> local square -> fixed-prime theorem.
   Both new nodes have source, proof origin, three search records, creation data,
   blueprint ancestry, chapter/unit and complete Lean records. No existing node
   outside the item is changed.

Second reading changed only the redundant import and this report. The mathematical
proofs and statements needed no repair. Holes closed: 1; holes added: 0; open split-off
statements: 0; two new intermediate theorems proved in full; modules pruned: none.
