## What changed

Replaced the sole sorry of
`Algebra.isRegular_localization_of_relativeGlobalCompleteIntersection` with a complete
Lean reduction following Stacks 00SV (1). Its signature and public imports are unchanged.
The proof extracts the finite type coefficient model from 00SU, proves the polynomial
coefficient equality, equips every larger finite type subring with its inclusion algebra
structure, uses 00SS to preserve the specified presentation, applies the Noetherian case,
and passes weak regularity to the original polynomial local ring. It proves that every
equation lies in the localized maximal ideal and uses Mathlib's finite-module criterion
for the final regularity condition.

Added four public helper modules, each with one public theorem and a new node:

- `Sheaf.RingTheory.PolynomialLocalClosedFiberEquiv`: proved the natural closed-fibre
  isomorphism by the fibre-prime correspondence, polynomial scalar extension, the existing
  natural fibre-local-ring quotient equivalence, equality of the extended maximal ideal,
  and localization of a ring equivalence. The formula holds for every polynomial.
- `Sheaf.RingTheory.RelativeCompleteIntersectionClosedFiberRegularSequence`: proved
  regularity in that closed fibre. A proved private field-case helper identifies the
  residue-field fibre of a field-algebra quotient with the quotient, obtains the additive
  dimension hypothesis, and applies the existing global complete-intersection lemma.
  The public proof applies base change and transports regularity using the natural formula.
- `Sheaf.RingTheory.RelativeCompleteIntersectionNoetherianRegularSequence`: proved the
  Noetherian case. Mathlib supplies polynomial flatness, flatness of the local map, and
  Noetherian localization. The existing 00MG declaration lifts the proved closed-fibre
  regularity to the polynomial local ring.
- `Sheaf.RingTheory.PolynomialLocalWeakRegularSequenceDescent`: states the remaining
  generic finite-coefficient descent argument, without a complete-intersection hypothesis.
  This has exactly one named public theorem with `:= by sorry` and a complete proof in
  words, following the displayed colimits and multiplication maps in 00SV and 00DB.

Updated the item's node proof, proof_deps and proof_origin to agree with the Lean proof.
No definitions, existing statement signatures, visibility, or other held modules changed.
The blueprint unit and its realized route are unchanged.

All five sandbox modules compile together through lcompile.py, in import order, with no
compiler errors or non-sorry warnings. The delivery dry run is the final verification.

## Proved and sorry left

Closed the original hole:
`Algebra.isRegular_localization_of_relativeGlobalCompleteIntersection`
(node `lem-weil-pbc-relative-global-complete-intersection-local-regular-sequence`).
There is no sorry remaining in the item's module.

Also proved these new public declarations:

- `MvPolynomial.exists_polynomial_local_closedFiber_equiv`
  (`lem-weil-pbc-polynomial-local-closed-fiber-equiv`).
- `Algebra.isRegular_closedFiber_of_relativeCompleteIntersection`
  (`lem-weil-pbc-relative-ci-closed-fiber-regular-sequence`).
- `Algebra.isRegular_localization_of_relativeCompleteIntersection_of_noetherian`
  (`lem-weil-pbc-relative-ci-noetherian-local-regular-sequence`).

Added exactly one hole, the sole sorry in the delivered modules:
`RingTheory.Sequence.isWeaklyRegular_polynomial_local_of_finiteType_subrings`
(`lem-weil-pbc-polynomial-local-weak-regular-sequence-descent`). This is a decomposition,
not a claim of a sorry-free proof: one original hole is closed and one generic hole is
added. The Noetherian argument and the combination with approximation and properness
are written in Lean. Existing imported declarations may themselves depend on sorry,
as intended in stage 3; their statements are not duplicated or changed.

Edge cases checked against the statements and proofs: an empty sequence has automatic
weak regularity, and its prime localization is nonzero; zero quotient rings admit no
prime containing all the equations; the field-case nonzero quotient forces `c ≤ n`
from the presentation hypothesis and uses `dimension + c = n`, not an invalid truncated
subtraction; the polynomial closed-fibre equivalence requires neither Noetherianity nor
complete-intersection hypotheses; finite type subrings containing R0 form a nonempty
cofinal directed system because R0 is finite type. Descent does not assume that the
coefficient-subring inclusions are flat.

## No longer needed

Removed these direct proof imports from the item's module:

- `Sheaf.RingTheory.FibreLocalRingNaturalIso`, used by the proved polynomial closed-fibre
  equivalence instead.
- `Sheaf.RingTheory.GlobalCompleteIntersectionLocalRegularSequence`, used by the proved
  closed-fibre regularity helper instead.
- `Sheaf.RingTheory.RegularSequenceFlatClosedFiber`, used by the proved Noetherian helper
  instead.

These three modules and their nodes remain needed transitively; none is claimed pruned
from the targets' closure. No other original proof-dependency node is discarded: the
polynomial, fibre-prime, flat-local-map, Noetherian, regular-sequence, and exactness nodes
are retained where the new helper proofs use them. No globally unnecessary module was
identified. Pruned modules: none.

The old direct proof-dependency nodes now delegated to helpers are
`def-weil-pbc-noetherian-ring`, `lem-weil-pbc-projective-module-flat`,
`lem-weil-pbc-flat-local-ring-maps`, `lem-weil-pbc-polynomial-scalar-extension`,
`lem-weil-pbc-fibre-ring-primes-bijection`,
`def-weil-pbc-relative-global-complete-intersection`,
`lem-weil-pbc-global-complete-intersection-local-regular-sequence`,
`lem-weil-pbc-fibre-ring-local-ring-natural-iso`,
`lem-weil-pbc-grothendieck-regular-sequence-flat`, and
`lem-weil-pbc-filtered-colimit-abelian-groups-exact`. They remain in the new helpers
through proof or statement dependencies; none is globally pruned.
The second reading also removed the redundant proof import
`Mathlib.RingTheory.Localization.Submodule` from the new Noetherian helper.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the item's statement or the six-step DAG plan was found.
The original plan's two large unstated interfaces were polynomial closed-fibre transport
and finite-coefficient descent of prefix quotient multiplication maps. The former is
now proved from existing declarations; the latter is isolated as a generic theorem,
strictly a part of the argument, with no complete-intersection hypothesis.

The cited local file `literature/stacks-project/algebra.tex` is absent on this machine.
I read the official Stacks source at https://stacks.math.columbia.edu/tag/00SV instead,
including its displayed localized prefix quotient colimits and injective multiplication
argument. LeanSearch returned an Internal Server Error for all attempted relevant
queries; the new nodes record it as unavailable. LeanFinder/Loogle and local source
searches were available and found transport lemmas, but no direct complete-intersection
or finite-coefficient descent theorem.

## New nodes

`lem-weil-pbc-polynomial-local-closed-fiber-equiv` states and proves the natural
isomorphism of a polynomial closed fibre with a localized polynomial ring over the
residue field, including the polynomial formula. Source: 0H9M and the first paragraph
of 00SV. Searches found scalar extension, prime correspondence, and localRingEquiv,
which the Lean proof combines; no direct complete statement was found.

`lem-weil-pbc-relative-ci-closed-fiber-regular-sequence` states and proves the field
regularity step of 00SV using base change, the proved polynomial closed-fibre equivalence,
and the existing field-case theorem 00SC. Searches found regular-sequence transport
lemmas, not this presentation-dependent closed-fibre result.

`lem-weil-pbc-relative-ci-noetherian-local-regular-sequence` states and proves the
Noetherian first paragraph of 00SV, using Mathlib's flat local map and the existing
00MG lifting theorem after the proved closed-fibre result. It is a special case of the
original argument and is needed at every finite type coefficient stage.

`lem-weil-pbc-polynomial-local-weak-regular-sequence-descent` is the single remaining
hole: localized weak regularity over all finite type coefficient subrings containing
a fixed finite type model implies weak regularity over the whole ring. Source: the
filtered-colimit paragraphs of 00SV and exactness 00DB. Its proof spells out finite
coefficient witnesses for localized rings and their prefix quotients. This is generic
and makes no complete-intersection or flat-inclusion assumption. Searches found
localization and flat transport, but no such finite-coefficient descent declaration.

No change records or forced adaptations are needed.


## Second reading by D4

1. Compared the existing module with the repository using diff and checked its theorem
   header byte for byte. Verdict: unchanged signature, docstring, visibility and public
   imports; only proof imports and the proof changed. All four other modules are new;
   no definitions or existing interfaces changed and no change records are required.
2. Compiled all five modules locally in import order. Inspected all source for forbidden
   declarations and data selection from unproved existence. Verdict: one explicit sorry,
   exactly the named generic descent theorem listed above; no hollow definitions, forbidden
   commands or arbitrary witness construction. Scratch-copy `#print axioms` checks for
   all five public theorems returned only propext, Classical.choice, Quot.sound and
   sorryAx. The latter is expected from the listed hole and existing open dependencies;
   the private fieldCase helper is included transitively in the closed-fibre check.
3. Read the generic descent statement and its complete docstring proof independently,
   and checked Stacks 00SV and 00DB. Verdict: true and strictly part of the original
   argument, with no complete-intersection assumption or properness conclusion. For c=0
   it asserts automatic weak regularity. For n=0 the same finite-coefficient argument
   applies to localized coefficient rings. A zero ring has no prime Q. The stage family
   is nonempty (R0 itself), directed, and contains every finite set after adjoining it.
   Every kernel relation in each prefix quotient is a finite ideal-membership expression;
   adjoining its coefficients and any clearing denominator moves it to a stage where
   hstage gives injectivity. No flatness of inclusions is needed. Independently searched
   LeanFinder for injectivity on successive quotients over filtered unions, Loogle for
   IsWeaklyRegular with Subring, Mathlib Regular sources for colimits/direct limits, and
   both project library roots for weak regularity. No direct replacement found. The
   other new helper statements match their proved natural identification, field case,
   and Noetherian special case. The remaining descent infrastructure is not a small
   missing tactic step and was left as the documented split.
4. Read the proof from the target downward through every helper and checked the old
   proof dependencies and dag/units/sk-thm-p1.json realized route. Verdict: the original
   approximation, field-dimension, flat-lifting and exactness route is retained below
   the unit level; no realized unit step is bypassed. The report now lists every old
   direct dependency delegated to helpers. There is no globally pruned module.
   Removed the redundant Localization.Submodule proof import and verified the helper
   still compiles; all public imports are needed by statements.
5. Checked every node against its Lean statement, all dependency-node references, the
   union of proof-step uses, source, origin, created record and blueprint ancestry.
   Verdict: all agree. Only proof/proof_deps/proof_origin differ on the existing node.
   Every new node has the same chapter/unit as the item, and its recorded Lean signature
   matches its declaration after trimming boundary whitespace.

Changes in this reading: removed one redundant proof import; corrected the descent
node's search entry that named LeanFinder but described Loogle results, replacing it
with the independent searches; made the delegated-dependency report exhaustive; added
this review. No mathematical statement or proof was rewritten. The delivery remains
one hole closed and one added (a decomposition, net zero), with three new public helper
proofs and one new public helper hole.
