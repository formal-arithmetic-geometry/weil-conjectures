## What changed

Proved the normalized realization and its uniqueness on the constructible finite-Tor
inputs, and proved identification of the strict scalar-limit arrow with the actual
proper/open scalar mate under these realizations. Public signatures and chosen
realization maps are preserved.

The new, fully proved module CompactSupportProjectionRealizationLift constructs the
underlying normalized morphism from QcqsCompactSupportStrictReductionComparison.
It transports between the arbitrary input reduction calculus and the supplied
calculus by uniqueness of left adjoints, and proves the finite adjunct identities.
The construction has compiled successfully. Invertibility and uniqueness are proved
using the existing qcqs finite
comparison and constructible Milnor injection. The gamma proof uses the existing
scalar-limit finite equation, the actual coefficient comparison reduction equation,
and the same injection after descent from the ramified cofinal subsequence.
Profiling identified expensive Mono-instance search when cancelling large derived
functor images. The gamma proof cancels their explicit isomorphisms instead,
without unfolding those functors or changing any shared definition. The full item
still measured 70 seconds after this improvement, so the realization and gamma
components now live in CompactSupportProjectionRealization and
CompactSupportScalarGammaIdentification. The original module publicly re-exports
the exact existing declarations and chosen realization definition. Their nodes
carry the moved Lean attachments. No direct Lean importers of the original item
were found, so no existing consumer required adaptation. See
coord/changes/B3-compact-support-projection-proof-components.md.

The finite comparison is changed to finiteTensorMap using the existing
comparison_factorization theorem. The reduction-square equation uses the generic
comparison_reduction law in IntegralCompactSupportCoefficientComparison, not that
module's overall integralCoefficientComparison assertion.

The proof uses existing named geometric statements even where those statements
remain sorry. No claim is made that the complete dependency closure is axiom-free. Delivery
compilation and its axiom probes completed before the metadata preflight. That
preflight exposed a coarse-node cycle, corrected by replacing the finite-mate
node's dependency on the whole integral comparison with a node for its exact
existing openComparison_isIso helper; no Lean code changed in that correction.
The new lift is a proved categorical component, not a split-off theorem hole.

Validation: lcompile.py --all returned exit code 0 for all four Lean modules.
The construction, unique realization, gamma identification and original assembly
all compile against the same sandbox. All original public declaration headers
match across the re-exports; node signatures and proof-dependency unions match.
No profiler/debug options or overlong Lean lines remain. The delivery warning check
also required replacing haveI/letI with have/let in proofs and explicitly omitting
two unused separatedness instances from the private constructibility helper.

## Proved and sorry left

Starting holes: 3, all attached to
lem-pur-compact-support-scalar-projection-identification.

Closed:
- WeilConjectures.PurScalarProjection.realization_existsUnique
- WeilConjectures.PurScalarProjection.gamma_identification

Remaining:
- WeilConjectures.PurScalarProjection.native_scalar_identification

Added holes: 0. The new public theorem
WeilConjectures.PurScalarProjection.compactSupportProjectionRealization_lift
is fully proved.

Existing dependency hole made explicit, not added by this delivery:
WeilConjectures.PurCompactSupport.openComparison_isIso, attached to
lem-pur-open-coefficient-comparison-isomorphism. Its existing source file is
unchanged; this is a prerequisite attachment, not a split-off Lean theorem.

## No longer needed

For realization_existsUnique, the stronger completed-open tensor realization and
an additional direct proof of proper/total-limit commutation are unnecessary:
the existing normalized strict system comparison already supplies the morphism.
Constructibility and the finite comparison then prove it is an isomorphism.

For gamma_identification, the proposed augmentation/transposed-total-limit argument
using PerfectQuotientExchangeNormalization and TowerLimitTransposeNormalization is
unnecessary. Its finite equation is already a conclusion of
compactSupportScalarLimitReduction, and the constructible Milnor injection detects
the resulting equality. This injection is used only on the stated constructible
domain, not asserted on arbitrary derived objects.

The identity ramification fact uses the short Ideal.map_id argument, so the new
realization component does not import the full strict scalar-composition module.

No whole module is withdrawn. The finite-mate node no longer needs the full
lem-pur-compact-support-integral-coefficient-comparison as a proof prerequisite:
its actual proof uses comparison_factorization and the existing
openComparison_isIso, now attached to its own exact node. The native scalar
identification retains its original proof obligations and comparison dependencies.
Existing public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The finite-mate node had a coarse prerequisite
that incorrectly treated its open-isomorphism helper as dependence on the whole
integral comparison, creating a DAG cycle when the new realization was attached.
The declaration-specific correction is recorded in
coord/changes/B3-compact-support-finite-mate-prerequisite.md.

The original augmentation plan is stronger than
needed for the two closed holes. In particular, the prohibition on assuming
arbitrary reduction faithfulness does not prohibit the proved constructible
Milnor injection available under the finite-field hypotheses.

## New nodes

lem-pur-compact-support-projection-realization-lift:
Sheaf.Paper.CompactSupportProjectionRealizationLift,
WeilConjectures.PurScalarProjection.compactSupportProjectionRealization_lift.
A fully proved normalized morphism construction; it asserts neither invertibility
nor uniqueness for an arbitrary ambient input. The original node records the
separate constructible invertibility, uniqueness, and scalar-identification steps.


lem-pur-compact-support-projection-realization:
Sheaf.Paper.CompactSupportProjectionRealization,
WeilConjectures.PurScalarProjection.realization_existsUnique and realization.
The existing declaration names, statements and chosen map are preserved in a
self-contained proved component after profiling the complete file.

lem-pur-compact-support-scalar-gamma-identification:
Sheaf.Paper.CompactSupportScalarGammaIdentification,
WeilConjectures.PurScalarProjection.gamma_identification.
The existing scalar-identification statement is preserved in a proved component.
The cofinal finite-reduction argument and explicit mate factorization introduce
no theorem hole.

Change record: coord/changes/B3-compact-support-projection-proof-components.md.


lem-pur-open-coefficient-comparison-isomorphism:
WeilConjectures.PurCompactSupport.openComparison_isIso, already declared in
Sheaf.Paper.IntegralCompactSupportCoefficientComparison. This node attaches the
unchanged existing named prerequisite for finite mates; it adds no Lean file,
statement or hole. Its proof plan identifies the actual scalar-adjunction
presentation with the normalized geometric open comparison.

Change record: coord/changes/B3-compact-support-finite-mate-prerequisite.md.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
