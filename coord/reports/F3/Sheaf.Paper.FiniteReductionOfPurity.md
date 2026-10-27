## What changed

Replaced the `sorry` in `WeilConjectures.PurityFiniteSetting.finiteReductionOfBaseChange`
by a proof of both original conjuncts. The source conjunct uses the new, strictly
smaller ordinary source-square lemma. For the exceptional conjunct, the proof
pastes that source square with the two instances of `finiteReductionOfPurity`.
It proves naturality of the actual pullback coefficient comparison directly from
its composite natural isomorphism, uses the existing input-naturality theorem for
purity, and cancels the first purity isomorphism. The private generic
`reduction_inverse_pasting` helper contains the cancellation argument.

Added proof-only imports of `Sheaf.Paper.FiniteReductionBaseChangeSource` and
`Sheaf.SecSmoothPurity.SmoothPurityNaturality`. Added the former module and its
node. Updated the parent node's final proof step, proof dependencies and origin
to describe this Lean proof. Existing public signatures, definitions, public
imports and the unit route are preserved. No source-library module was changed.

Validation: the new module and the modified item compile through `lcompile.py`.
The final item compile is clean, with no error or warning.

## Proved and sorry left

Initial item holes: 5. Closed item hole:
`WeilConjectures.PurityFiniteSetting.finiteReductionOfBaseChange`
(node `thm-pur-finite-reduction-of-purity`). Added hole:
`WeilConjectures.PurityFiniteSetting.finiteReduction_baseChangeSource`
(node `lem-pur-finite-reduction-base-change-source`). This is a decomposition,
not a net hole reduction: one item hole closed, one strictly smaller hole added.
The source lemma is only the ordinary source-square identity, with no purity
map or exceptional inverse image. The proof of the second conjunct from that
identity is complete Lean, rather than a renamed statement of the item.

The four retained item holes, all at
`thm-pur-finite-reduction-of-purity`, are:

- `WeilConjectures.PurityFiniteSetting.finiteReductionOfPurity`;
- `WeilConjectures.PurityFiniteSetting.finiteReductionOfUnitSmoothTrace`;
- `WeilConjectures.PurityFiniteSetting.finiteReductionOfCompositionSource`;
- `WeilConjectures.PurityFiniteSetting.finiteReductionOfCompositionExceptional`.

The earlier proofs of `finiteReductionOfSmoothTrace`,
`finiteReductionOfCompositionCoherence` and `finiteReductionOfAffineOrientation`
are retained. Total holes in delivered Lean files: 5 (four retained, one added).

## No longer needed

No modules or declarations are withdrawn and no original imports are removed.
The exchange-arrow proof does not use
`thm-pur-smooth-base-change-coherence`; its explicit three-arrow definition,
purity input naturality and the independent source square suffice. Removed
that node from this item's proof dependencies. The unresolved main, unit-trace
and separate composition clauses retain their earlier planned dependencies.
This does not assert that the base-change coherence node is unused elsewhere.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The prior parent proof record left base change
entirely unproved. The new proof makes its categorical pasting step explicit,
while isolating the coordinate compatibility still requiring proof. The source
lemma also applies without a constructibility or finite-Tor hypothesis: its
root-chart characterizations and scalar/pullback comparisons are defined for
arbitrary derived inputs. Edge cases checked in the argument are relative
dimension zero (unit charts), identity coefficient reduction, arbitrary
ramification and an arbitrary base morphism v. No quotient-flatness assumption
is introduced.

The rational twisted-pullback scalar-square node found in the whole-DAG search
uses finite field-extension coefficients, rather than finite quotient
coefficients. The existing finite tensor-presentation theorem states tensor
reassociation in fixed coordinates, rather than this intrinsic source square.
Neither supplies the new statement by direct specialization.

## New nodes

`lem-pur-finite-reduction-base-change-source`, in
`dag/nodes/sec-smooth-purity/lem-pur-finite-reduction-base-change-source.json`,
realized by `Sheaf.Paper.FiniteReductionBaseChangeSource` and
`WeilConjectures.PurityFiniteSetting.finiteReduction_baseChangeSource`.
It isolates the first conjunct of base-change reduction. Its source is the
blueprint proof's ordinary pullback, twist and shift compatibility step; its
proof in words expands compatible root charts and transposes the compositor
mate square to restriction. It has no dependence on the parent theorem and
introduces no definition or arbitrary chosen data. No change record is needed:
no existing statement or definition changed.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
