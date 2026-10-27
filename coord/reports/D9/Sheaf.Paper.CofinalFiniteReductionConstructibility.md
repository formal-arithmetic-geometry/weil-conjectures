## What changed

Proved all three theorems in `Sheaf.Paper.CofinalFiniteReductionConstructibility`
without changing any public signature, definition, or public import. The ideal
inclusion is principal-ideal arithmetic. Quotient compatibility and the completed
projection equation use the existing cofinal coefficient cocone. The main theorem
uses the given normalized presentation, the existing K-flat change-of-rings theorem,
and finite scalar-extension constructibility/Tor preservation.

A proved private comparison identifies an arbitrary presented derived extension
with the canonical scalar functor by uniqueness of universal left derived functors.
Two proved private helpers transport Tor amplitude and extract its cohomological
vanishing, using the existing bounded-flat-model theorem. Private imports with
`import all` reuse already proved helpers in the scalar-extension, adic-coefficient,
and constructibility modules. Added only a local size-specific site instance and
section-scoped instance removals; the change record is
`coord/changes/D9-cofinal-finite-reduction-proof-context.md`.

Updated the node proof and dependencies to match this route. The unit reconstruction
route is retained; its `realized` entries are empty and no unit record is changed.
The final server single-file compile passed with exit code 0, no warnings, and no
remaining `sorry` in this module.

## Proved and sorry left

Closed 3 original holes, all attached to
`lem-sp-cofinal-finite-reduction-constructibility`:

- `AlgebraicGeometry.ProEtale.sp_cofinal_finite_ideal_le`.
- `AlgebraicGeometry.ProEtale.sp_cofinal_finite_quotient_compatibility`.
- `AlgebraicGeometry.ProEtale.sp_cofinal_finite_reduction_constructibility`.

Holes left in the item: zero. Holes added: zero. Split-off statements: zero.
The existing coefficient cocone is used as a dependency, as required by stage 3;
this delivery does not claim to eliminate its hole or all transitive axioms.
All four private helpers (including the site-smallness theorem) are proved.

## No longer needed

Removed direct proof imports:

- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`.
- `Sheaf.Algebra.Homology.ScalarHomTensorCancellation`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`.

The planned `lem-sp-cofinal-quotient-kflat-bisystem`, module
`Sheaf.Algebra.Homology.CofinalQuotientKFlatBisystem`, is not needed by this
proof: the statement already quantifies over a normalized presentation, so its
normalized comparison is supplied directly by `n.derived`. Its K-flat assertion
follows from the existing generic flat-term change-of-rings theorem. No need to
construct another entire bisystem, or choose a fresh K-flat resolution of K.

Removed the direct proof dependency `lem-pc-kflat-resolution`; its resolution
existence is already encapsulated in the scalar-extension preservation theorem.
The direct proof does not use the normalization-existence theorem, coefficient
adjunction theorem, or scalar-tensor-cancellation theorem. Their corresponding
obsolete direct `tool_uses` entries were removed together with the resolution
entry. These dependencies remain where other existing proofs use them; no Lean
file or adopted source declaration is deleted. Public imports remain verbatim.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The planned bisystem theorem
constructs a presentation and normalization existentially, whereas this item must
work for every supplied presentation and normalization. Using its existential
output directly would therefore not establish the displayed theorem. The shorter
route uses the supplied normalization, compares each quotient presentation with
the canonical scalar functor through its universal property, and applies the
existing finite-ring preservation theorem.

Checked the e=0 compatibility case (its exponent hypotheses are impossible),
positive ramification e=1 and e>1, equality j+1=e*(N+1), and empty/zero complexes:
the same identities and transports apply. No additional flatness, completeness,
invertibility, or boundedness hypothesis was introduced. All finite rings are
the actual quotient rings and all coefficient maps remain their canonical maps.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
