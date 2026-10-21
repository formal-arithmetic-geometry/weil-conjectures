## What changed

Completed `WeilConjectures.scalarCompletionAssociator` from the existing unrestricted
scalar subfamily in `Sheaf.Paper.CompletedLineTensorCoherence` and the specified
finite-free comparison. Constructed natural isomorphisms from the actual chi maps,
proved their normalization by naturality and cancellation, and proved uniqueness by
cancelling isomorphisms. The ordinary K-flat model formulas, completeness preservation,
pentagon and unit equations use the existing normalized declarations. No public
statement or data definition changes; no other Lean module is adapted.

The private proved `comparisonAlong` restricts an objectwise invertible natural
transformation along an arbitrary functor. Local irreducibility and transparency
settings keep the published scalar constructions behind their interfaces.
The change record is `coord/changes/B6-scalar-completion-proof-context.md`.

The updated DAG uses `lem-pur-completed-line-tensor-coherence` as a generic scalar
coherence tool: the used clauses have no coefficient-line hypothesis and do not
replace a geometric step of the parent projection-formula unit. Import-direction
and DAG reachability checks show no cycle. The unit record has no realized step
attached to this node, and its statement and route are preserved.

## Proved and sorry left

Closed: `WeilConjectures.scalarCompletionAssociator`
(`lem-fix-scalar-completion-associator`), the single original hole.
Added holes: zero. Split-off statements: zero. Remaining holes in the delivered
Lean module: zero. Existing imported declarations may still depend on sorry;
this delivery proves the assigned statement from those declared dependencies.

Validation: the complete module compiled through the prescribed `lcompile.py`
workflow with exit code 0, no warnings, and 53.6 seconds of compiler time.
The associator is presented by its published objectwise components; naturality is
inherited from the composite of natural comparison isomorphisms. This avoids the
repeated unfolding diagnosed in the initial composed-functor presentation, without
splitting the file, adding a proof hole, or changing the compile limit.

## No longer needed

Removed proof-only imports:

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`

The proof no longer directly needs these old proof-dependency nodes:

- `lem-weil-l-adic-extension-absolute-value`
- `lem-weil-l-adic-extension-integers-dvr`
- `lem-weil-pbc-constant-completion-equivalence`
- `lem-weil-pbc-sheafification-exact`
- `lem-weil-proetale-countable-products-exact`
- `lem-pc-kflat-resolution`
- `lem-pur-kflat-change-of-rings`
- `lem-pur-quotient-scalar-comparison-descent`
- `lem-weil-integral-scalar-extension-well-defined`
- `lem-sfb-successive-derived-quotient-normalization`
- `lem-pur-finite-free-completion-exchange`
- `lem-pur-finite-free-completion-exchange-coherence`
- `lem-fix-cofinal-roos-restriction`

The existing normalized scalar subfamily already supplies the ordinary model and
coherence results. Completeness and invertibility use finite-free comparison.
The specified normalization determines the assembled associator uniquely, so no
separate Roos exchange or cofinal-restriction calculation is needed here.
These dependencies may remain needed transitively or by other parents; no module
or declaration is withdrawn. All original public imports are retained.
Removed the obsolete top-level tool approvals for those direct dependencies,
retaining the finite-free-comparison approval in its original order.

## Where the brief, the DAG or earlier work was wrong

The planned seven-step reconstruction overlaps the unrestricted scalar subfamily
already stated in `CompletedLineTensorCoherence`; reusing that subfamily is shorter.
Its scalar clauses allow arbitrary schemes, independent site/coefficient universes,
unbounded derived objects and repeated coefficient fields, as the assigned statement
requires. The assigned statement itself is unchanged.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
