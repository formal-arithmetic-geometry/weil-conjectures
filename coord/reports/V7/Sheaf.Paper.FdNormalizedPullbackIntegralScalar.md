## What changed

Replaced the hole in `WeilConjectures.fdNormalizedPullbackIntegralScalar` by the
existing `fdScalarRoosIntegralIntertwining` completion-conjugated equation,
explicit inverse cancellation, and transport across equality of the two actual
completed coefficient maps. The main theorem's signature and public imports
are unchanged. The coefficient-map equality is proved locally by finite
quotient projection uniqueness, following the existing private proof in
`PbcFiniteRawScalarComparison`; no arbitrary scalar comparison is substituted.
A general private categorical cancellation lemma and a private transport lemma
prove the final inverse-b equation and preserve the HEq to the actual PBC alpha.

Validation: remote single-file compilation passed for the main module (9.8 s),
`FdPullbackRoosMatchingUniqueness` (42.1 s), and
`FdCoefficientScalarCompletionIdentification` (35.2 s).

Two separate normalization identifications are stated in new modules. The first
has one coefficient field and no scalar inclusion: a matched selected ambient
component equals the inverse common-tower component. The second has one scheme
and no scheme pullback: a fixed coefficient scalar component equals ordinary
coefficient transport inverse followed by completion. Each is strictly a part
of the original argument, and neither asserts a scalar/pullback square or
constructs the original witness.

## Proved and sorry left

Closed the original hole in `WeilConjectures.fdNormalizedPullbackIntegralScalar`
(`lem-fd-normalized-pullback-integral-scalar`) by a reduction to existing
intertwining and the two new normalization lemmas. The assigned module has zero
remaining holes, from an original count of one.

Added two holes, each the entire proof `:= by sorry`:

- `WeilConjectures.fdPullbackRoosMatching_uniqueness`
  (`lem-fd-pullback-roos-matching-uniqueness`).
- `WeilConjectures.fdCoefficientScalar_completionIdentification`
  (`lem-fd-coefficient-scalar-completion-identification`).

This is a decomposition: one upper hole closed and two lower holes added,
net minus one. It is not a claim that the integral scalar theorem is sorry-free.
The inverse cancellation, completed coefficient-map equality, witness transport,
and combination with the existing integral intertwining theorem are proved in Lean.
No hole is put in a definition or private helper.

## No longer needed

No original public import is removed, and no whole module is claimed pruned.
The proof does not use the rational clause
`fdScalarRoosComparisonIntertwining`: it uses the integral clause
`fdScalarRoosIntegralIntertwining` of that same module directly. It uses neither
the rational mixed field nor the common-stage pair descent of `FdPullbackSystem`.
These declarations remain in place.

The augmentation/counit matching existence theorem is not invoked to choose new
finite components. Its matching predicate remains in the unchanged statement;
the needed identification of the already supplied finite components belongs to
the new uniqueness node. All four original mathematical dependencies remain
needed, directly or below these two identification steps.

## Where the brief, the DAG or earlier work was wrong

The existing scalar intertwining theorem has the desired square for common
strict-tower models, but its independently supplied common-model components
are not definitionally the selected finite components. Likewise, the chi
normalization in `FdCoefficientComparison` is a representative equation; it is
not already a theorem identifying its scalar component with the transported
completion isomorphism on every constructible object. The two new statements
isolate exactly those identifications. They do not restate the original square.

The ambient scalar functor and embedding scalar functor use separately chosen
completed coefficient maps. Treating their functors as definitionally equal
would lose the transport required in the original HEq clauses. The local
projection-uniqueness proof and equality-elimination lemma handle this explicitly.

The current blueprint trace definition is under `sk-cor-plancherel` and contains
the trace formula, not this auxiliary whole-tower proof. The new sources therefore
identify the auxiliary argument recorded in the assigned node and supporting
Stacks 0941 and 099N precisely. No claim is attributed verbatim to that current
trace-definition text. The unit route is unchanged.

## New nodes

`lem-fd-pullback-roos-matching-uniqueness`, in
`Sheaf.Paper.FdPullbackRoosMatchingUniqueness`, identifies matched fixed finite
ambient components with common-model inverses. Its proof in words compares
entire normalized quotient towers and their completion augmentations before
cancelling the invertible realization maps. It has no scalar inclusion.

`lem-fd-coefficient-scalar-completion-identification`, in
`Sheaf.Paper.FdCoefficientScalarCompletionIdentification`, identifies a fixed
coefficient scalar component with normalized ordinary transport and completion.
Its proof in words uses tensor generators, retained derived counits, the chi
representative equation, and localization. It has no scheme pullback.

Both nodes carry their exact Lean signature, source, proof in words and searches
with LeanSearch, LeanFinder, Loogle and library grep. Equal fields, ramified
extensions, identity schemes and zero objects introduce no extra hypotheses;
no finite quotient transition is inverted. No change record is required because
no existing interface, definition, attribute or public import changes.

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
