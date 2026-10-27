## What changed

Proved `WeilConjectures.PurStrictScalar.scalar_refinement_origins_E` without
changing its statement or any target. At each level, use the actual finite
coefficient reduction and its bounded constructible homology. The existing
proved `ProEtale.fixedDerivedOrigin` helper supplies its bounded etale origin.
Realize that origin in the finite function-coefficient category and transport
it through the specified quotient scalar map. The final isomorphism uses the
calculus's reduction evaluation and the strict tower evaluation comparison.

Three private proved scalar comparisons and an explicit lifted quotient ring
homomorphism bridge the completed-sheaf and fixed-scalar presentations. In
particular, the constant-to-completion map followed by a finite projection is
the constant quotient map by the limit cone equation. Sheafification-unit
naturality gives its action on constant sections; existing normalized scalar
comparison helpers then give the derived isomorphisms.

Added proof-only `import all` access to already proved helpers in
`FiniteConstantCoefficientTransport` and `ProEtaleConstructibleOrigin`. Updated
only the item's node's proof, proof dependencies and proof origin. The public
import removal and its consumer check are recorded in
`coord/changes/A2-scalar-refinement-origins-E.md`.

LeanFinder and Loogle searches found no direct Mathlib theorem for this
specialized witness. Repository search found the existing fixed-scalar origin
helper, avoiding both new intermediate obligations and the large compact
support coefficient-model theorem.

## Proved and sorry left

Closed the one existing hole:
`WeilConjectures.PurStrictScalar.scalar_refinement_origins_E`
(node `lem-pur-compact-support-strict-scalar-refinement-origins-e`).

One of one holes closed; zero holes left in the item; zero holes added; zero
split-off statements. Every new private helper is fully proved. This is a proof,
not a decomposition into new obligations.

Validation: `lcompile.py` compiled the item and the unchanged direct importer
`Sheaf.Paper.CompactSupportStrictScalarRefinement` together, with exit code zero
and no warnings. The temporary importer copy was removed after this check.
The import-direction check found no cycle; the theorem signature is unchanged,
all Lean lines meet the 100-character limit, and the node proof dependencies
are exactly the union of its proof-step uses.

## No longer needed

Removed the unused public import
`Sheaf.Paper.CompactSupportScalarLimitReduction`. The direct importer already
imports that module explicitly. No module is withdrawn.

The proof does not use the planned proof dependency
`lem-pur-compact-support-coefficient-models`
(`Sheaf.Paper.CompactSupportCoefficientModels`): finite-level constructibility
is already a component of the hypothesis, and the origin helper applies
directly. Removed that proof dependency from this item's proof route; retained
the original statement dependencies. The Tor bound and derived completeness
components need no proof here, though their hypotheses and the geometric
hypotheses remain unchanged. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The node's source path says `more-etale.tex`, but Stacks Tags 09AK and 09AL are
in `literature/stacks-project/proetale.tex`, specifically the constructible
comparison and derived constructible comparison lemmas. The updated proof
origin records the correct location; no mathematical statement is disputed.
The original one-sentence proof plan suppressed the comparison between the
completed coefficient sheaf and its fixed constant scalars. The private
scalar-unit calculation supplies that comparison explicitly.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
