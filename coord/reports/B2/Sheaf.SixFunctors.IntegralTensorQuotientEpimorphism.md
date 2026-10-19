## What changed

Completed both proofs in `Sheaf.SixFunctors.IntegralTensorQuotientEpimorphism` without
changing any existing declaration signature or definition body. Naturality follows from
the pure-tensor restriction formula and preservation of one by ring restrictions.
For local surjectivity, tensor induction constructs a covering image sieve: the zero
case uses zero, the pure-tensor case lifts its coefficient along the covering image sieve
of q, and the sum case intersects covering sieves and adds preimages. Composing with the
abelian sheafification unit gives local surjectivity of the specified sheaf morphism.
The faithful underlying-abelian-sheaf functor reflects the epimorphism supplied by Mathlib.

The node proof now records that argument. Its two off-unit tool approvals are withdrawn
because the Mathlib WEqualsLocallyBijective API supplies the sheafification step directly.
The public imports are replaced with the direct upstream scalar-extension construction.
Change record: `coord/changes/B2-integral-tensor-quotient-imports.md`.

The original and reduced-import proofs compiled through lcompile.py. On resumption, the
item compiled in 5.2 seconds and its current direct consumer
`Sheaf.SixFunctors.IntegralLisseReductionEquivalence` compiled unchanged against it in
7.5 seconds. Delivery preflight performs the final axiom check.

## Proved and sorry left

Closed two of two original holes, both attached to
`lem-sfb-integral-tensor-quotient-epimorphism`:

- `SheafOfModules.integralTensorQuotientPresheafUnit_naturality`.
- `SheafOfModules.integral_tensor_quotient_epimorphism`.

No sorry remains in the item. No holes added, no intermediate statements split off,
and no new nodes. The proof uses no unproved project lemmas.

## No longer needed

Removed imports:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: only the existing Grothendieck-topology
  covering-sieve API is needed, already available through the tensor construction.
- `Sheaf.CategoryTheory.RingedSiteModules`: the extra abbreviation is unused; the
  Mathlib sheaf-of-modules category is already available through the construction.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`: neither the
  independent-universe tensor functor nor any of its auxiliary theorems is used.
  Import `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct` directly.
- `Mathlib.CategoryTheory.Sites.EpiMono`: the proof uses the locally-surjective-to-epi
  result from the already available LocallySurjective module, not the converse criterion.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the current source
  added this proof import after the earlier attempt; the sectionwise tensor proof does
  not use the cochain tensor construction.
- `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`: the current
  source added this proof import, but Mathlib supplies the sheafification step directly.

Removed proof dependencies and their top-level tool approvals:

- `lem-weil-pbc-site-sheafification-sections-local`, module
  `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`.
- `lem-pc-sites-sheafification-underlying-sets`, the Mathlib underlying-set comparison.

Both are subsumed here by `(J.W_toSheafify _).isLocallySurjective`; no separate
underlying-set comparison or choice of representatives is required. The earlier sandbox
predated the local-sections proof import now present in the current source; it is removed.
All remaining definition
nodes describe the actual site, tensor, sheafification and module-category APIs used.
This is local pruning for this proof; it does not assert those nodes are globally unused.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is mathematically correct but unnecessarily goes through set
sheafification and an auxiliary local-sections theorem. Its sectionwise coefficient
lifting can instead be formalized by tensor induction on covering image sieves, followed
by the abelian sheafification API. The module's existing WEqualsLocallyBijective
assumption supplies precisely the local-surjectivity fact required. The unit record has
no realization attached to this node; the unit's statement and route are preserved.

Read Stacks sites-modules.tex at section-tensor-product and
lemma-sheafification-presheaf-modules, and sites.tex at lemma-sections-sheafification.
Checked edge cases: zero tensor, zero module, zero target ring, identity coefficient map
and empty covering. The construction handles each without extra hypotheses. The source
statement and both conclusions are unchanged. The earlier report's zero-downstream count
is stale: downstream.py now reports 305 transitive import consumers. The sole direct consumer is
`Sheaf.SixFunctors.IntegralLisseReductionEquivalence`. It compiles unchanged against the
reduced imports. Its import of this item is proof-only, so the removed re-exports do not
propagate through its public interface; no transitive consumer adaptation is necessary.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
