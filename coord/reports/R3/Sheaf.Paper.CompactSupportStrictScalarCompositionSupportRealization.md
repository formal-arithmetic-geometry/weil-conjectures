## What changed

Replaced the hole in `WeilConjectures.PurStrictScalar.supportRealization_coherence`
by an explicit categorical pasting proof, preserving its statement. The private
`support_pasting` lemma performs comparison naturality, selection naturality,
F-model cancellation, retained-level reassociation, and L-model naturality.

Added three modules, each with one public component statement:
`ScalarReductionBalancingComposition`, `StrictScalarComparisonSelection`, and
`StrictImageReindexComposition`. The first two isolate coefficient balancing and
selection compatibility of the scalar mate. The third proves nested selection
through proper/open image using the public canonical derived normalization, normalization-naturality and
exact-square composition theorems. A private generic normalization lemma prevents
repeated kernel expansion of the concrete proper-image comparison. Only the assigned existing module and its node
are changed; all other Lean files and nodes are new.

Validation: all four files compile through `lcompile.py` in import order. The final
parent compile is clean at 11.8 s; the nested-image proof is clean at 28.3 s.
The existing theorem signature is preserved verbatim, and each new Lean signature
matches its node. The legacy geometry parameters remain; their unused-section
warning is suppressed locally to preserve the declaration.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PurStrictScalar.supportRealization_coherence` by decomposition.
This is not a claim that the entire theorem is now independent of `sorry`.

Proved the new `WeilConjectures.PurStrictScalar.reindexImage_composition`, node
`lem-pur-strict-image-reindex-composition`, with no new hole. Its proper and open
components use the actual published comparison maps, not arbitrary isomorphisms.

Added two holes, each the entire proof of a named public theorem:

- `WeilConjectures.PurStrictScalar.reductionBalancing_composition`, node
  `lem-pur-scalar-reduction-balancing-composition`. This has no geometry, image,
  support model or inverse limit: it is the coefficient-only composition law.
- `WeilConjectures.PurStrictScalar.comparison_selection`, node
  `lem-pur-strict-scalar-comparison-selection`. This concerns two coefficient
  fields, one positive index and an arbitrary tower. It has no reduction calculus,
  ramification or support model, and no three-field associator.

Thus one original hole is replaced by two strictly smaller holes. The actual
remaining hole count in the four delivered modules is two; the assigned module
has zero. This is a decomposition, with one hole closed and two holes added,
not a net reduction in holes. Neither new hole is equivalent to the assigned support equation by
cancelling an isomorphism: the assembly uses both distinct compatibility laws,
the separately proved reindex law, and several naturality equations.

## No longer needed

No original import is removed. The public Prelude import remains necessary for
the unchanged statement. No existing module can be withdrawn. The original two
proof dependencies are now accessed through the three component nodes; they
remain needed for their definitions and component arguments. Pruned: none.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition defect was found. The original single proof
step combined three independent coherence calculations. The new nodes make
those calculations explicit and the parent now records their actual assembly.
The derived retained-level comparison cannot simply be treated as an identity:
its canonical compositor must be retained, including the inverse orientation.

The new statements include the zero tower and empty schemes, and require neither
nonzero objects nor a nonempty site. Positive indices include e=1 and h=1;
the index equation still uses the canonical identity-selection comparison.
Coefficient embeddings may be identities. Index zero is correctly excluded from
the selection and ramification-composition statements. The source unit route
and every target statement are preserved.

## New nodes

`lem-pur-scalar-reduction-balancing-composition` records the pure-tensor
normalization and derived counit uniqueness argument for composing reduction
balancings. The statement is before support realization, and its proof docstring
specifies both the tensor formula and the retained index equality.

`lem-pur-strict-scalar-comparison-selection` records the termwise ordinary
selection cube, its canonical derivation and scalar-adjunction mate, and the
proper/open pasting giving compatibility with arithmetic restriction.

`lem-pur-strict-image-reindex-composition` records the proved proper-normalization,
exact-open-square and image-pasting calculation. Its generic normalization-pasting
calculation is proved privately here from the public normalization-naturality
theorem and exact restriction factorization formulas; it imports no private
lemma from another module. It uses the closed generic
exact-square composition theorem as a categorical tool; no Poincare-duality
argument or alternate unit route is involved. No shared-definition change record
is needed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CompactSupportStrictScalarCompositionSupportRealization": "7cbecc2d677dd79b612e66ab13b073d1f8585d0d", "Sheaf.Paper.ScalarReductionBalancingComposition": "0601631caad2d887f5e3bdfee4722ded77f747b7", "Sheaf.Paper.StrictImageReindexComposition": "22cf546886cea2d6814cd99b84bd40aab86d1945", "Sheaf.Paper.StrictScalarComparisonSelection": "29467ace57ae669ff158dda6e06b73c9d8e20c7b"}, "results": {"Sheaf.Paper.CompactSupportStrictScalarComposition": {"hash": "1141ee9253de498885d9849812bc4e6ab652a274", "status": "OK"}}, "seconds": 127, "time": "2026-10-28T08:15:34+0800", "transitive": 0, "version": 1}
```

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
