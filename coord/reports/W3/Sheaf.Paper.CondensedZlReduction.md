## What changed

Proved `AlgebraicGeometry.ProEtale.pur_condensed_zl_reduction_mod_ell_power` in
`Sheaf.Paper.CondensedZlReduction`, retaining its exact signature and all quotient,
ring and module assertions. Added private proved helpers for continuous division,
the pointwise cokernel, normalization, inverse-image transport, linearity and tower
naturality. The normalized completed-coefficient comparison remains the unit route.
The node proof, proof dependencies and proof origin now describe this route.

The existing `purZlPointReduction` definition now chooses from a smaller, fully
proved normalized-cone existence theorem instead of choosing from the conjunction
of normalization, limits and rationalization. Its normalized components are uniquely
determined, so this retains the mathematical map while avoiding expensive kernel
unfolding of unrelated choice data. The definition has an irreducible interface with
its generated equation lemma. The new public theorem is in
`Sheaf.Paper.CondensedZlReductionCone`. No target statement changes. The consumer
check finds no external direct use of this definition; all twenty transitive import
consumers are listed in the change record, with unchanged signatures and proofs.

Private proof imports provide the proved finite constant-function comparison,
abelian-group exactness, compact p-adic topology and the embedding-to-homeomorphism
API. Local irreducibility attributes control elaboration of the existing functor
and chosen comparison data. Change record:
`coord/changes/W3-condensed-zl-reduction-cone.md`.

## Proved and sorry left

Closed the sole existing hole:
`AlgebraicGeometry.ProEtale.pur_condensed_zl_reduction_mod_ell_power`
(node `lem-pur-condensed-zl-reduction-mod-ell-power`).

Holes added: zero. Holes remaining in the delivered module: zero. The new normalized-cone theorem is also completely proved; no holes are split off. This proves the item from existing declarations;
the existing `sfb_completed_coefficients` theorem remains a dependency and is
not claimed proved here.

## No longer needed

Removed private imports `Mathlib.CategoryTheory.Sites.Limits`,
`Mathlib.CategoryTheory.Sites.LocallyBijective` and
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`.

Removed proof dependencies:

- `def-weil-pbc-algebra-hom-quotient` (still a statement dependency): use the actual
  module cokernel and transport the residue ring structure along its comparison.
- `def-weil-pbc-constant-sheaf` (still a statement dependency): the finite continuous
  comparison already identifies the specified finite constant object.
- `def-weil-pbc-sheafification`: no quotient presheaf sheafification construction.
- `lem-weil-pbc-site-sheaf-sets-limits-sectionwise`: establish a cokernel directly
  on the condensed point and preserve it under inverse image.
- `lem-weil-pbc-site-sheafification-sections-local`: continuous division and finite
  discrete lifts give an objectwise cokernel.
- `lem-weil-pbc-site-sheafification-iso-locally-bijective`: no local-bijectivity
  criterion for a quotient sheafification is used.

The obsolete top-level `tool_uses` approvals for the last three site lemmas are
removed. No module or declaration is withdrawn; these statements may still have
other consumers. The historical `split_report` is preserved.

## Where the brief, the DAG or earlier work was wrong

The planned inverse-limit/local-label proof is unnecessary below the retained
completed-coefficient comparison. On the condensed point, multiplication by a
nonzero p-adic scalar has a continuous inverse on its image by compactness.
This gives the kernel/image equality for continuous functions directly; left
adjointness then transports the cokernel to every scheme. The argument covers
exponent zero and empty profinite sets as well as all positive exponents required
by the unchanged statement. No statement was disputed or weakened, and no
source-library declaration was edited. The original reduction definition carried an
expensive choice predicate; the smaller normalized-cone interface repairs this
without changing its mathematical normalization.

## New nodes

`lem-pur-condensed-zl-normalized-reduction-cone` records the normalization-only
projection of the completed comparison. Its Lean theorem
`AlgebraicGeometry.ProEtale.pur_normalized_reduction_cone` is fully proved by
existential/conjunction elimination. It has no `sorry` and is strictly a component
of the original comparison. Edge cases include exponent zero. The extracted cone
is uniquely determined pointwise, as the item's normalization proof verifies.
Change record: `coord/changes/W3-condensed-zl-reduction-cone.md`.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
