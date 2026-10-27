## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.scheme_descent_quotient_chart_isomorphism`
with its entire original signature and all five conclusions unchanged. The proof
restricts the given kernel pair, proves injectivity using normalization, glues
sections with prescribed base coordinate, identifies the transition, and constructs
the joint etale atlas using the scheme products `T ×_S U i`.

Added two fully proved public helper modules:
`Sheaf.AlgebraicGeometry.SchemeCoproductKernelPairComponents` and
`Sheaf.AlgebraicGeometry.SchemeDescentChartSectionLifting`. Their private geometric
helpers reuse the proved arguments of `CoproductSchemePullback` for arbitrary
specified coproducts, so no index-universe restriction is added. The former works
for arbitrary presheaves; the latter only proves existence of a chart section,
assuming its uniqueness. Neither restates the assigned theorem.

The new section-lifting proof uses the existing declared theorem
`AlgebraicGeometry.AlgebraicSpace.representable_etale_fppf_local_lifting`.
Representables on the fppf over-site are sheaves by Mathlib subcanonicity, so
gluing is performed directly in `Over S`. The atlas is recovered from the chart
isomorphisms and the original cover, instead of decomposing a scheme test of V.

All three files compiled in single-file server checks, in less than 15 seconds per
file. Final delivery preflight checks compilation and declarations again.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.AlgebraicSpace.scheme_descent_quotient_chart_isomorphism`
(node `lem-trf-scheme-descent-quotient-chart-isomorphism`).

Added 0 holes; split off 0 unproved statements. Both new declarations are proved:
`AlgebraicGeometry.AlgebraicSpace.scheme_coproduct_kernel_pair_components`
(node `lem-trf-scheme-coproduct-kernel-pair-components`) and
`AlgebraicGeometry.AlgebraicSpace.scheme_descent_chart_section_lifting`
(node `lem-trf-scheme-descent-chart-section-lifting`).

No `sorry` remains in any file of this delivery. The existing imported local-lifting
theorem remains an upstream proof dependency; this delivery does not claim to close
that theorem or the project's targets.

## No longer needed

Removed the item's private imports of
`Sheaf.AlgebraicGeometry.RepresentableEtaleFppfLocalLifting` (now used by the new
section-lifting module), `Mathlib.AlgebraicGeometry.OpenImmersion`,
`Mathlib.AlgebraicGeometry.Morphisms.Etale`,
`Mathlib.AlgebraicGeometry.Sites.Fpqc`, and
`Sheaf.CategoryTheory.SiteCoveringAxioms`. All existing public imports are preserved.
The actual remaining proof imports provide the two helpers, scheme-pullback points,
Yoneda product comparison, and the Type-valued pullback API.

The route no longer needs separate applications of
`lem-trf-fppf-covering-is-fpqc` or
`lem-weil-pbc-fpqc-representable-descent`: the already proved Mathlib fppf
subcanonicity instance directly gives the needed gluing in the slice category.
These nodes are removed from the item's proof dependencies. No module is withdrawn.
The general local-lifting and site-sheaf-condition tools, coproduct geometry,
open immersions, and etale composition remain needed in the new lifting lemma;
they are transferred to its node rather than claimed pruned.

Removed the item's direct `tool_uses` entries for
`lem-a1-representable-etale-fppf-local-lifting` and
`def-weil-pbc-sites-and-cohomology`: these are used in the new lifting module,
not directly by the item's proof. The given cocycle hypothesis is unnecessary
once the full presentation kernel-pair square is assumed; its binder is retained unchanged, with
the unused-variable linter suppressed only for this declaration.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or mathematical error was found. The original plan's final
coproduct-atlas argument is unnecessary after chart recovery: base change of the
original etale cover supplies the required indexed representing schemes directly.
The original fpqc gluing route can be shortened to the proved subcanonical fppf
site on `Over S`, which also handles the S-morphism condition directly.

Checked the current blueprint unit and its `realized` record. The assigned node
is an auxiliary descendant with no unit-step attachment; this argument changes
only its internal proof route. Empty tests, empty summands and arbitrary index
universes are covered by the proofs; empty I is compatible with the assumed cover
only for an empty base. The shared tree and all existing dependency files remain
untouched.

## New nodes

`lem-trf-scheme-coproduct-kernel-pair-components`: a proved presheaf pullback
restriction theorem for two specified scheme coproducts. Its proof gives the
pointwise factorization through the unique disjoint open component and uniqueness.

`lem-trf-scheme-descent-chart-section-lifting`: a proved existence theorem for
sections with prescribed quotient and base coordinates, assuming injectivity.
It constructs local lifts on the pulled-back coproduct cover, transports them
through the overlap isomorphism, and glues them with the sheaf condition.

Both nodes inherit the assigned chapter and unit, record sources and Mathlib
searches, and have exact Lean attachments. No change record is required: no
existing statement, definition, public import, or other module is modified.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
