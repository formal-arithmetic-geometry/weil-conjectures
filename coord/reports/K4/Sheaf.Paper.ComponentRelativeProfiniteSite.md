## What changed

Proved `AlgebraicGeometry.ProEtale.component_relative_profinite_site` from the existing
`Scheme.ProEt.affine_component_site_projection`, Mathlib, and three proved auxiliary results.
The statement and all five existing definitions are unchanged. The proof constructs the mapping
property, finite-stage isomorphisms, relative presentations, scheme limit cones, finite
coproduct preservation, covering preservation, and the specified inverse-image factorization.

The mapping property works for every scheme over T. The finite-stage proof uses the actual
restricted clopen subschemes, including repeated blocks and empty stages. The relative
presentation allows empty source and base. The final comparison uses the exact absolute
inverse-image functor appearing in the statement and Mathlib's slice adjunction.

All four delivered modules compile through `lcompile.py`, without holes or warnings;
the final main-module check took 4.8 seconds. Text comparisons confirm the main signature,
all five existing definition bodies, and all public imports are unchanged.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.component_relative_profinite_site` (one of one).
Added zero holes. No `sorry` remains in the delivered modules.

Also proved:

- `AlgebraicGeometry.Scheme.existsUnique_lift_of_stalkMap_isIso`;
- `Profinite.exists_relative_finite_presentation`;
- `Profinite.functor_iso_of_finite`.

The existing dependency `Scheme.ProEt.affine_component_site_projection` is used as stated;
its proof is outside this item. No theorem was replaced by a renamed equivalent hole.

## No longer needed

Removed these private imports:

- `Sheaf.Topology.FiniteQuotientFiberProduct`;
- `Sheaf.CategoryTheory.Sites.SliceSubtoposSitePresentation`;
- `Sheaf.RingTheory.IndEtaleStability`;
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`;
- `Mathlib.Topology.LocalAtTarget` (introduced during this work and then removed).

Also removed redundant private imports already exposed by retained public imports:
`Mathlib.AlgebraicGeometry.Limits`, `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`, and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`. The new relative-presentation
module also drops an unused `Mathlib.Topology.Category.Profinite.CofilteredLimit` import.

The proof no longer directly needs these planned nodes:

- `lem-sfb-finite-quotient-fiber-product`: use canonical Mathlib finite-quotient limits;
- `lem-trf-slice-subtopos-site-presentation`: use `Over.forgetAdjStar` on sheaves;
- `lem-weil-pbc-ind-etale-stability`: the component projection already supplies ProEt objects;
- `lem-weil-pbc-morphism-affine-schemes-affine`: the required scheme limit is proved directly;
- `lem-weil-pbc-affine-scheme-qcqs` and `lem-weil-pbc-qcqs-scheme-spectral`: the unchanged
  component-space definition uses the Mathlib affine spectral instance.

Updated only `proof`, `proof_deps`, and `proof_origin` in the item node.
These are local dependency removals; no module or declaration is withdrawn.
In particular,
`IndEtaleStability` remains a dependency of the reused affine component-site projection.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was necessary. The planned proof via affine tests
and gluing is longer than needed: the profinite-to-topological-space inclusion is a right
adjoint, also after passing to slices. Its limit property and the continuous mapping
property directly give the scheme limit for arbitrary cone sources.

The planned slice-site theorem is unnecessary because Mathlib already supplies the precise
slice adjunction. The source-library declarations and public imports are untouched.

## New nodes

`new-lem-zl-stalk-isomorphism-lifting`: the general, proved lifting property for a scheme
morphism inducing isomorphisms on every stalk. It is proved by inverse-image adjunction,
stalk comparison, sheafification, and the locality of the resulting stalk maps.

`new-lem-zl-relative-finite-profinite-presentation`: the proved presentation of a profinite
space over a profinite base using compatible finite clopen partitions. Mathlib's absolute
finite-quotient limit proves its universal property.

`new-lem-zl-profinite-functor-extension`: the proved extension of a natural isomorphism on
finite tests when both functors preserve the canonical finite-quotient limits. It follows
by transporting cones and uniqueness of limits.

All three nodes are in `dag/nodes/sec-zeta-weil/`, attached to new modules under `Sheaf/`.
They have recorded Mathlib searches and the same blueprint ancestry as the item.
`coord/changes/K4-component-relative-profinite-proof.md` records the module-level
elaboration options, private helpers, and the new public proved results. No existing
statement, definition, signature, or visibility changed. The first preflight required this
record for its command-level interface check; compilation passed. The second preflight
required its five template headings, now supplied with the complete downstream-user table.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
