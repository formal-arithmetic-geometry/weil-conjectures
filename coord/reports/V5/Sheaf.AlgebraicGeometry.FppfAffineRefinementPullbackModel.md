## What changed

Proved `AlgebraicGeometry.exists_fppf_affine_refinement_pullback_model` in
`Sheaf.AlgebraicGeometry.FppfAffineRefinementPullbackModel`, with its public statement
unchanged. A fully proved private helper constructs the datum on the specified
Cartesian square over the changed base and verifies all three transport laws.

The proof base changes the fppf family, applies the existing finite affine refinement,
and constructs its coproduct map. Mathlib supplies flatness, local finite presentation,
affineness, quasi-compactness and quasi-separatedness; joint coverage proves surjectivity.
The singleton satisfies the actual qc-cover and flat-cover conditions defining fpqc.
The canonical pullback theorem supplies the final datum.

For the local model, use the component Cartesian-square clause of the existing
`fppf_family_coproduct_descent_encoding`, transported to the supplied colimit cofans.
Pasting and cancellation give each local pullback square. Universality of finite
scheme coproducts assembles them; uniqueness of pullbacks gives the isomorphism
and its exact projection equation over C. The source places read were Stacks
Descent, lemma-family-is-one, lemma-pullback (1), and
lemma-descending-types-morphisms; Topologies, lemma-fppf-affine.

Added the private proof import
`Sheaf.AlgebraicGeometry.FppfFamilyCoproductDescentEncoding`. The import-direction
check and a traversal of all statement/proof/proof-step dependencies found no cycle.
The DAG proof now records this route. No definition or statement changed; no consumer
adaptation or change record is needed. The unit's realized statement and steps are
unchanged. The construction permits empty bases, Fin 0, empty summands and repeated
indices throughout. Single-file server compilation completed without warnings in 15.3 seconds;
the public theorem statement was also checked byte-for-byte against the original.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_fppf_affine_refinement_pullback_model`
(node `lem-trf-fppf-affine-refinement-pullback-model`): 1 of 1 original holes.
Added holes: none. Remaining holes in delivered Lean files: none.
The private theorem `pullback_datum_over_base` is completely proved.

The proof uses the existing, still-stated theorems
`AlgebraicGeometry.Scheme.exists_finite_fppf_affine_open_refinement`
(`lem-pc-fppf-affine-refinement`) and
`AlgebraicGeometry.fppf_family_coproduct_descent_encoding`
(`lem-trf-fppf-family-coproduct-descent-encoding`); their existing holes are unchanged
and are not new split-offs in this delivery.

## No longer needed

Removed the direct private import `Mathlib.AlgebraicGeometry.Gluing`.
The revised local comparison does not directly use
`lem-weil-pbc-open-immersion-base-change` or
`lem-weil-pbc-scheme-morphism-gluing`; these are removed from this node's direct
proof dependencies. They remain dependencies of the imported family-encoding theorem,
so this delivery does not claim to prune their modules from the target closure.
All other declared geometric dependencies are retained. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The plan's explicit disjoint-open gluing argument can be replaced by the existing
family-encoding component-square statement and universality of finite coproducts
(the existing Mathlib leaf
`lem-sc-etale-fibre-product-base-change-coproduct`).
The base-change datum can be constructed directly on the supplied pullback square,
which also avoids any identification between that square and the chosen pullback.
The hypothesis `hD` is unnecessary for the conclusion: the geometric local model
depends only on the componentwise structure map q, and the transport construction
works for any D. Its binder and the entire public statement are preserved.

## Second reading by V5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
