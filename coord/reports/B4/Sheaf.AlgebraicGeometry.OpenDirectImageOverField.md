## What changed

Proved
`AlgebraicGeometry.Etale.isBoundedConstructible_rightDerivedLowerStar_primeSheaf_of_isOpenImmersion`
in `Sheaf.AlgebraicGeometry.OpenDirectImageOverField`, keeping its signature and docstring
unchanged. Added only the proof import
`WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence` for the canonical
isomorphism of derived pullback along an identity with the identity functor.

The proof follows `cor-fin-deligne-open-over-field` and its current blueprint update:
apply the stated generic-open theorem over `Spec k`; a point of its nonempty open and
subsingletonness of `Spec k` show the open is top. Present both base changes using identity
maps, with the base structure map factored through `Scheme.topIso.inv`. Apply the generic
theorem's bounded constructibility conclusion and push forward the derived identity
pullback isomorphism. Transport the same cohomological bounds, stratification, etale
covers, and finite constant module witnesses along the induced cohomology isomorphisms.
The exchange-isomorphism conclusion is unused.

The proof also covers empty X or Y and the zero sheaf: it assumes nonemptiness only of
the open of `Spec k`, supplied by the generic theorem. No object or data definition was
changed. No new declarations or nodes are needed; the existing DAG proof describes this
same specialization and transport, so its dependency record remains accurate.

Validation: the delivered module compiled through `lcompile.py` in 8.4 seconds, with
exit code 0 and no warnings. Search checked Mathlib via LeanFinder and Loogle and searched
the source library locally. The upstream Deligne module contains the analogous
specialization with a different constructibility predicate; this proof uses the assigned
generic theorem and transports finite constant values directly, without importing that
separate corollary or a comparison theorem.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Etale.isBoundedConstructible_rightDerivedLowerStar_primeSheaf_of_isOpenImmersion`
(node `cor-fin-deligne-open-over-field`).

The item's module has 0 sorries left. Added 0 holes and split off 0 statements.
The existing imported theorem
`AlgebraicGeometry.Etale.exists_nonempty_open_isBoundedConstructible_derived_open_pushforward`
(node `thm-fin-deligne-generic-open`) remains the intended proof dependency; its proof is
outside this delivery.

## No longer needed

None. No original import, node, or module was pruned. The proof uses the sole stated
proof dependency `thm-fin-deligne-generic-open`. All public imports and their visibility
are unchanged. No constructibility comparison dependency was added.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The current blueprint places the corollary in
`sec-six-functors-basics/sk-cor-geo-open-finiteness`; the existing module and node cite
its older `sec-smooth-purity/sk-prop-sf-cbc` location. The statements and specialization
argument agree, and the proof follows the node's `blueprint_update`.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
