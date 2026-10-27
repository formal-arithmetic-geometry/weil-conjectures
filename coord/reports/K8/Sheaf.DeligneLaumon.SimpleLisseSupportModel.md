## What changed

Kept the statement of `AlgebraicGeometry.WeilSheaf.exists_simple_lisse_support_model`
verbatim. Its proof now combines two independent steps: geometric selection of the
clopen connected support over its field of constants, and native Frobenius-return
restriction on that supplied support. The two unfinished steps are separate new
modules, with their own statements, source proofs and DAG nodes.

The remaining construction is written in Lean: replace the support in every
relative dimension d by its relative affine line of dimension 1+d, compose the
return functor with exact pullback, lift both points by the zero section, and
compose the actual pointwise Frobenius-module equivalences. Private helpers prove
pointwise power transport for ordinary pullback and its compatibility with
composition.

`AffineLinePullbackIrreducible` proves arithmetic lisse simplicity under affine-line
pullback. It uses the zero section, exactness, the lisse cokernel theorem, and
vanishing detected by one stalk on an irreducible geometric fiber. It adds no
hole. The geometric construction is a fully proved private existence lemma, which
constructs Mathlib's actual affine space and zero section. The native category
argument receives its scheme and maps through that interface, avoiding expansion
of the large Scheme pullback representation inside native functor objects.
Pullback isomorphisms are composed at the functor level and evaluated only in
the generic retraction lemma. No data is selected from an unproved geometry
construction. No existing
declaration signature, definition body, public import, source-library body, or
target was changed. The unit route is preserved.

Validation: all four delivery modules compiled together. The affine-line API
compiled in 6.7 seconds and the main item in 55.9 seconds, under the per-file
limit. Temporary probes and all profiling options were removed. The final
narrower imports are checked again by the delivery command.

## Proved and sorry left

Original module: one hole closed, in
`AlgebraicGeometry.WeilSheaf.exists_simple_lisse_support_model`; no holes remain
in that module. This is a decomposition, not an axiom-free completion: two holes
are added, for a net increase of one syntactic hole.

- `AlgebraicGeometry.WeilSheaf.exists_geometrically_connected_clopen_support`
  (`lem-zl-geometrically-connected-clopen-support`): geometry only, allowing dimension
  zero, with no return functor or preservation of simplicity.
- `AlgebraicGeometry.WeilSheaf.exists_clopen_return_restriction`
  (`lem-zl-clopen-return-restriction`): categorical return on a supplied clopen
  immersion, with no construction of a support scheme or positive dimension.

Fully proved new public theorem:
`AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse.exists_affineLine_model`
(`lem-zl-affine-line-pullback-irreducible`). Its private stalk-vanishing, categorical
retraction, general-section, geometric-construction and isomorphism API helpers, and all four private
degree/transport/powering helpers in the item are proved without
`sorry`. Total delivery holes: two, both whole named public theorem bodies.

## No longer needed

The item's proof no longer needs `lem-zl-point-weil-heart-flag` or
`Sheaf.Paper.PointWeilHeartFlag`. The dimension-zero eigenline classification is
replaced by a proved zero-section argument which works in every dimension.
This is a dependency removal for this item; no claim is made that the module
has no other users. In fact, the unit's first realized step still lists the
point-flag node; that route and its consumers are retained. No module is withdrawn
or claimed globally pruned.

`lem-zl-affine-geometric-components-finite-extension` is now a dependency of the
geometric support step, rather than a direct dependency of the item. It is not
pruned. The source local-Frobenius and constant-field-restriction definitions
remain needed. No original Lean import was removed: the original three public
imports are necessary for the unchanged statement. All new proof imports are
private. The geometric support statement imports the native stalk API directly;
it needs no constant-field restriction definitions. The affine-line module
publicly exposes the native category and its geometric hypotheses; affine space
and the lisse-filtration API are private proof imports.

## Where the brief, the DAG or earlier work was wrong

The declared component-descent theorem supplies geometry after a constant
extension but not the native source-category return functor or its simplicity
property. The existing point-flag and sheet-coordinate statements use the
common-stage paper interfaces; the item's statement uses native constructible
pro-etale Weil sheaves. They do not directly discharge the missing native return
construction. The two new statements isolate precisely the geometric and native
categorical work, rather than renaming the whole support-model obligation.

The dimension-zero flag argument is unnecessary: pullback along a relative affine
line preserves arithmetic lisse simplicity by a section and stalk detection. No
claim that all affine-line local systems are constant is used.

Edge cases checked: nonzero marked stalks exclude empty support; dimension zero
is allowed in the geometric step and becomes one in the final construction;
a degree-one constant extension reduces to ordinary clopen restriction. A proper
clopen component may carry a zero restriction of another simple sheaf, so the
return theorem explicitly requires a nonzero stalk on that component. The local
transport for that clopen immersion has exponent one because its residue fields
are identical. The final affine-line pullback uses the relative residue degree.

## New nodes

`lem-zl-geometrically-connected-clopen-support`, module
`Sheaf.DeligneLaumon.GeometricallyConnectedClopenSupport`: isolate the geometry
of the support and its field of constants, without a categorical conclusion.

`lem-zl-clopen-return-restriction`, module
`Sheaf.DeligneLaumon.ClopenReturnRestriction`: isolate native return restriction,
exactness, all-object local power transport and arithmetic simplicity on a
specified support. Its nonzero-stalk hypothesis prevents a false simplicity
assertion for the zero restriction.

`lem-zl-affine-line-pullback-irreducible`, module
`Sheaf.DeligneLaumon.AffineLinePullbackIrreducible`: a complete proof constructing a
relative-dimension-one model and proving its preservation of simplicity. The existing support-model node's proof and
proof dependencies follow the new Lean construction. No change record is
required because existing statements and definitions are unchanged.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
