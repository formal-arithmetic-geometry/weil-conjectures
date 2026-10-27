## What changed

Filled the proof of `WeilConjectures.integralQuotientCompletion_exact` without changing
its statement, its public imports, any definition, or any other existing Lean module.
Added `Sheaf.Paper.IntegralQuotientRoosHomotopy` for the native homotopy-level part of
the original argument. The existing item's proof imports that statement, the
resolving-class derived-functor API, coherent Kan shifts, the source-triangle Kan
lemma, saturation of quasi-isomorphisms, and triangulated localization.

The Lean proof constructs the resolving class from K-flat resolutions with flat
terms, proves inversion using the existing `roosGoodInverts`, derives the native
functor, and proves exactness for the particular shifts whose Kan counit is
compatible. It identifies this functor with the specified `completion` using
`completion_exists`. A proved private `kanUnit_commShift` lemma checks the unit's
shift equation by the shifted Kan universal property. Finally the normalization
on good representatives identifies the transported lift with `completionUnit`.
There is no new choice-based definition and no change of completion or its unit.

Validation: `lcompile.py --all` compiled both delivered Lean files with exit code
0 and no diagnostics: the native statement module took 4.9 seconds and the item
proof 21.1 seconds, both below the 60-second limit. The node dependency unions,
referenced node ids, and verbatim Lean signatures were also checked.

## Proved and sorry left

Original holes: 1, in `WeilConjectures.integralQuotientCompletion_exact`.
That declaration now has a complete Lean proof from the new native statement and
existing library declarations. Added holes: 1, exactly the public theorem
`WeilConjectures.integralQuotientRoos_homotopy`
(node `lem-sf-integral-quotient-roos-homotopy`). No holes remain in the item module.
This is a decomposition, with zero net holes closed, rather than an independent
proof of the original theorem. The private helper `kanUnit_commShift` is proved.

The remaining statement only descends the ordinary quotient Roos construction to
the homotopy category and proves its augmented exactness there. It has no K-flat
resolution or quasi-isomorphism inversion claim, no derived endofunctor on D(M),
and no conclusion about the specified normalized completion or its derived unit.
Thus it is strictly the native part (original proof steps 1 and the pre-derived
part of 4), not the original theorem under another name. The proof combining that
part with the resolving-class and Kan machinery is fully written in Lean.

Edge cases: the native statement uses no quasi-compactness, quasi-separatedness,
or invertibility hypothesis, since it uses ordinary additive quotient functors
and homotopies only. In particular it does not assert preservation of arbitrary
quasi-isomorphisms. The comparison uses the inverse of `quotientCompQhIso`, so its
normalization has source Q(P) and target Q(R(P)), as required. Empty schemes and
zero complexes require no extra assumption in either the native construction or
the derived descent.

## No longer needed

The item no longer directly uses `lem-pc-tensor-mapping-cone-iso`
(`WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`): cone preservation
of the ordinary quotient tower follows by the general complex extension of its
additive module functor. The native homotopy statement records that route.

The parent no longer directly uses `lem-pe-roos-cone-calculus`; it is retained as
a dependency of the new native node. It no longer separately uses
`lem-pur-derived-change-of-rings`: the required good-representative inversion is
already proved as `IntegralOnSlice.roosGoodInverts` in
`Sheaf.Paper.IntegralDerivedOperationsOnSlices`, which remains imported. None of
those upstream declarations or modules is withdrawn, and no global pruning of a
module still used elsewhere is claimed. No existing public import was removed.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The native cone calculation and the derived Kan
descent are distinct portions of the original plan. The previous plan mentioned
coherent Kan shifts and the source-triangle lemma only in its prose; the updated
proof dependencies explicitly name their already proved nodes, along with
resolving-class essential constancy and saturation of quasi-isomorphisms.

The good-representative comparison in the existing definition module already
contains the change-of-rings and Roos quasi-isomorphism argument, so repeating
that calculation in this item would duplicate proved work. Its private proved
API is used with `import all`, without changing the shared module.

## New nodes

`lem-sf-integral-quotient-roos-homotopy`, in
`dag/nodes/sec-six-functors/lem-sf-integral-quotient-roos-homotopy.json`, realizes
`WeilConjectures.integralQuotientRoos_homotopy` in the new module
`Sheaf.Paper.IntegralQuotientRoosHomotopy`. It inherits the original chapter, unit,
and blueprint ancestry. Its docstring and node give the module-valued quotient
tower construction, homotopy/cone descent, and the zero-second-coordinate unit
argument with sources. LeanSearch, LeanFinder, Loogle and local grep found the
generic homotopy and localization APIs, but no statement identifying this native
quotient tower and its specified augmentation. A current-blueprint text search
and the existing node dependencies were also checked. No change record is needed:
no existing statement or definition is modified.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
