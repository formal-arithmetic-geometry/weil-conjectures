## What changed

Replaced the sole sorry of `Sheaf.Paper.EtaleWeilSheafEquivalence` by a complete
Lean assembly of the prescribed realization, full faithfulness, essential
surjectivity, abelian transfer, finite-limit/colimit preservation in both
directions, and the actual tensor predicate. The theorem signature is unchanged.
Its fibre identifications are identity linear equivalences; its action identity
is reflexive, and its arrow identity is the proved normalized stalk-map formula.

The forward functor explicitly sends each Weil sheaf to `Rep.of` its recorded
fundamental representation. Membership uses `etaleFundamentalRep_isLAdic`.
Its arrow map is the unique intertwiner specified by its actual stalk map.
The Hom equivalence proves identity, composition and full faithfulness.
`etaleWeilAbelian` is proved using the small fundamental-group existence theorem,
the existing adic Galois dictionary, inverse automorphism pullback, and
`IsoAlgebra.abelian`. Mathlib supplies the remaining abelian transfer and the
four preservation instances.

Moved `etaleLisseWeilRepresentations` and `etaleWeilTensorCompatibility` verbatim
into `EtaleWeilRepresentationData`, publicly reexported by the original module,
to let the independent supporting statements avoid an import cycle.
All original public imports are retained in the item; the new interface imports only
its fundamental-representation and representation-category dependencies. No source-library module is edited.
The change record is
`coord/changes/P6-etale-weil-representation-interface.md`.

The complete proposed theorem and all eight delivery modules compile through
lcompile.py. Supporting statements retain the finite/integral/rational dictionary,
Frobenius descent, exactness and tensor stages of unit `sk-i-real-sheaves`.

## Proved and sorry left

Original holes: 1. Closed in the item:
`AlgebraicGeometry.Scheme.etaleWeilSheafRepresentationEquivalence`.
No sorry remains in the item module. This is a decomposition, not a net proof:
four genuine supporting results remain admitted in four new modules.
Net textual holes for this packet: 1 closed, 4 added (net -3).

New sorries, each with its source and a complete proof in words:

- `AlgebraicGeometry.Scheme.etaleWeilFiberHom`
  (`new-p6-etale-weil-fiber-hom`): only the normalized Hom dictionary.
- `AlgebraicGeometry.Scheme.etaleWeilReconstruction`
  (`new-p6-etale-weil-reconstruction`): only essential surjectivity.
- `AlgebraicGeometry.Scheme.lisseAlgebraicAutomorphismPullback_isEquivalence`
  (`new-p6-lisse-automorphism-equivalence`): only inverse reindexing after
  coefficient localization, independent of Weil objects or the point.
- `AlgebraicGeometry.Scheme.etaleWeilTensor`
  (`new-p6-etale-weil-tensor`): only actual tensor compatibility for the fixed
  realization, assuming the supplied equivalence.

Proved without additional holes in their modules:
`etaleWeilRealization`, `etaleWeilRealization_map`,
`etaleWeilRealization_fullyFaithful`, and `etaleWeilAbelian`.
Their imported hypotheses include the four new sorries and the existing named
Galois/fundamental-representation statements; this is not an assertion that
these declarations are already free of sorryAx transitively.

The Hom witness used by `etaleWeilHomEquiv` is uniquely determined: each of its
values has the stated underlying linear map, an intertwiner is determined by
that map, and an equivalence is determined by its forward function.
There is no arbitrary object chosen from an unproved existence theorem.

## No longer needed

Removed unused direct proof imports from the item:
`WeilConjectures.RepresentationTheory.FiniteDimensionalRealization`,
`WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup`,
`WeilConjectures.WeilSheaf.Tensor`.
The pro-etale source equivalence is not used as an etale equivalence.
None of these upstream modules or declarations is withdrawn or changed.

The old node's separate base-change/Noetherian prerequisite deductions are not
needed directly: connectedness, Noetherianness, separatedness and invertibility
are already hypotheses of the unchanged Lean theorem. Its new proof_deps
record the actual assembly. The finite-coefficient dictionary, path transport,
degree extension, coefficient categories and l-adic representation definitions
remain needed by the supporting lemmas and are not claimed as pruned.
No entire existing module is withdrawn. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The declared modules provide the underlying Galois dictionary and the
fundamental actions, but do not state the normalized Weil Hom dictionary,
reconstruction, inverse algebraic pullback or tensor compatibility as Lean
lemmas. These are genuine parts of the expanded proof, now isolated with
precise signatures. The existing source equivalence has pro-etale objects and
cannot identify the actual etale category in this theorem by a direct application.
No false statement was found. Edge checks include zero representations,
noninvertible morphisms, arbitrary invertible degree-one operators with no
stable integral lattice, and the empty scheme for inverse pullback.
The compile server intermittently returned exit 124 (busy); successful retries
established the stated compilation results.

## New nodes

`new-p6-etale-weil-representation-data` attaches the two verbatim relocated
interface definitions in `EtaleWeilRepresentationData`.

`new-p6-etale-weil-fiber-hom` states the normalized intertwiner dictionary;
its forward linear map is fixed on every morphism.

`new-p6-etale-weil-realization` attaches the explicit forward functor, its map
formula, the uniquely specified Hom equivalence and the proved fully faithful
structure in `EtaleWeilRealization`.

`new-p6-etale-weil-reconstruction` states the essential-surjectivity part of
the Frobenius-descent argument in `EtaleWeilReconstruction`.

`new-p6-lisse-automorphism-equivalence` isolates inverse reindexing through
all coefficient stages in `LisseAutomorphismEquivalence`.

`new-p6-etale-weil-abelian` attaches the proved source abelian structure in
`EtaleWeilAbelian`, using the Galois dictionary and inverse pullback.

`new-p6-etale-weil-tensor` states the tensor part for the exact prescribed
realization in `EtaleWeilTensor`.

Change record: `coord/changes/P6-etale-weil-representation-interface.md`.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
