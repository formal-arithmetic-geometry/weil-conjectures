## What changed

`Sheaf.Paper.CompletedHomScalarTranspose.completed_hom_scalar_transpose` now combines an
ordinary chain-map construction with its derived normalization. These are isolated in
`Sheaf.Paper.PointScalarHomCochainPairing` and
`Sheaf.Paper.PointScalarHomDerivedNormalization`, respectively. Both are private proof imports
of the item; the original public imports, signatures and definitions are unchanged.

The item constructs signed uncurrying using the existing totalTensor functor and the
proved cochain evaluation in PointSheafHomMaps. A general tensor-map formula for an
arbitrary codomain complex follows from mapBifunctorMap's summand equation and module
tensor naturality. Specializing it to the Hom complex gives the signed evaluation formula,
including negative degrees. A separate private
lemma proves CompletionSquare for every cochain map: naturality, the quotient-coordinate
normalization and the zero shifted-coordinate normalization suffice. These clauses are
proved directly for both gamma and the evaluation map, rather than left in either split.

The parent DAG proof now follows this assembly. Its unit route is retained.
Local irreducibility keeps the fixed model constructions and the result predicates from
being expanded during unrelated elaboration; their public definitions are unchanged.
In particular the underlying completed ring sheaf stays opaque locally, while its
commutative wrapper can reduce to that same ring sheaf. This prevents inverse-limit data
from being unfolded merely to compare the two module presentations.
The completion normalization is exposed before the transparency boundary; only the
witness-based tensor naturality step explicitly unfolds the ordinary scalar model.
The private counit equations respect transparency during elaboration, and the square
proof uses its typed congruence expressions directly. A proved private tensor-naturality
facade is reused by both square and coefficient-unit proofs.
All three modules have typechecked through lcompile.py. The delivery tool recompiles
all three modules and enforces the single-file time limit and preflight checks.
Within the square proof, the Roos transition endomorphism, its induced map and the scalar
transitions remain locally irreducible. Within the signed evaluation proof, the sheaf
tensor construction stays locally irreducible and the proof uses explicit tensor laws.
A local priority selects integralTowerHasDerivedCategory consistently throughout the file.
Its body is the same standard localization as the generic derived-category wrapper; this
only controls instance selection within the file.
The original derived-transport calculation is retained; its final uniqueness clause now
cancels the comparison isomorphism directly, avoiding composition with its inverse.
The ordinary tensor naturality steps use the source library's proved
integralOrdinaryScalar_obj and integralOrdinaryScalar_map API, instead of repeatedly
unpacking the functor witness. The coefficient-unit proof uses the same API.
Original public declaration
signatures and public imports were checked unchanged; all Lean lines fit 100 characters.

## Proved and sorry left

Original holes: 2. Closed original hole: 1,
`WeilConjectures.CompletedHomScalarTranspose.completed_hom_scalar_transpose`.
Added holes: 2. This is a decomposition, not a net proof gain: there are three holes in the
delivered modules, compared with two in the original item.

The remaining original hole is
`WeilConjectures.CompletedHomScalarTranspose.modelBaseChange_existsUnique`
(node `lem-pod-completed-hom-scalar-transpose`). Its statement and proof are unchanged.

The added holes are:

- `WeilConjectures.PointScalarHomCochain.scalar_hom_cochain_pairing`
  (node `lem-pod-scalar-hom-cochain-pairing`): only the ordinary chain-map existence and
  local evaluation formula, without derived/completion or signed-evaluation conclusions.
- `WeilConjectures.PointScalarHomCochain.scalar_hom_derived_normalization`
  (node `lem-pod-scalar-hom-derived-normalization`): the fixed derived identity for any
  supplied chain map satisfying that formula; no chain-map or signed-evaluation existence.

The private `completionSquare_of_map`, `signedUncurry` construction and
`signedUncurry_apply` are complete. The main theorem's combination proof is complete.
No sorry is placed in a definition or a private declaration.

## No longer needed

None globally. No existing public import or declaration is removed, and no module is
withdrawn. The parent's direct proof-dependency edges to perfect-dual scalar calculus,
bounded-flat K-flatness, point completed evaluation, the Hom-complex definition,
derived internal Hom, one-K-flat chain transposition and derived closed symmetry
are removed: the appropriate child records those ingredients instead. They remain
needed below the parent, so this is not a claim of seven globally pruned nodes.
The parent's obsolete direct tool-use entries for bounded-flat K-flatness, one-K-flat
transposition and derived closed symmetry are removed; the other approvals retain their
order. The new child records these three tools as proof dependencies for the reader. The
bounded-flat, K-flat and derived-adjunction ingredients remain dependencies of the
derived-normalization step. The ordinary chain construction uses the ordinary
scalar dual map and sheaf tensor realization. There is no pruning claim for those modules.

## Where the brief, the DAG or earlier work was wrong

The existing proof dependencies do not directly state the combined ordinary point-sheaf
chain formula and its equality with the specified derived comparison. The two new nodes
record precisely those gaps. Abstract transpose injectivity alone does not supply the
representative normalization. Module extension/restriction and algebraic dual base change
do not by themselves supply the sheafification and fixed-model compatibility.

The new statements were checked on P=0, P=R[0], and a shifted rank-one complex. The first
makes both formulas zero; the second gives multiplication; the shifted example retains
(-1)^(p*j). The argument uses projective splittings rather than a global basis, and does
not assume that a ramified coefficient extension is etale or that sections preserve
infinite sums. The ordinary chain construction itself needs neither boundedness nor
finite-projectivity; the derived-normalization statement retains all original hypotheses.

No target, public definition, or existing statement is changed.

## New nodes

`lem-pod-scalar-hom-cochain-pairing` isolates the ordinary chain construction in
`Sheaf.Paper.PointScalarHomCochainPairing`. Its source is the parent's steps 2--4 and the
Hom-complex differential in the current blueprint/Stacks sources. Its proof first uses
ordinary module dual base change, then balanced tensor reassociation and sheafification.

`lem-pod-scalar-hom-derived-normalization` isolates the derived identification in
`Sheaf.Paper.PointScalarHomDerivedNormalization`. Its source is the parent's steps 1 and
4--6: bounded K-flat representatives, the fixed K-injective resolution, normalized tensor
comparison, both strict-cone coordinates and injectivity of the tensor-Hom bijection.
The generic bounded-flat, derived-change-of-rings, one-K-flat transpose and derived
closed-structure tools were already part of the parent's approved argument; the child
retains them to justify this representative normalization. There is no replacement of
the unit's route by a theorem from another unit.

There are no definition or statement change records, because existing interfaces and
meanings are unchanged.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
