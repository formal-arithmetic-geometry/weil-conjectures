## What changed

Replaced the hole in
`AlgebraicGeometry.WeilSheaf.nonempty_stalk_equiv_of_equivariant_power_translate`
by a compiling proof from one strictly smaller single-return compatibility statement.
The original statement, binders, universes, visibility and public imports are unchanged.
The proof adds private imports of `WeilConjectures.WeilSheaf.StalkUpperStar` and
`Sheaf.DeligneLaumon.FrobeniusPowerTranslateStructure`.

The new module constructs `frobeniusPowerTranslateAut` and
`frobeniusPowerTranslateSheafIso` explicitly. In particular, its carrier map is not selected
from an unproved existence theorem. It is a composite of the pullback/inverse-pushforward
comparison, pushforward compositors, the given carrier equalities and the supplied `e`.
Its one unfinished theorem is `frobeniusStr_powerTranslate`, the compatibility of this
specific isomorphism with one return on C.

The item proves, with no additional holes: commutation of the conjugated geometric map
with Frobenius; an induction extending the single-return square to all positive iterates
on global sections; invertibility of the actual stalk map; and its Frobenius equivariance.
The zero iterate uses the proved identity `frobeniusEnd_stalkAt_zero`. The final linear
Frobenius-module equivalence is inverted to give the required B-to-A direction.

This is a decomposition, not a complete proof of the entire mathematical obligation.
The remaining statement has no geometric points, local Frobenii, stalks, scalar squares,
or iteration parameter m. The induction and passage from the single-return square to the
original conclusion are actual proved Lean code in this delivery.

Repair of the returned delivery: restored the reverted packet from commit `4e3756730b`
and compared its node and module with current main. The original compatibility hypothesis
was declared by a section `variable` command. Although ordinary compilation succeeded,
a Lean environment probe found synthetic holes at its two `frobeniusStr` terms, in all
three helper types, and in the final proof. Writing all compositor arguments explicitly
alone did not fix this. The compatibility hypothesis is now an explicit binder of each
private helper, where the privately imported structure maps are elaborated in the helper's
context. The public single-return theorem also spells out its compositors and coefficient
category. Both modules, including the importer identified in the return, are in this packet.

Validation: the final companion module compiled in 7.3 s and the item in 10.6 s.
The unchanged direct importer `Sheaf.DeligneLaumon.GeometricPowerOrbitStalk` compiled
against the set in 16.9 s; its temporary sandbox copy was then removed. A separate
Lean-environment probe found zero direct holes in all item declaration types and values,
zero holes in both new definitions, and precisely the declared body hole (not a type hole)
in `frobeniusStr_powerTranslate`. Diagnostic commands were removed before the final compile.
The original item statement and public imports are preserved. The unit's realized route
is kept.

## Proved and sorry left

Original holes closed by decomposition (one):
`AlgebraicGeometry.WeilSheaf.nonempty_stalk_equiv_of_equivariant_power_translate`
(node `lem-zl-frobenius-power-stalk-transport`). No `sorry` remains in the item module.

Holes added (one): `AlgebraicGeometry.WeilSheaf.frobeniusStr_powerTranslate`
(node `lem-zl-frobenius-power-translate-structure`). Its entire proof is `by sorry`;
it is a public named theorem, with the source and the full comparison argument in its docstring.

Net hole reduction: zero. This delivery discharges construction, iteration and local
Frobenius transport, leaving the single-return coherence step as the next item.
Both new definitions and all five private helper theorems have complete proofs or bodies.

## No longer needed

No imports were removed and no modules were withdrawn. All original statement dependencies
are retained. The deck-point module is needed for its explicit point definition, but its
`exists_frobenius_power_deck_point` theorem is not used by this proof. No finite point,
finite-point existence theorem, ambient sheaf, monomorphism, or independent choice of a lift
is needed for the stalk transport assertion.

No declared proof dependency is globally pruned. In particular the existing source
constant-field restriction declarations remain intact; the proof uses their transport
construction rather than adding a different notion of Weil sheaf.

## Where the brief, the DAG or earlier work was wrong

The returned packet's ordinary successful compile was insufficient evidence: the section
hypothesis had inserted holes despite containing no written `sorry`. This repair checks
Lean expressions for direct `sorryAx` occurrences in both types and values, in addition to
compiling the importing module against its companion.

The item has one original hole and its dependency declarations exist, but those declarations do not
state the single-return compatibility square for the constructed translated carrier map.
`frobeniusPowIso_comm` concerns the returns of one actual single-Frobenius Weil object;
it does not by itself identify the formal commutor with the geometric comparison for
arbitrary r-return algebras P and Q. The remaining square is therefore stated explicitly,
with exactly the given equivariance equation as its input.

Repository search found the proved `globalSectionsTransport_comm_of_upperStar`,
`globalSectionsTransport_frobeniusPowStr_comp`, `frobeniusEnd_stalkAt`, and the zero-iterate
identity. They supply the last two steps once generalized from the geometric-fibre map of
a base-field morphism to an arbitrary commuting geometric map. That generalization is
proved privately here. No statement is disputed, weakened, or changed.

The new square was checked on j = 0, r = 0, an identity theta, and zero sheaves: the
construction uses the corresponding identity or zero-object comparisons, and the
compatibility is precisely the assumed return equation through those comparisons.
The m = 0 case of the original theorem is proved independently in Lean. A geometric point
is supplied, so no nonemptiness or finite-type assumption is silently introduced.

## New nodes

`lem-zl-frobenius-power-translate-structure` records the explicit conjugated automorphism,
carrier isomorphism and its single-return compatibility. It realizes only step 2 of the
old node; the pointwise construction, induction and scalar comparison are already proved
in the item. The source is the geometric-orbit step recorded by that node in
`sk-i-dl-general-real`. Searches were run with LeanSearch, LeanFinder, Loogle and Mathlib
text search; none gives this comparison square. The source-library pushforward and
pullback coherence lemmas remain tools for its proof. Blueprint search found no matching
separate node named by the power-translate description.

Change record: `coord/changes/H8-frobenius-power-stalk-transport.md`.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
