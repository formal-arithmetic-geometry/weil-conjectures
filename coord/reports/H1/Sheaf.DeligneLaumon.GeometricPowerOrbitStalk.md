## What changed

Replaced the proof hole in `AlgebraicGeometry.WeilSheaf.exists_stalk_equiv_of_power_orbit`
by the three steps of its plan. The statement is unchanged.

`FrobeniusPowerCommutation` constructs the comparison between geometric power pullbacks and
ordinary functor iterates. Its `frobeniusPowIso_comm` derives commutation of the original returns
from the source library's proved `IsoAlgebra.strIterate_add_hom`. A proved categorical helper
cancels the monic inclusion of Q to show that the supplied e preserves the induced r-returns.
This resolves the full algebraic middle step, rather than adding another embedded-orbit lemma.

The remaining two steps have separate statements: `FrobeniusPowerDeckPoints` concerns only
schemes and points, and `FrobeniusPowerStalkTransport` concerns only an equivariant power
translate at supplied geometric points. The final proof combines them and applies the proved
source `WeilSheaf.nonempty_equiv_stalkAt` to compare the actual translated lift with the library's
chosen lift at the related point. No definition chooses data from either remaining proof hole.

## Proved and sorry left

Original hole closed by decomposition:
`AlgebraicGeometry.WeilSheaf.exists_stalk_equiv_of_power_orbit` (1 of 1 original holes).

Proved without new holes: `AlgebraicGeometry.ProEtaleWeilSheaf.frobeniusPowIso_comm` and its
iterate-comparison helpers; `restrict_commuting_returns` and `fixed_conjugate_power` in the item.
These prove the ambient commutation and monic-cancellation part of the argument.

Two holes added, each the whole proof of a public named theorem in its own module:

- `AlgebraicGeometry.Scheme.Hom.exists_frobenius_power_deck_point`
  (`lem-zl-frobenius-power-deck-points`): finite-point geometry, with no sheaves.
- `AlgebraicGeometry.WeilSheaf.nonempty_stalk_equiv_of_equivariant_power_translate`
  (`lem-zl-frobenius-power-stalk-transport`): local naturality at supplied geometric points,
  with no ambient object, embeddings, or existence of related finite points.

There are zero holes in the item module and two holes in the delivery. This is a decomposition,
not a complete proof of the mathematical result; it closes one hole and adds two.

Validation: all four modules compiled through `lcompile.py --all`; the main theorem took
27.6 seconds. The only warning was its unused original `hrpos` binder, now explicitly referenced by a local proof
without changing the signature. Delivery preflight recompiles this final version.
The original statement matches verbatim, all new node Lean attachments match, proof-dependency
lists equal the union of their steps, and each recorded search matches `searches.jsonl`.

## No longer needed

No original imports or dependencies were removed. No existing module or node is withdrawn.
All three original proof ingredients remain necessary; the new nodes refine their actual uses.
The point-only module imports GeometricFrobenius.Points rather than WeilSheaf.Stalk. The item
gets the geometric helper through the stalk-transport module's public import, without a
redundant direct proof import.
The previously split parents remain untouched and continue to use this item's unchanged theorem.

No irreducibility, geometric decomposition, eigenvalue or lissity module is imported for this
comparison. The point theorem uses the actual translated geometric lift; no additional lemma
asserting equality with independently chosen canonical lifts is needed.

## Where the brief, the DAG or earlier work was wrong

The DAG's cited dependencies provide definitions, not the complete deck-point or local
power-translate naturality theorems. The latter two missing steps are now explicit independent
statements. The middle step is proved using an existing addition identity in the adopted source.

The phrase about changing the geometric point must distinguish its actual translate from the
library's independently chosen lift. Equality between those lifts need not hold. The delivery
keeps the actual translate and uses the source's proved independence-of-lift theorem.

Edge cases checked: zero translate j=0, identity constant extension, empty schemes (there is then
no input finite point), zero sheaves, arbitrary non-lisse constructible sheaves, and schemes not
locally of finite type. No positivity, lissity, simplicity or finite-type hypothesis was added.
The cardinality identity excludes r=0 for finite fields when it is used for stalk transport.

## New nodes

`lem-zl-frobenius-power-return-commutation`: the three explicit pullback comparisons and the
proved commutation theorem in `Sheaf.DeligneLaumon.FrobeniusPowerCommutation`. The source is
step 2 of the item's proof, realized through the source's `strIterate_add_hom`.

`lem-zl-frobenius-power-deck-points`: the point-selection part of step 1, with no
coefficient objects. Equal degrees and the translated fixed-point square are proved in the item.
Its definition `frobeniusPowerTranslatePoint` is an actual composite of
scheme morphisms; its named theorem records finiteness, equal residue size and its underlying point.

`lem-zl-frobenius-power-stalk-transport`: step 3 for equivariant power-return objects, evaluated
at an arbitrary supplied geometric point and its actual translate. It does not perform monic
cancellation, choose finite points, or identify independently chosen lifts.

Searches: LeanSearch found presheaf/ringed-space stalk isomorphisms and finite-field Frobenius
automorphisms; LeanFinder found arithmetic Frobenius and unrelated small-object iterations;
Loogle had no entry for `IsoAlgebra`. Repository searches found the useful proved
`IsoAlgebra.strIterate_add_hom` and `WeilSheaf.nonempty_equiv_stalkAt`, but no deck-point or
source power-return stalk theorem. The new node records give the queries and results.

Change record: `coord/changes/H1-geometric-power-orbit-stalk.md`.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
