## What changed

Proved `Algebra.pointedEtaleQuotient_final` with its original signature and public
imports unchanged. Added three proof-only imports and six proved auxiliary modules.
The explicit functor is extension of scalars followed by transport of the point
through H(K) ≅ L, restricted to etale objects. Its forgetful comparison is reflexive.
Etaleness preservation follows from Mathlib stability under base change.

The point comparison uses the bijective residue-field map, `IsSepClosure.equiv`,
and the actual ring pushout universal property. The pushout adjunction gives
bijectivity of maps into the point. The existing coefficient-lift theorem yields
etale pushout lifts, first of objects and then of morphisms relative to their
source algebra. Existing filteredness of pointed etale algebras supplies source
successors and target equalizers. Relative morphism lifting then constructs a
common successor in each comma category. The main proof assembles the zigzag
X -> Z <- Y and applies the connected-comma criterion for finality.

No existing dependency statement, definition or interface was changed. There
are no forced adaptations or change records.

## Proved and sorry left

Closed the one original hole, `Algebra.pointedEtaleQuotient_final`.
Added zero holes; no delivered Lean file contains `sorry`.
All six new theorem declarations are proved:

- `Algebra.quotientBaseChange_etale`.
- `Algebra.pointedEtaleQuotient_point_iso`.
- `Algebra.quotientBaseChange_point_bijective`.
- `Algebra.pointedEtaleQuotient_comma_nonempty`.
- `Algebra.pointedEtaleQuotient_morphism_lift`.
- `Algebra.pointedEtaleQuotient_comma_refinement`.

The functor and its comparison isomorphism are real constructions; all private
helpers are proved. This is a proof from existing declarations, including the
existing `Algebra.exists_etale_coefficientLift` of `Sheaf.RingTheory.EtaleAlgebraLift`.
Existing unfinished dependencies in its import closure, if any, are unchanged;
this delivery does not claim a sorry-free transitive closure. Accounting: one hole closed,
zero added, zero split off as new unfinished statements.

Prescribed sandbox compilation passed for all seven modules with no warnings.
The individual compile times were 2.1, 2.7, 3.2, 4.3, 6.7, 3.0 and 2.7 seconds.

## No longer needed

No original imports were removed. The following old proof dependencies are
unnecessary for this argument and removed from the parent's proof route:

- `lem-weil-pbc-quotient-residue-field`: residue-field bijectivity is proved
  directly, rather than invoking its quotient-field statement.
- `lem-weil-pbc-etale-ring-map-iff-etale-affine`: no affine-scheme dictionary is used.
- `def-weil-etale-morphism`: no scheme etaleness argument is used.
- `def-weil-unramified-morphism`: no open scheme diagonal argument is used.

The corresponding scheme modules `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`,
`Mathlib.AlgebraicGeometry.Morphisms.Etale`,
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
`Mathlib.AlgebraicGeometry.OpenImmersion` are not needed as proof imports here.
This is route pruning, not a claim that those modules are globally unreachable.
`lem-exc-etale-algebra-lift` remains necessary. The existing pointed filteredness
node `lem-sc-pointed-etale-filtered` is used in place of the diagonal argument.
Redundant draft imports of LocalRing.RingHom.Basic and SeparableDegree were removed;
the existing public interface already exposes the needed declarations.

## Where the brief, the DAG or earlier work was wrong

The DAG's scheme-diagonal route is unnecessary. Filteredness plus relative
etale morphism lifting provides common successors in the comma categories.
The coefficient-lift declaration supplies the underlying reduction pushout;
its pointed compatibility and relative version required actual Lean assembly.
No false or changed statement was used.

The first dry run required LeanSearch in addition to LeanFinder/Loogle and source
grep. All six LeanSearch requests returned Internal Server Error; these actual
requests are logged and recorded as unavailable in the new nodes, without a
verdict. The other searches and the actual Mathlib proofs supply the inputs.

The published SurjectiveQuotientBaseChange dependency initially lagged its
landed source. It became available with the next green build, and full prescribed
compilation then passed. No dependency was copied or compiled to bypass publication.
The landed strict-henselization quotient-action change record was read; this proof
uses the explicit extension-of-scalars functor and does not rely on arbitrary
quotient actions.

Edge cases checked: for identity π, point transport is by an isomorphism. No
nilpotence of ker π or Noetherian hypothesis is used. The kernel acts trivially
on K because it lies in the maximal ideal; this gives the adjunction unit
isomorphism. The relative lift works for arbitrary etale algebras, not just
finite algebras. The unit's realized lists are empty, so no prescribed unit-level
statement or proof step was bypassed.

## New nodes

`lem-sbc-pointed-etale-quotient-functor` records proved preservation of etaleness,
the explicit functor, and its reflexive forgetful comparison.

`lem-sbc-pointed-etale-quotient-point` records the proved comparison H(K) ≅ L
using residue-field bijectivity and pushout uniqueness.

`lem-sbc-pointed-etale-quotient-point-bijective` records the proved bijection on
maps into K after extension of scalars, using the adjunction unit isomorphism.

`lem-sbc-pointed-etale-quotient-comma-nonempty` records the proved pointed
object lift and its structured arrow, from the coefficient-lift theorem.

`lem-sbc-pointed-etale-quotient-morphism-lift` records the proved relative lift
of pointed morphisms, using coefficient lifting and pushout pasting.

`lem-sbc-pointed-etale-quotient-comma-refinement` records the proved common
successor construction using filteredness and relative morphism lifting.

All new nodes are proved auxiliary results, not new unfinished items. The parent
node's proof and dependency fields now follow this Lean route. No change records.

## Second reading by U3

1. **Signatures and visibility.** I diffed the delivered item module against the
repository version. The existing theorem signature and all existing declarations
are byte-for-byte unchanged; only proof imports and the proof body changed. The
six auxiliary modules are new files, with their public declarations matching their
DAG node statements. Verdict: pass.

2. **Proof and axioms.** I compiled all seven delivered modules with the prescribed
`lcompile.py --all` command. They compile without errors or warnings. I searched
the delivered Lean files for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`,
and `extern`; none occur. The constructions use actual pushout and coefficient-lift
data, with no hollow definitions. Verdict: pass.

3. **Split statements.** I checked each of the six auxiliary statements against
its docstring, source, and node. Each is a strictly smaller intermediate result
(functor construction, point comparison, map bijection, comma nonemptiness,
relative lift, or common refinement), and each is used by the final proof. The
edge case of the identity quotient reduces to transport along an isomorphism.
No duplicate Mathlib or upstream declaration was found in the recorded searches.
Verdict: pass.

4. **Pruning and route.** The final proof uses the explicit extension-of-scalars
functor, coefficient lifting, pointed filteredness, and the connected-comma
criterion. The old scheme-diagonal dependencies listed in `No longer needed` are
not imported by the delivered modules. The unit's `realized` list is empty, so no
unit-level route is bypassed. Verdict: pass.

5. **DAG agreement.** I checked the parent node's proof steps and `proof_deps`
against the imports and theorem applications, and checked all six new node Lean
records and proof origins. They agree with the delivered declarations and contain
the required source and search metadata. Verdict: pass.

I changed only this report section; no Lean statement, definition, or DAG record
needed repair after the second reading.
