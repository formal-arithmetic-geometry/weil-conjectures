## What changed

Proved `WeilConjectures.integralOperationsWellDefined` with its original signature.
The proof establishes both quasi-isomorphism clauses, natural descent, uniqueness
compatible with representative comparisons, and the derived-limit assertions.

Finite reduction preserves quasi-isomorphisms of K-flat complexes. Tensor
cancellation proves that the reductions remain K-flat with flat terms, so the
existing site derived tensor comparison gives finite tensor invariance. Exactness
of the specified constant-coefficient module pullback gives finite pullback
invariance. Restriction of scalars is exact. Exact countable products and the
mapping-cone triangle then give invariance of the strict Roos constructions.

A functorial flat resolution proves that good complexes localize to the full
derived category. Universal localization and its product construct the descended
functors and their comparisons. Fully faithful precomposition gives uniqueness.
The Roos distinguished triangle proves the derived-limit property, which transports
along the representative comparisons.

Three reusable coefficient results have new modules and complete proofs: tensor
cancellation, preservation of K-flatness under coefficient change, and exactness
of the specified pro-etale coefficient pullback, all in independent universes.
Operation-specific arguments are proved private helpers in the original module.
Every original construction retains its name, signature, universe, body, visibility
and defining module. No target, definition or mathematical statement changes.

The earlier sandbox extracted the constructions and introduced separate modules
for the operation-specific clauses. That extraction is now unnecessary: the
consolidated proof compiles in 49.5 seconds after local opacity avoids expanding
large coefficient expressions during elaboration. Two duplicated private helpers
are merged. These are local proof changes; the original definitions are unchanged.
The extraction's unlanded files and records are retained only in the scratchpad,
outside the delivery. The packet contains four
Lean modules and three new nodes, with no consumer adaptation. The static checker
records the added proof-section commands as an interface change, documented in
`coord/changes/integral-operations-proof-commands.md`. All four modules compile together through `lcompile.py --all` with no errors or
warnings (the main module takes 49.5 seconds). Delivery preflight is run on this
completed packet. Two unchanged consumers, `IntegralDerivedOperations` and
`IntegralTowerLimitComparison`, compile against the final packet.

## Proved and sorry left

Original hole closed:

- `WeilConjectures.integralOperationsWellDefined`
  (`lem-pur-integral-operations-well-defined`).

New public theorems, all fully proved:

- `SheafOfModules.exists_changeOfRings_tensorCancellation_independentCoefficients`
  (`lem-pur-change-of-rings-tensor-cancellation-independent`);
- `SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients`
  (`lem-pur-kflat-change-of-rings-independent`);
- `AlgebraicGeometry.Scheme.coefficientProEtaleModulePullback_exact`
  (`lem-pur-coefficient-pullback-exact`).

All private helpers are proved, including comparison existence, both invariance
clauses, localization, uniqueness and triangle transport. The only remaining
`sorry` occurrences are the two unchanged original transition specifications in
the item module, attached to `lem-pur-integral-operations-well-defined`:

- `WeilConjectures.integralOperationsPullbackTransition_existsUnique`;
- `WeilConjectures.integralOperationsTensorTransition_existsUnique`.

Count: one of three original holes closed; two original holes retained; zero holes
added; zero unproved statements split off. There is no `sorry` in a definition.
The retained unique-existence specifications determine the transitions used by the
existing constructions. No arbitrary witness of mere existence supplies data.

## No longer needed

No existing whole module is claimed pruned from the targets' import closure.
The original main module no longer directly imports:

- `Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso`;
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`;
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`;
- `Mathlib.CategoryTheory.Localization.Predicate`;
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`;
- `Mathlib.CategoryTheory.Adjunction.Additive`;
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`;
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`;
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`.

The coefficient pullback exactness module drops the unused
`Mathlib.CategoryTheory.Abelian.ShortExact` import. The independent coefficient
K-flat proof drops the legacy `Sheaf.Algebra.Homology.KFlat` import and the redundant
explicit `KFlatCoefficientUniverse` import, already exported by its statement
interface. The explicit `TensorColimitsIndependentCoefficients` proof import is
needed for `siteSheafTensorRightIso` and is retained.

The proof replaces the original direct dependencies
`lem-pur-kflat-change-of-rings` and `prop-weil-pbc-proetale-constant-exact` by their
proved independent-universe versions. The finite-reduction witness supplies the
quasi-isomorphism assertion without a separate use of
`lem-pur-change-of-rings-kflat-quasi-iso`. The source-library product
quasi-isomorphism lemma and cone triangle replace a separate appeal to
`lem-weil-derived-limit-levelwise-iso`. Mathlib localization of good complexes
replaces the manual homotopy descent and the separate
`lem-weil-pbc-localization-universal-property` dependency. Only the obsolete
`prop-weil-pbc-proetale-constant-exact` top-level tool approval is withdrawn.

The ten unlanded operation-specific modules, including the construction extraction,
are unnecessary and absent from this delivery. No previously landed module or DAG
node is withdrawn. The blueprint unit's statement and route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The inherited packet left comparison existence unproved and used its comparisons
to obtain both invariance assertions. This session proves finite-level invariance
first, then constructs the comparisons by universal localization. The final main
node records this acyclic argument; no new hole remains from the inherited split.

The original change-of-rings and finite pullback interfaces did not fit the actual
coefficient universe `max u (t + 1)` or the specified pullback presentation.
The independent-universe theorems prove the needed assertions for those actual
constructions. The ring-pullback comparison is normalized by the constant-section
unit. Tensor cancellation works for zero rings and zero modules; pullback exactness
has no nonempty-site or flatness hypothesis. Uniqueness is compatible with the
representative comparisons, as the original statement requires.

The dispatcher reset the reference clock at 2026-10-19 17:06:23 UTC on resumption.
Earlier dry runs counted the two original holes moved into a new construction
module as added holes. Consolidating the proof removes that extraction completely.
No budget metadata or launcher script was edited. The final packet has the two
original holes in their original module and adds none. The earlier work and tool
outputs remain in the scratchpad.

## New nodes

`lem-pur-change-of-rings-tensor-cancellation-independent` proves the balanced
sectionwise cancellation, then descends it through sheafification and establishes
naturality in both variables. Its source is Stacks Tag 05V4.

`lem-pur-kflat-change-of-rings-independent` uses cancellation and exact conservative
restriction of scalars to prove flatness of terms and acyclicity of total tensors
under the specified coefficient change. Its sources are Stacks Tags 0G7E and 06YN.

`lem-pur-coefficient-pullback-exact` transports through coefficient-sized site
models, proves the normalized constant-ring inverse-image comparison, and reflects
exactness through the underlying abelian sheaf functor. Its sources are Stacks
Tags 00YV, 03D2 and 04JC.

The proof-command change record is
`coord/changes/integral-operations-proof-commands.md`. Preflight also required the
LeanSearch kind separately from Loogle/LeanFinder; all three new nodes now include
real LeanSearch queries (eight hits each), in addition to their earlier searches.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
