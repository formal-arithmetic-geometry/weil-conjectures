## What changed

Repaired `Sheaf.Paper.ContinuousModuleEncodingRestriction` against the current upstream-sync
library, retaining and completing the existing coefficient-transport proof.

The ring restriction theorem now uses `ProEtale.upperStarIsoSheafPushforward` and its existing
monoidal instance from the upstream `UpperLowerStar.InternalHom` module. That proof-only
import now works; the old private abelian specialization is removed.

The field restriction proof compares the pullback functors formed from the two definitionally
equal `Ring E` projections before evaluating them on a module. The equality gives an explicit
isomorphism on that module, which is mapped through the continuous encoding and composed with
the ring restriction comparison. The proved private coefficient-transport helpers then identify
the rational encoding and the prescribed `lisseEtaleCoefficientIdentification`.
This avoids the retained proof's kernel timeout from comparing scalar-extension objects.
`rename_i` names the existing normed-field instance within the proof; no instance is added.
All three existing public declaration signatures are textually identical to the current source.
All public definitions, assumptions, universes, and visibility are unchanged.

The existing node's proof and proof-origin note describe this route. The stale canonical-instance
change record is replaced by `coord/changes/E4-continuous-restriction-functor-transport.md`.
No module outside this item is changed.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.continuousField_module_restriction`
(node `lem-weil-pbc-continuous-module-encoding-restriction`).
Added 0 holes; split off 0 statements. There are 0 `sorry`s in the delivered module.
The ring restriction theorem and every private helper are proved.

The final module compiled without warnings in 11.4 seconds. A fresh artifact build compiled
the item in 12.0 seconds and both unchanged direct importers:
`ContinuousModuleEncodingLattices` in 3.8 seconds and
`ContinuousModuleEncodingSliceFreeness` in 7.2 seconds.
A separate axiom check compiled in 11.4 seconds. Both restriction theorems use the three standard
axioms and inherited `sorryAx` from existing dependencies; this delivery adds no local hole and
does not claim that the full dependency closure is axiom-free. The earlier retained report's
claim of only the three standard axioms is not valid for the current compiled dependencies.
Scratch checks and copied consumer sources are outside the delivered `lean/` tree.

## No longer needed

No import, DAG node, or library module is pruned. The existing proof dependencies remain needed.
The sole public import supplies the coefficient encodings occurring in the declarations.
The new private upstream import supplies the monoidal localization comparison.

Removed the private `encoding_localization_comparison` and `encoding_localization_monoidal`
copies, since the current upstream comparison supplies them. Removed the unused retained
`rawContinuousPullback` definition and `continuousRing_raw_restriction` helper. None of these
private helpers has a separate node or creates a pruned module.

## Where the brief, the DAG or earlier work was wrong

The upstream-sync return required an actual compile repair. The retained field proof did fail
kernel checking, despite its stale report saying it compiled. Comparing its elaborated result
with the goal isolated the differing `CommRing.toRing` and `DivisionRing.toRing` paths inside
the pullback. An explicit equality of the functors checks quickly; mapping its isomorphism
through the encoding avoids unfolding the scalar-extension construction.
The source theorem statement and the unit route require no mathematical correction.

The old private localization specialization said the general upstream module could not be
imported because of duplicate declarations. That restriction no longer holds against the
current library, so the proof now uses the existing upstream result.

The retained canonical-instance report and independent-reader section described an earlier
implementation. They were removed; the fresh second reading is recorded below.

## Second reading by E4

1. **Interface and definitions: PASS.** Read the full module and its diff against the shared
   repository. The signatures of `continuousRestrictionMap`, `continuousRing_module_restriction`,
   and `continuousField_module_restriction` are byte for byte identical. The entire concrete
   definition of `continuousRestrictionMap` is also identical. No other module is delivered,
   and no public definition, hypothesis, conclusion, universe, or visibility changes.
2. **Proof and axioms: PASS.** Independently compiled the delivered file without errors or
   warnings in 13.1 seconds. Compiled a scratch copy with `#print axioms` for all nine public
   and private declarations in 18.3 seconds. Their axioms are contained in `propext`,
   `Classical.choice`, `Quot.sound`, and inherited `sorryAx`; there is no local `sorry` or
   forbidden declaration. The private pushforward square is an explicit composite of
   `pushforwardComp` and equality isomorphisms, with no choice of arbitrary data. The field
   proof obtains isomorphisms only inside a theorem proof.
3. **Split statements: PASS (none).** The delivery adds zero holes and zero split statements;
   all new private helpers are proved. Checked the coefficient square's orientations and
   its identity-coefficient case: the two composites agree and transport reduces to ordinary
   restriction. The argument also works for the zero module and empty scheme; it requires
   neither nonzero sections nor a nonempty underlying space.
4. **Route and pruning: PASS.** Read the imported encoding, chart, and coefficient interfaces
   and the upstream monoidal localization comparison. Searched the library for coefficient
   transport and presheaf pushforward comparison results, and ran the launcher's Mathlib
   grep search for `PresheafOfModules.pushforwardComp|upperStarIsoSheafPushforward`.
   The proof already uses the available upstream comparison and pushforward composition
   API. Both imports are needed; only the encoding import is public, since it supplies types
   in the existing signatures. All three old proof dependencies remain used, so `No longer
   needed` correctly lists no pruned node or module. Read the unit's statement, three steps,
   and `realized` entries: this coefficient-compatibility proof changes none of that route.
5. **DAG agreement: PASS.** Compared both node records: only `proof` and `proof_origin` change.
   Their steps describe the actual monoidal comparison, chart conjugation, sectionwise
   linearity, functor equality, and coefficient transport. The unchanged `proof_deps` are
   exactly the three existing encoding, coefficient, and chart-realization nodes used here.
   There are no new node records to validate.

Second reading changed this report only: recorded the independent checks and replaced the
stale statement that a second reading was still pending. The Lean proof, node, and change
record required no repair. Closed 1 of 1 original holes; added 0 holes; split off 0 statements.
