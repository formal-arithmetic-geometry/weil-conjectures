## What changed

Repair of return C-73b31: reclaimed the current rework item for U4 and compared
the retained packet with returned head 73b31bacd. The item text matched that head.
The current archive is quarantine/Sheaf/SixFunctors/CoefQbarVerdierCore.lean
(SHA-256 39036e8fdae4eedc85aef4db4f621ee6fc3280f850e8cc78971e59733e2bfba1).
Restore the reviewed implementation to its original lean/ path; preserve all five
archived public declarations and the original core node attachment. In particular,
CoreProperties is verbatim the archived definition. No archive is deleted, no
withdrawal stub is supplied, and no path is listed for deletion. The delivery
tool rebases this restoration on current sheaf-dag rather than the old f326929ff base.
The first repair preflight stopped before pushing because Data and
RationalHomIdentifications were quarantined source imports. Both subsequently
returned verbatim through the project restoration, and are committed by the
current 30d90446634 build head. Their restored and archived SHA-256 hashes match.
The original item also returned at its original path. The repair therefore
rebases the reviewed proof onto that restoration, preserving its dependencies.
A fresh server compile of all six reviewed modules succeeded without warnings
(CoreEquations 38.8 s, FiniteCoherence 19.0 s, Functor 12.9 s, Biduality 10.6 s,
Evaluation 12.9 s, item 32.8 s). The source-restoration check then confirmed both restored dependencies are
verbatim their archives. Delivery performs the current-source and consumer checks.

Constructed the common-stage contravariant functor in CoefQbarVerdierFunctor
using the existing opposite-representative and StageSystem.Morphism quotient APIs.
Proved its literal finite-stage object formula and identity-component inclusion
comparison. In CoefQbarVerdierEvaluationDescent, constructed omega at the base
coefficient field, its comparisons by finite u maps, and evaluation by the
included finite evaluation. Proved its finite-inclusion normalization by iso
cancellation. A private proved helper obtains anti-equivalence directly from biduality using
Mathlib Functor.IsEquivalence.mk', avoiding a second inverse-Hom calculation.
The item assembles those constructions into DualityData and proves
core_descent from three smaller coherence/equations statements.

Moved the unchanged CoreProperties, core_complete and completeCore APIs into
CoefQbarVerdierCoreEquations and publicly reexported them from the item. This
isolates the formal retract proof from the descent construction and its proof
imports. Existing public names, statements, attributes and definitions remain
mathematically unchanged. The source library is untouched. All six delivery modules compile without
warnings within 60 seconds each (largest helper 54.1 seconds; item 47.9 seconds).
Both direct consumers, CoefQbarVerdierDualizing and CoefQbarVerdier, compile
unchanged against the packet (8.5 and 7.3 seconds); their temporary sandbox
copies were removed.

## Proved and sorry left

The item originally had one hole, core_descent; its proof is now complete.
This is a decomposition, not a net closure: three named lower holes are added:

- WeilConjectures.CoefQbarVerdier.finite_coherent
  (lem-coef-qbar-verdier-finite-coherence): only finite beta unit/tower equations.
- WeilConjectures.CoefQbarVerdier.descended_duality_exists
  (lem-coef-qbar-verdier-biduality-equations): exact linear biduality and comparison
  equations for the already constructed functor; no omega/evaluation data.
- WeilConjectures.CoefQbarVerdier.descendedEvaluation_equations
  (lem-coef-qbar-verdier-evaluation-equations): omega coherence and naturality of
  the already constructed evaluation; no duality or evaluation existence claim.

All three have source references and complete proof plans in their docstrings.
The constructions contain no sorry and select no arbitrary existential witness.
The new functor/object/comparison and finite-evaluation normalization proofs are
complete. The existing finite_data_exists and formal retract completion remain
proved. The finite-data construction is checked in finiteData_nonempty in the
finite-coherence module, while finite_data_exists keeps its original public
statement as a small proved wrapper. In total: one upper hole closed, three lower holes added, zero holes in
the item and three in the packet.

## No longer needed

The item's direct proof import of Sheaf.CategoryTheory.StageSystemOpposite is
replaced by the Functor module; the opposite-stage construction remains needed
there. The planned wrapper lem-sbc-coherent-pair-functor-descent and its module
Sheaf.CategoryTheory.StageSystemFunctorDescent are not used by this proof: the already
proved source-library StageSystem.Morphism.functor and functor_map_ι suffice
directly, as attached to lem-pur-associative-stage-family-descent. This is the
same representative construction, not a replacement of the unit route. No module
is withdrawn or claimed globally unreachable. The direct RationalHomIdentifications import moved from the item to
FiniteCoherence with the finite-data construction. The item's direct RationalVerdier
proof import is no longer needed; its API remains publicly available through
Data and is used by the finite construction. IntrinsicQbarCategory remains used. The unit's coefficient
descent route is preserved. No upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is disputed. The original module exceeded the 60-second
compile limit even before proof changes; its dependent identity-component HEq conversion and
the enlarged functor comparison needed performance investigation. Per-step
heartbeat counts identified the identity-component HEq clause as the expensive
conversion, and its proof was isolated through the generic stage-system API. The rework row read for this repair assigns restoration after the
CoefficientChange dependency quarantine. Its recorded build error lists missing
Data, RationalHomIdentifications and RationalVerdier imports. These dependencies
remain mathematically required. This repair preserves their dependency records
and restores the archived item through the reviewed implementation; it does not
treat missing sources as a withdrawal request.

## New nodes

lem-coef-qbar-verdier-finite-coherence records the normalized finite unit/tower step
and the already proved finiteData_nonempty construction.
lem-coef-qbar-verdier-representative-functor records the explicit quotient functor
and the proved comparison formulas. lem-coef-qbar-verdier-biduality-equations
records exactness, linearity and biduality for that fixed functor; anti-equivalence
is derived from biduality in the consumer.
lem-coef-qbar-verdier-evaluation-equations records the explicit omega/evaluation
construction and its remaining equations. lem-coef-qbar-verdier-retract-completion
records the already proved formal retract argument in its new module. The original
core node's proof and Lean declaration list follow this decomposition.

Change record: coord/changes/U4-qbar-verdier-explicit-descent.md.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefQbarVerdierBidualityDescent": "4c95fad07b872e6c11d7db8cdc9e7a16a64ed505", "Sheaf.SixFunctors.CoefQbarVerdierCore": "9e958454f1e189dec671106840380e92f3724fdc", "Sheaf.SixFunctors.CoefQbarVerdierCoreEquations": "54a843d825394530e98b48aacd7705138a496eeb", "Sheaf.SixFunctors.CoefQbarVerdierEvaluationDescent": "8999b79d2d840a6de8774f9cf3b87a1c62cd53e4", "Sheaf.SixFunctors.CoefQbarVerdierFiniteCoherence": "0923df2ea38e9697e3eeb29190f7ff7088fc825a", "Sheaf.SixFunctors.CoefQbarVerdierFunctor": "837b7fef85cadf744d47008e69a572a30258bafa"}, "results": {"Sheaf.SixFunctors.CoefQbarVerdier": {"hash": "36026758723ddb846cce37cc323a7b8f7ea0a6f9", "status": "OK"}, "Sheaf.SixFunctors.CoefQbarVerdierDualizing": {"hash": "cd16b4af6d8c1a630d26dd9de7b846da0c3f90f8", "status": "OK"}}, "seconds": 51, "time": "2026-10-28T01:56:31+0800", "transitive": 0, "version": 1}
```

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
