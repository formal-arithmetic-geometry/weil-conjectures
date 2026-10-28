## What changed

Repair the returned landing 20261028T034856-L-3560188, following the maintainer's
2026-10-28 05:55 UTC diagnosis in coord/returns/N2.md. The unit clause in
CoefQbarVerdierData and finite_unit_equation contain definitionally equal but
syntactically different coefficient-instance proof terms. Direct conjunction
introduction caused a kernel deterministic timeout. The repaired finite_coherent
uses the supplied run_tac argument to replace only differing proof subterms by
proof_irrel, congrArg and Eq.mp, then combines the unit and tower clauses.
The generated proof is checked by Lean's kernel; it adds no axiom or check bypass.

Restore CoefQbarVerdierFiniteUnit and CoefQbarVerdierFiniteTower, together with
lem-coef-qbar-verdier-finite-unit-equation and
lem-coef-qbar-verdier-finite-tower-equation, which the returned delivery introduced
and the batch take-out removed. These retain the unit and tower formulas and their
proof plans. The item imports both modules privately and preserves
finiteData_nonempty and the exact finite_coherent signature. The main node now
records the two component obligations and explicit proof transport.

Validation: all three delivered modules compile without errors or warnings; the
item compiles in 26.6 seconds, below the unchanged 60-second limit. A scratch
#print axioms check for finite_coherent and finiteData_nonempty reports only
propext, Classical.choice, Quot.sound and the expected sorryAx from existing
unfinished dependencies (including the two component obligations). The unchanged
direct importer Sheaf.SixFunctors.CoefQbarVerdierCore compiles against the repaired
overlay in 39.1 seconds; its temporary sandbox copy has been removed.

Only the item and its two restored component modules and three matching node files
are delivered. CoefQbarVerdierData and all existing consumer sources are unchanged.

## Proved and sorry left

The item originally has one textual hole,
WeilConjectures.CoefQbarVerdier.finite_coherent. It is now proved from the two named
component equations. WeilConjectures.CoefQbarVerdier.finiteData_nonempty retains
its existing complete proof. The item's remaining textual hole count is zero.

The delivery retains the two split holes of the returned landing:

- WeilConjectures.CoefQbarVerdier.finite_unit_equation in
  CoefQbarVerdierFiniteUnit, node lem-coef-qbar-verdier-finite-unit-equation.
- WeilConjectures.CoefQbarVerdier.finite_tower_equation in
  CoefQbarVerdierFiniteTower, node lem-coef-qbar-verdier-finite-tower-equation.

Against current main after the take-out, this closes one hole and restores two
split holes: a decomposition, not a completed proof of the underlying coherence
mathematics, and no net hole reduction. Against the returned delivery, this fixes
the kernel timeout and adds no further holes or split obligations.

## No longer needed

None. Both unit and tower obligations remain necessary. The parent uses
thm-coef-rational-verdier and lem-coef-rational-operations for finite-data
existence, and uses both component nodes for coherence. Its old direct proof
references to lem-weil-scalar-extension-composition,
lem-coef-integral-finite-extension and def-weil-algebraically-closed-coefficients
are retained as dependencies of the component nodes; these are not globally pruned.
No module, public import, declaration or unit route is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The shared sandbox initially contained only launcher marker files, rather than the
retained packet described in the brief. The returned landing's packet has been
restored and reconciled with current main. The current return includes the
maintainer's tested proof-irrelevance repair; this supersedes the previous
worker's conclusion that final assembly cannot meet the compile limit.

The expensive conversion involves 706 occurrences of coefficient-instance proof
parameters and the reflexivity proof in the unit equation. Its mathematical
statement is unchanged. The tower clause needs no such transport. The repair
checks each replaced term has propositional type and constructs explicit equality
transport rather than increasing any compilation or heartbeat limit.

## New nodes

lem-coef-qbar-verdier-finite-unit-equation and
lem-coef-qbar-verdier-finite-tower-equation restore the two independent clauses
introduced in the returned landing. Each is strictly one part of FiniteCoherent;
neither restates the conjunction or asks for the full theorem under another name.
No additional intermediate theorem or shared definition repair is introduced.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefQbarVerdierFiniteCoherence": "ec5a5eab86c2e7b329f7344427e6bc913cb3325e", "Sheaf.SixFunctors.CoefQbarVerdierFiniteTower": "4808ce38716b8389c54f1d0c09e8cbc9d7bcd716", "Sheaf.SixFunctors.CoefQbarVerdierFiniteUnit": "fb10d11507ff87bb6f53b4b211a6ae8a21f2d084"}, "results": {}, "time": "2026-10-28T13:58:51+0800", "transitive": 0, "version": 1}
```

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
