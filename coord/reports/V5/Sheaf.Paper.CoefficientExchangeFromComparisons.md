## What changed

Definition change record: `coord/changes/V5-coefficient-exchange-ambient-interface.md`.

Restore the quarantined `Sheaf.Paper.CoefficientExchangeFromComparisons` with its public theorem signature verbatim. Repair the exchange-step representation by retaining all four vertices and three arrows in an `ExchangeChain`, and retaining the original total-map factorizations in its comparison record. The typed `mapHom` is proved equal to the original functor map. The internal chain uses the actual ambient residue adjunction and square; the etale chain uses the actual etale adjunction and square. Both total components are the original constructions, with proved defining equations.

The proof uses the existing `boundedConstructibleBaseChange_hom_eq_ambient`, the existing etale mate formula, and a fully proved coherent-family specialization of `threeStepComparison`. A private reflexive equality of whole pullback families removes the automatically inserted eta expansion before specializing square coherence. No derived construction or coherence hypothesis changes. `CoefficientDerivedFunctorAPI`, `FiniteDiscreteDerivedCoefficientData`, and `IntegralResidueComparisonInterface` remain byte-identical to the repository. The adopted `WeilConjectures` source tree is untouched.

The completed ten-file candidate compiles through `lcompile.py` on the official project server. The uncached repaired interface took 22.4 seconds, the restored item 6.7 seconds, and the adapted parent 8.4 seconds. The item also compiled in 3.7 seconds against the published unchanged support modules. No file limit or heartbeat limit is raised. The final 29-module suite passed on the official server, covering all 22 live downstream modules plus the repaired item, restored parent chain, and support modules. The final item compiled in 7.0 seconds and the consumer in 8.8 seconds (`dev/final-consumers-adapted.log`, exit 0). The delivery packet omits the three byte-identical support copies, leaving seven Lean files.

Restore `FiniteDiscreteCoefficientExchange` and `FiniteDiscreteExchangeRealization` byte-identically from quarantine, and adapt their parent `FiniteDiscreteExchangeComparison` to the proved original-total-arrow API. These prerequisites are needed to compile and restore the adapted consumer. Their declarations and dependency attachments remain intact.

## Proved and sorry left

This is a zero-hole repair. The archive has 0 sorries; the restored module has 0. Holes closed: 0. Holes added: 0. Split-off statements: 0. No sorry remains in any delivered Lean file. The existing `coefficientComparisonData_exchangeSteps` theorem is fully proved, and every new diagram equation, factorization, and generic comparison wrapper is fully proved.

## No longer needed

No public module or DAG node is withdrawn. No import module is pruned. All existing statement dependencies remain required, directly or through the new diagram API. The archived private helpers `transport_app`, `restricted_unit_hom`, `restricted_comp_hom`, `restricted_square_iso`, `restricted_square_hom`, `unit_step_hom`, `square_step_hom`, and `counit_step_hom` are unnecessary: the existing whole-exchange ambient identification replaces the repeated restricted-component conversions. The original public bounded-step APIs are preserved. The item's former direct proof edge to `def-weil-pbc-derived-exchange` is now through the typed etale-exchange node. The consumer's former direct edge to `lem-weil-pbc-three-step-arrow-comparison` is now through the diagram/comparison API. Both nodes remain transitively required; neither module is pruned.

## Where the brief, the DAG or earlier work was wrong

The quarantined item already had zero holes, but its repeated concrete derived-functor conversions did not satisfy the single-file compile limit. Profiling isolated endpoint conversion and the eta-expanded pullback-family argument of square coherence. Retaining endpoints and rewriting the equality of whole families before applying the abstract coherent-family theorem avoids those reductions. This repairs the assigned defect rather than closing a hole or weakening the statement. No protected unit route is bypassed, and no added hypothesis is used.

The definition change record `coord/changes/V5-coefficient-exchange-ambient-interface.md` lists all 22 current live downstream modules and the preserved quarantined parent chain. The one forced consumer adaptation is listed below; its module is unclaimed. Target signatures are unchanged; any target whose statement definitions reach the repaired predicate requires the usual independent semantic review.

## Forced adaptations

`Sheaf.Paper.FiniteDiscreteExchangeComparison` is unclaimed. Its original proof fails at line 190 with `Type mismatch`: `ExchangeChain.FactoredComparison.nonemptyArrowIso H` has the typed internal/etale chain Arrow objects, but the unchanged goal has the original `boundedConstructibleBaseChange` component and `F1.map (Etale.baseChange ...)` Arrow objects. Replace the two lines `obtain ⟨H⟩ := hsteps L hL; exact H.nonemptyArrowIso` by `exact finiteDiscreteExchangeSteps_arrowIso B ℓ k sq F0 F1 hsteps L hL`. The API proves equality of both entire Arrow objects, including endpoints, before returning the isomorphism. This resolves the original compiler error and preserves the public signature. A pre-existing 139-character conclusion line is wrapped without changing any token. The original failure is in `dev/parent-checks-server.log`; the passing adapted chain is in `dev/raw-arrow-interface.log`.

Its two prerequisites `FiniteDiscreteCoefficientExchange` and `FiniteDiscreteExchangeRealization` are unclaimed and restored byte-identically from quarantine, with no adapted lines. The comparison node's stale `lean.statement` still contained the encoding hypothesis discharged by E4; synchronize it with the already-correct archived Lean signature. This changes no mathematical statement or Lean signature.

## New nodes

All five nodes describe actual constructions and fully proved APIs; none introduces a hole:

- `def-weil-pbc-adjunction-exchange-chain`
- `def-weil-pbc-three-step-chain-comparison`
- `def-weil-pbc-ambient-typed-bounded-exchange`
- `def-weil-pbc-ambient-typed-etale-exchange`
- `def-weil-pbc-coefficient-exchange-diagram`

## Second reading by V5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
