## What changed

Proved `WeilConjectures.point_tor_amplitude_realization` without changing its statement or any existing definition. The proof constructs the finite free model in the specified interval, identifies the signed dual complex degree by degree, and proves both perfectness assertions, finiteness of dual cohomology, and the reversed dual Tor interval.

Added the proved theorem `WeilConjectures.point_sections_torAmplitude` in `Sheaf.Paper.PointSectionsTorAmplitude`. It transfers the intrinsic Tor interval through realization, a bounded flat model, and exact point sections. Its private flatness argument identifies final-object evaluation with the geometric stalk using the initial pointed final neighbourhood. There is no equivalence assertion between all point sheaves and ordinary modules.

Private helpers in the item prove the single-target Hom coordinates and differential, finite cohomology of a bounded finite-term model over a finite ring, and perfectness from a finite free model. Proof imports supply the generic Noetherian pseudo-coherence criterion and finite-Tor perfectness theorem at the actual lifted coefficient and module universes. The existing node's proof route and dependencies now describe this argument. No source-library file or consumer is changed.

## Proved and sorry left

Closed the item's one hole: `WeilConjectures.point_tor_amplitude_realization` (`lem-sf-point-tor-amplitude-realization`).

Added zero holes. The new `WeilConjectures.point_sections_torAmplitude` (`lem-sf-point-sections-tor-amplitude`) is proved. No `sorry` remains in either delivered Lean file. The proof uses existing declared dependencies as this stage requires; it does not claim those dependencies are themselves free of axioms from unfinished proofs.

## No longer needed

Removed direct proof imports `Sheaf.SixFunctors.PointRingedEvaluationModel`, `Sheaf.CategoryTheory.DerivedCategory.FiniteTorAmplitudePerfect`, `Sheaf.Paper.PointProEtaleSectionsExact`, `Sheaf.Paper.PointSectionsFiniteness`, and `Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk`. Replaced `Mathlib.RingTheory.Noetherian.Defs` with `Mathlib.RingTheory.Noetherian.Basic`; removed the redundant `Mathlib.Algebra.Module.Projective` import, whose declarations are already public statement dependencies.

The direct proof route no longer uses `lem-sf-point-ringed-evaluation-model` (bounded flat models replace its arbitrary derived tensor comparison), `lem-trf-finite-tor-amplitude-perfect` (the coefficient-specific theorem has the wrong module universe; its generic pseudo-coherence ingredients apply), `lem-weil-point-proetale-sections-exact` (exactness is already supplied by the recorded sections functor), `lem-weil-point-sections-finiteness` (the finite fibre codomain already supplies this property), `lem-weil-proetale-constant-sheaf-stalk` (no constant test-sheaf tensor argument is needed), or `lem-weil-valued-dvr-finite-quotients` (use the coefficient construction's finite-ring theorem). Removed exactly these six obsolete entries from the existing node's `tool_uses`, preserving the order of the others.

These are direct-dependency removals, not module withdrawals: some remain required transitively by public interfaces or other proofs. No module is deleted, and no adopted source declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The planned use of `finiteTorAmplitude_iff_perfect_iff_finiteFree` cannot be applied directly to the recorded fibre: its modules are in universe u over the unlifted coefficient ring, whereas the fibre uses modules in u+1 over ULift coefficients. The generic pseudo-coherence and finite-Tor perfectness declarations solve precisely this mismatch while retaining the planned intermediate bounded finite-term model before the interval-controlled free model.

The finite-cohomology clause is already in the finite fibre's codomain. Reproving it from constructibility is unnecessary. The Tor transfer is proved from bounded flat models and geometric stalk flatness, so it does not need the proposed arbitrary tensor-evaluation comparison. The unit's point-perfectness/free-model/dual route is retained.

## New nodes

`lem-sf-point-sections-tor-amplitude`, in `dag/nodes/sec-six-functors/lem-sf-point-sections-tor-amplitude.json`, records the proved, strictly smaller Tor-transfer assertion. It has three kinds of logged Mathlib search and the latest blueprint Step 1 source. Its statement permits arbitrary complexes and arbitrary module tests, with finite coefficient ring as required by the intrinsic realization interface. There are no split-off holes and no definition or statement change records. Edge-case reading checks zero objects, zero ranks, and a=b: the cochain coordinate equivalence and interval bounds apply unchanged. The new lemma also permits the zero coefficient ring; its argument uses flatness and equivalences and never assumes nontriviality. The positive-level coefficient quotient in the main theorem is shown nontrivial before installing its local-ring instance. Existing theorem docstrings are preserved; the revised node and new lemma docstring describe the implemented flat-model route.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
