## What changed

Reduced `MvPowerSeries.formalFiber_polynomial_degreePPresentation` to two construction
components sharing the specified coefficient `a : M` with `z^p = a`. The quotient
component states ordinary base change of a simple degree-p field extension, for any
commutative base algebra. The derivation component retains the finite-model,
completion, and localization argument. Both new modules have source citations,
complete proof docstrings, and matching nodes. The upper signature is unchanged.
Updated the upper node to match this proof and removed unused proof imports.
Added proof-only `import all Mathlib.RingTheory.OreLocalization.Basic` and
`import all Mathlib.Algebra.MonoidAlgebra.Defs` so instance comparisons can unfold
their underlying non-exposed operations. A scoped heartbeat increase is needed for
the nested formal-fibre ring instances; the single-file wall-clock limit is unchanged.

Validation: both component modules and the upper module compile locally. The dry run
printed OK, with only the second reading outstanding and nothing pushed. On the
first successful dry run, the upper module's appended axiom probe exceeded the
60-second limit; deliver3.py records this and permits the dry run, with the merge
running the probe again. Both component probes ran without a prohibited-axiom report.
To reduce elaboration cost, the quotient component uses an intermediate field M
of L rather than separate abstract field and scalar-tower parameters; this preserves
its arbitrary-base-algebra generality. The three-module compile then passed, with
the upper module taking 21.1 seconds. The default 200000-heartbeat limit still fails,
so the documented scoped increase is retained.
The upper proof only combines the two named component theorems; no target signature,
definition, or existing visibility changed.

## Proved and sorry left

One upper hole closed by decomposition:
`MvPowerSeries.formalFiber_polynomial_degreePPresentation`
(node `lem-weil-pbc-power-series-polynomial-degree-p-presentation`).
No sorry remains in the item. Two holes added, each strictly one component:

- `MvPowerSeries.FormalFiberDegreePDerivation`
  (`new-lem-weil-pbc-degree-p-derivation-component`).
- `MvPowerSeries.FormalFiberDegreePQuotient`
  (`new-lem-weil-pbc-degree-p-quotient-component`).

This is a decomposition, not a proof free of sorry dependencies: one hole closed,
two added. Neither component assumes the conclusion of the other. Their common
coefficient is fixed by the actual equation `z^p = a`; no arbitrary data is defined
from an unproved existence theorem. Edge cases checked: p is prime, so p > 1;
zero-dimensional power-series or polynomial rings are allowed, and both component
arguments permit a zero formal fibre.

## No longer needed

Removed the following imports from the item:
`Sheaf.RingTheory.FiniteSubalgebraFractionField`,
`Sheaf.RingTheory.CompletionFiniteExtension`,
`Sheaf.RingTheory.CompletionFiniteQuotient`,
`Sheaf.RingTheory.Derivation.CompletionAndLocalization`,
`Sheaf.RingTheory.Derivation.DetectNonPthPower`,
`Sheaf.RingTheory.PurelyInseparableIntegralPrimeUnique`,
`Sheaf.RingTheory.RadicialPrimeUniqueDegreeP`,
`Sheaf.RingTheory.RegularRingNormal`,
`Sheaf.RingTheory.PowerSeriesFieldCohenRegularComplete`, and
`Sheaf.RingTheory.RegularLocalLocalization`.
The finite-model and derivation dependencies are retained in the new derivation
node's plan and imported privately by its module; removing their direct upper imports does not establish their global
unreachability. The route no longer needs nodes
`lem-weil-pbc-completion-finite-quotient`,
`lem-weil-pbc-radicial-prime-unique-degree-p`,
`lem-weil-pbc-monic-quotient-free`, and
`lem-weil-pbc-localization-noetherian`: quotient base change is done over the fields
before any completion comparison. Their corresponding Sheaf modules are
`Sheaf.RingTheory.CompletionFiniteQuotient` and
`Sheaf.RingTheory.RadicialPrimeUniqueDegreeP`; the other two are Mathlib leaves.
No claim is made about other consumers of these modules.

All fourteen old upper `proof_deps` are absent from the new upper proof. In addition
to the four discarded dependencies listed above, these ten move to the derivation
component's plan (and their modules stay reachable through its proof imports):
`lem-weil-pbc-power-series-field-cohen-regular-complete`,
`lem-weil-pbc-regular-local-localization`, `lem-weil-pbc-regular-ring-normal`,
`lem-weil-pbc-normal-domain-of-local-normal`,
`lem-weil-pbc-finite-subalgebra-fraction-field`,
`lem-weil-pbc-finite-algebra-noetherian`,
`lem-weil-pbc-purely-inseparable-integral-prime-unique`,
`lem-weil-pbc-completion-finite-extension`,
`lem-weil-pbc-derivation-nonzero-on-non-pth-power`, and
`lem-weil-pbc-derivation-extends`.
Removed the new derivation module's unused public Polynomial.Basic import.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox quotient component claimed the presentation for every
coefficient with unit derivative, with no relation to the field extension. That
claim was unjustified and potentially false; it has been replaced before delivery
by the specified-coefficient field base-change statement. The earlier component
nodes copied the full upper statement, had empty proof plans and placeholder Lean
signatures, and the modules lacked required docstrings. These have been repaired.
The report previously claimed a private finite-degree helper that was absent; that
claim has been removed. No existing library statement or definition was changed.
The unit route is unchanged; neither new component realizes a different unit step.

## New nodes

`new-lem-weil-pbc-degree-p-derivation-component`: detects `a tensor 1` by extending
a derivation from a finite model and undoing multiplication by a pth power.
Module `Sheaf.RingTheory.FormalFiberDegreePDerivation`.

`new-lem-weil-pbc-degree-p-quotient-component`: base changes the presentation of
L as M[Z]/(Z^p-a), independently of derivations and completion.
Module `Sheaf.RingTheory.FormalFiberDegreePQuotient`.
No change record is needed: existing public signatures and public imports are unchanged.

## Second reading by J2

1. Compared the delivered upper module with the read-only repository using diff
   and checked its theorem signature byte for byte: identical. No existing
   definition, visibility, target statement, or public import changed. The only
   existing node fields changed are proof, proof_deps, and proof_origin. Verdict: pass.
2. Compiled all three delivered modules in import order through lcompile.py, with
   no errors or warnings. Scanned all delivered Lean: precisely two sorries, each
   the full proof of a listed named component theorem; no prohibited declarations
   or hollow definitions. Scratch copies with explicit #print axioms for all three
   declarations show only propext, Classical.choice, Quot.sound, and sorryAx.
   The upper proof combines two components at the same specified coefficient;
   destructing hpow is inside a theorem proof, not a data definition. Verdict: pass
   as a decomposition, not an axiom-clean completed proof.
3. Read both complete component statements, docstrings and nodes against Stacks
   Tags 07PR, 07PH and 07PE (the local Stacks source is absent on this machine;
   read the official pages). The derivation component omits the quotient conclusion;
   the quotient component requires no completion, derivation or characteristic-p
   hypothesis. Neither restates the upper theorem. The non-pth-power contradiction
   uses Frobenius injectivity and p > 1; denominator clearing by s^p preserves it
   and transports the unit derivative back to the original a. In the quotient
   component, finrank = p > 0 implies finite dimensionality even without an explicit
   instance, and generation forces the minimal polynomial to have degree p.
   Checked n=m=0, q=0, a=0, z in M, M=L, zero base algebra, and the characteristic
   different from p case of the quotient component: no false edge case. Repeated
   leanfinder, loogle and grep searches with different terms, and searched both
   library roots. Found the standard Mathlib constituents, no full duplicate.
   Closing either component requires substantial construction beyond a short
   application; left both documented holes. Verdict: true, needed, strictly smaller.
4. Read the old proof plan, its dependency declarations and sk-thm-p1 realized
   record. The upper reduction is a direct conjunction of the specified-coefficient
   derivation and ordinary field-presentation base change. The finite-model route
   remains in the derivation component and is now imported there. All fourteen
   previous direct upper dependencies are accounted for under No longer needed;
   ten move to the component and four are discarded by the shorter quotient route.
   Neither the parent nor the new components is a realized unit step, and no unit
   route or record changes. Public imports serve statement notation/instances;
   proof-only imports are private. Verdict: pass after import/report repair.
5. Checked the upper node against the actual two component applications; checked
   new node ids, chapter/unit, source, created, blueprint ancestry, search records,
   complete Lean signatures, and proof-step dependency unions. The upper node's
   statement and Lean record remain unchanged. Updated new signatures to the
   verbatim multiline Lean signatures and added this reader's actual searches.
   Verdict: pass.

Second reading changed: added private derivation-plan dependency imports, removed
its unused public Polynomial.Basic import, replaced the upper theorem's old-route
proof docstring with its actual reduction, completed the direct dependency pruning
inventory, and made new-node signatures/search evidence exact. No theorem statement
or proof body changed. Local compile and explicit axiom probes passed; final
lcompile/preflight validation is performed by deliver3.py.
