## What changed

Replaced the body of `WeilConjectures.IntegralDualExceptionalSystem.integralDualExceptionalSystem`
with the actual categorical assembly. All existing public statements and definitions are unchanged.
The proof establishes the normalized finite-Tor domain of reductions, dual-comparison naturality
and evaluation, and actual completed-pullback counit invertibility. It builds q and b as natural
isomorphisms from their specified composites, proves their component identities, derives the
finite exceptional formula from theta.finiteFormula and fiber_naturality, and combines the two
single-dual Tor bounds with preservation by pullback. Private proved helpers implement the
reduction-domain and dual-comparison calculations.

Two new public theorems in separate modules isolate the independent remaining geometric
arguments: integral duality for the actual dualizing-system limit, and preservation by the
actual total-limit completed system pullback. Both have individual nodes, sources, complete
proof plans, and whole-proof sorry bodies. The parent node now records the Lean assembly.
No source-library declarations, target statements, or definitions were changed.
All three delivered modules compiled through lcompile.py. The item compiled in 32.9 seconds;
two formatting warnings were then removed. Delivery performs its own final compile and axiom
preflight for the full packet.

## Proved and sorry left

Closed the direct hole of
`WeilConjectures.IntegralDualExceptionalSystem.integralDualExceptionalSystem` (1 original hole).
The item now contains zero direct sorries. Added two holes:

- `WeilConjectures.integralSystemDualityCompatibility`, node
  `lem-coef-integral-system-duality-compatibility`.
- `WeilConjectures.completedSystemPullbackPreservation`, node
  `lem-coef-completed-system-pullback-preservation`.

This is a decomposition: one upper hole closed, two lower holes added, net minus one.
It is not a completed proof of the underlying geometric assertions. The combination of the
parts is a real Lean proof, including construction and naturality of both system isomorphisms,
their specified finite evaluation, and endpoint arithmetic. Each remaining theorem is strictly
simpler: the pullback theorem has no duality or exceptional operation, and the duality theorem
involves one scheme and no relative pullback or exceptional comparison. No data is chosen from
an arbitrary unproved existence assertion.

## No longer needed

Removed the item's direct proof imports:
`Sheaf.Paper.CoefficientSystemDerivedComparison`,
`Sheaf.Paper.IntegralOperationsPreserveConstructible`,
`Sheaf.Paper.PullbackTorAmplitude`,
`Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`, and
`Sheaf.SixFunctors.IntegralVerdier`.
Their work is still needed by the two split-off lemmas, so no module or mathematical node is
claimed globally pruned. The original direct proof dependencies
`lem-pur-coefficient-system-derived-comparison`,
`lem-pur-integral-operations-preserve-constructible`, `lem-sf-pullback-tor-amplitude`,
`lem-weil-l-adic-extension-integers-dvr`, `lem-weil-l-adic-extension-complete`,
`prop-coef-integral-dualizing`, and `thm-coef-integral-verdier` move below the two new nodes.
All public imports are retained. No Lean module is withdrawn and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is mathematically retained. Two presentation bridges require separate
formal arguments: the arbitrary specified calculus reduction/limit must be related to the
concrete completed-pullback model, and the actual limit of a DualizingOperation must be related
to the integral Verdier input with its prescribed reduction maps. IntegralVerdier's conclusion
and IntegralPullbackSystemComparison do not directly have those signatures. The new lemmas
state these genuine steps without assuming any part of q, b, naturality, finite exceptional
comparison, or the double-dual conclusion.

The zero-complex, empty-scheme, identity/point, degenerate-interval, and nonnegative integer
dimension-bound cases were checked in the statements and informal arguments. The bound is
computed as [-b-2dY,-a] followed by [a-2dX,b+2dY]. Positive coefficients remain indexed by n+1.
The actual adjunction counits and theta are used, so no assertion of equality of derived maps
is inferred merely from their independent finite evaluations.

## New nodes

`lem-coef-integral-system-duality-compatibility` in
`dag/nodes/sec-six-functors/lem-coef-integral-system-duality-compatibility.json` states
preservation, invertibility of the evaluation-defined system dual comparison, and the one-dual
Tor bound for the specified normalized dualizing limit. Its source is the current blueprint's
integral Verdier proof; its proof uses normalized reconstruction, the integral dualizing
presentation, and integral Verdier duality with the evaluation calculus.

`lem-coef-completed-system-pullback-preservation` in
`dag/nodes/sec-six-functors/lem-coef-completed-system-pullback-preservation.json` states
constructibility, normalization, and preservation of the same Tor interval for total-limit
pullback. Its source is Bhatt--Scholze, Lemma 6.5.9(4)-(5), printed pages 50-51, with the
parent's original proof steps 2-4. It needs coefficient-system compatibility, the completed
pullback preservation theorem, actual reconstruction, and finite pullback Tor preservation.

No interface or definition change record is needed: the existing interface is unchanged,
and the only new declarations are the two split-off statements with their own modules/nodes.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
