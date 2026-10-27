## What changed

Prove `AlgebraicGeometry.ProEtale.AmbientClopen.UnderivedPasting.ambientUnderivedClopenPasting`
in `Sheaf.SixFunctors.AmbientUnderivedClopenPasting`, preserving every existing signature
and the public import.
The system horizontal predicate receives the definition representation repair described below.
The ordinary vertical and horizontal pasting equations follow
by normalizing the pasted arrows and applying the existing clopen uniqueness theorem.
The individual factor equations use naturality and the existing normalization equations.
The system pasting equations use the already proved ordinary-system pasting API.
Both identity cases use the specified adjoint identity comparisons and their unit equations.
All added proof helpers are private and proved. Proof-only imports add the source pullback
coherence, system pasting and semilinear compositor coherence modules. The DAG proof records
this route. The existing nodes `lem-sp-varying-ring-proper-open-pasting` and
`lem-sf-semilinear-compositor-coherence` are used as categorical tools from their
respective units: they supply ordinary-system pasting and identity compositor equations
already proved in Lean. No node of this unit supplies that published system API.
The maintainer's `tool_uses` approvals are left unchanged. The private pasting proofs
are parameterized by arbitrary finite rings and arbitrary coefficient sequences, and take
only normalization and uniqueness as hypotheses. The public theorem supplies those clauses
from the existing localization assertion. Local irreducibility and theorem-scoped instance
settings prevent elaboration from expanding chosen adjoints.

`Systems.HorizontalFactorData` packages the six categories and the fixed functors,
units, square comparisons and arrows used by horizontal factor restriction.
`Systems.horizontalFactorData` constructs every field directly from the existing system
operations. `Systems.HorizontalFactorData.factors` writes exactly the original two equations.
`Systems.Horizontal` folds its second conjunct through this package. Every original binder,
the first pasting equation and the other eight public definitions stay unchanged. The
representation avoids kernel expansion of chosen functors when comparing cached smallness
witnesses. Congruence and proof irrelevance identify the two constructed data records.
The three public data definitions are attached to the existing node. No new public theorem, axiom,
choice of data, foundational-module change, or downstream adaptation is introduced.
The change record includes both definitions verbatim and the consumer inventory.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.AmbientClopen.UnderivedPasting.ambientUnderivedClopenPasting`.
No holes added, none split off, and zero textual `sorry` remain in the delivered module.
The proof uses existing theorem statements; their outstanding dependencies remain their
own stage-3 items. This is a proof from existing declarations, not a decomposition.

## No longer needed

No existing import is removed, and no module is withdrawn. The proof does not invoke
`lem-sf-ambient-clopen-restriction-uniqueness` separately: normalization uniqueness is
already a clause of `lem-sf-ambient-exact-clopen-comparison-localization`.
It does not use `lem-sf-ambient-pullback-tensor-coherence` or its module
`Sheaf.Paper.AmbientPullbackTensorCoherence`: the existing source-library pullback
compositor identities suffice, without tensor comparisons. It does not invoke
`lem-coef-semilinear-derived-sections` separately: the system operations are already
constructed, and published ordinary-system pasting and coherence prove the needed equations.
These three nodes are removed from this item's direct proof dependencies; this makes no
claim that they are unused elsewhere in the library.

## Where the brief, the DAG or earlier work was wrong

The original plan is valid but asks for more general tensor and derived-system results
than the underived equations need. The existing ordinary-system pasting theorems provide
a shorter route for the two system pasting clauses. The ordinary argument still carries
out the planned unit normalization and uniqueness proof. The unit has no realized proof
step that this route bypasses. No statement is weakened.
The original literal `Systems.Horizontal` definition
causes kernel conversion to exceed the server stop, even though the normalization and
abstract calculation check. Its two factor equations now use the constructed data package.
This is a representation repair, with the same objects, units, arrows, equation order and
hypotheses. It therefore requires the definition-change semantic review described in
`coord/changes/ambient-underived-horizontal-factor-data.md`. A fresh read-only consumer
scan finds zero downstream Lean modules and only this item's internal uses. No module is
withdrawn and no target signature changes. The eight other public definitions were checked
against the checkout modulo whitespace. The revised module compiles in 16.0 seconds with
a reduced diagnostic heartbeat budget; the diagnostic setting is removed from the packet.
Validation: `lcompile.py --all` on the actual sandbox passes in 17.0 seconds at the
standard settings, with no errors or warnings. The delivered module has zero `sorry`.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
