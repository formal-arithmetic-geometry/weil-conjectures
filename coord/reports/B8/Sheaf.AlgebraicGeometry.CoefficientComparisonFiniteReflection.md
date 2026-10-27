## What changed

Repair of the return on delivery cac3512f25f: the current main branch now
contains the newer 56-line module shell created by the
`CoefficientComparisonConstructibilityTest` landing (base 28ff0332d, commit
b45c99619c5). The retained B8 proof was merged into that current shell: the
public import, theorem signature, namespace and statement remain exactly the
current source version, while the proof-only imports, explicit sheafification
instances and completed cover-reflection argument are restored. The universe
`w` required by those local instances is declared explicitly. This is a
substantive proof repair, not a rebase or unchanged re-push.

The parent node `lem-pe-coefficient-comparison-constructibility-test` now
imports this item directly, so the current shell and its proof dependency are
compiled together. The complete theorem, its private cover-reflection proof and
its new chart-reflection dependency are delivered together. The delivery is
rebuilt against the current main branch rather than reusing the old base.

Replaced the proof hole of
`AlgebraicGeometry.ProEtale.coefficientComparison_finite_reflect` by an assembly
from the existing coefficient-sized etale-chart theorem and reflection of a single
constant chart. The statement, public imports and definitions of the item remain
unchanged. Added proof imports of `CoefficientFpLocalSystemEtaleCover` and
`CoefficientComparisonConstantChartReflection`, plus Mathlib's induced-topology
instances for the transported site equivalence.

The argument explicitly upgrades each finite model to finite presentation,
extracts the etale chart family, reflects its covering property, and restricts
its constant charts to each arrow of `Sieve.ofObjects V W` for arbitrary W.
The private helper `comparison_coversTop_reflect` proves cover reflection:
transport the covering sieve down, use a generating pro-etale precover to obtain
joint surjectivity, apply the etale covering criterion, then transport back.
This topology argument has no deferred proof.

The new module states only reflection of one constant chart with its specified
module. It has no finite-generation, finite-presentation, Noetherianity,
local-constancy or covering assumptions. It is the local full-faithfulness part
of the argument, rather than a renamed finite-local-system reflection theorem.
Its statement imports only `ProEtaleSmallModelComparison`, avoiding the unrelated
constructible/local-system definitions in `CoefficientConstructibleEtaleModules`.
Updated the parent node's proof route and added the helper's node.

## Proved and sorry left

Closed the item's one direct hole:
`AlgebraicGeometry.ProEtale.coefficientComparison_finite_reflect`
(node `lem-pe-coefficient-comparison-finite-reflection`).

Added one direct hole, as the whole proof of the public theorem
`AlgebraicGeometry.ProEtale.coefficientComparison_constant_over_reflect`
(node `lem-pe-coefficient-comparison-constant-chart-reflection`). Its source,
complete proof in words, edge cases and coefficient-universe argument are in
its docstring and node. No other declaration in the packet contains a hole.
No definition contains a hole.

Validation of the original packet: `lcompile.py --all` compiled without
errors or warnings: ConstantChartReflection 8.4 seconds, FiniteReflection
13.4 seconds. Repair validation after merging the current shell: `lcompile.py --all`
compiled without errors or warnings: ConstantChartReflection 7.5 seconds,
FiniteReflection 13.3 seconds. The current theorem signature is byte-for-byte
identical to main and all delivered files remain within 100 columns. All imports have current sources; the original signature and
Lean attachment are unchanged, and the 328-node dependency closure is acyclic. The original theorem statement is byte-for-byte unchanged.
The overlaid dependency closure contains 328 nodes and no cycle.

This is a decomposition: one old hole closed, one strictly smaller hole added,
net zero new holes. The existing
`AlgebraicGeometry.ProEtale.coefficientFpLocalSystem_etaleCover` is used unchanged;
its proof remains a separate existing item, not a new split in this delivery.

## No longer needed

No original import is removed, and no module is withdrawn. The original public
import supplies the statement interface; the filtered-colimit import supplies
its explicit sheafification instances.

The parent no longer directly needs `det-pe-finite-local-systems-twist` or
`Sheaf.AlgebraicGeometry.ProEtaleFiniteLocalSystemsTwist`: the coefficient-sized
etale-cover theorem gives precisely the charts needed, without the ULift-only
interface or the other conclusions of that larger theorem. The finite-model
and torsor mathematics remains needed below that existing chart theorem.

The parent no longer directly needs `det-pe-classical-sheaves-modules` or
`Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules`. Only reflection of a
specified constant chart is needed. Its node records a coefficient-sized unit
argument using the existing affine-presentation sheafification theorem.
The original-site classicality predicate, exactness assertions and global
essential-image characterization are not used here. Those declarations and
all source-library declarations remain in the library.

The Noetherian finite-presentation leaf and site-comparison dependency remain.
The unit's finite-local-system route is preserved; this delivery makes no
claim that an entire blueprint unit or a whole library module is pruned.

## Where the brief, the DAG or earlier work was wrong

The stated plan correctly identifies the mathematics but its two large
comparison interfaces are not directly instantiable: finiteLocalSystemsTwist
uses a ring in the scheme universe followed by ULift, and the classical module
theorem fixes the module universe to u+1. The item allows an arbitrary ring in
max(v,u+1). Existing coefficientFpLocalSystem_etaleCover already states the
independently sized torsor/chart step, so that step is reused rather than
restated. The remaining new interface concerns exactly one constant chart.

Cover reflection requires only joint surjectivity of a genuine pro-etale
precover, not the false assertion that every jointly surjective pro-etale
family is a pro-etale covering. The proof uses the etale covering criterion
only after obtaining an etale family. It does not assume a nonempty base,
a nonempty covering family, nonzero coefficients or a nonzero model.

Edge cases checked against the statements and argument: empty X and empty
covers; empty individual charts; the zero ring and zero module; infinite
Noetherian rings such as the integers; arbitrarily large coefficient universes;
and non-quasi-compact schemes. No added hypothesis excludes these cases.

## New nodes

`lem-pe-coefficient-comparison-constant-chart-reflection`, in
`dag/nodes/sec-proetale-coefficients/`, states descent of a specified constant
module chart over one etale object. Source: Stacks Tags 099T and 099Y,
localization of comparison full faithfulness. Its planned proof uses the
existing coefficient-sized affine-presentation sheafification theorem to
establish the unit in the required universe, the slice-site equivalences,
constant-sheaf adjunctions and reflection of isomorphisms by full faithfulness.
LeanFinder, Loogle, LeanSearch and local repository/Mathlib searches found no
exact theorem with this interface. No existing statement, definition or
consumer interface is changed, so no change record or forced adaptation is
required.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
