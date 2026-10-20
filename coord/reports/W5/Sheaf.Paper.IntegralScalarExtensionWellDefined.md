## What changed

Proved `WeilConjectures.integralScalarTransition_existsUnique` in
`Sheaf.Paper.IntegralScalarExtensionWellDefined`.

The proof first checks compatibility of the constant quotient-sheaf maps and hence
of the maps `integralScalarRho`. It reuses the proved balanced tensor map from
`Sheaf.Paper.IntegralReductionTowerUnrestricted`, via a private proof import with
`import all`. A private lemma for arbitrary ring sheaves restricts that map along
the commuting triangle from the target completion. This separates balancing over
the source completion from linearity over the target completion, including ramified
extensions. Equality transports identify the ordinary change-of-rings construction
with the recorded scalar-extension functors. Tensor generators prove naturality
and uniqueness after sheafification. The natural module maps assemble degreewise
into the required natural transformation on complexes.

Only private helpers and a theorem proof were added. The conservative static
preflight requested a visibility change record for the additional scoped commands;
it is `coord/changes/W5-integral-scalar-tower-transition.md`. The record lists all
transitive importers and explains why no consumer adaptation is needed. Existing public statements,
public imports, and definitions are unchanged. The argument implements the tensor
transition part of step 1 of the existing node's proof; there is no replacement
route or new intermediate obligation.

The entire module compiled through `lcompile.py` in 34.6 seconds. A separate
`#print axioms WeilConjectures.integralScalarTransition_existsUnique` check reported
exactly `propext`, `Classical.choice`, and `Quot.sound`. Explicit universes and a
section-scoped dependent-type transparency option keep elaboration below the
60-second limit. No compilation limit was increased.

## Proved and sorry left

Original holes: 2. Closed: 1. Added: 0. Remaining: 1. Split off: 0.

Closed: `WeilConjectures.integralScalarTransition_existsUnique`.

Remaining, unchanged: `WeilConjectures.integralScalarExtensionWellDefined`, attached
to `lem-weil-integral-scalar-extension-well-defined`. Its outstanding assertions are
quasi-isomorphism invariance, derived descent with additive and shift structures,
comparison uniqueness, derived-limit values, and scalar compatibility. Its original
source and complete proof plan remain in its docstring and DAG node. This is a
partial delivery under the brief's rule permitting one hole of a multi-hole module
to be proved while another remains untouched.

## No longer needed

No node or module is pruned. The remaining main theorem still needs its declared
proof dependencies. Removed only a duplicate private import line for
`WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`; another import
of that same module remains. No source-library declaration was removed or changed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or proof-plan error was found. The source and target
completed coefficient sheaves must be kept distinct when restricting the tensor
transition. The existing tensor-map implementation already supplies the balanced
map; the new private triangle helper supplies its target-completion linearity.
Concrete inference initially unfolded the completed coefficient constructions too
far. Explicit coefficient universes, generic scalar-linearity, and the scoped
transparency setting resolved that elaboration issue without an interface repair.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
