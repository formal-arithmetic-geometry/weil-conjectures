## What changed

Proved `FrobeniusModule.mixedOfWeightsAtMost_stability` in
`Sheaf.Paper.MixedWeightsStability`, preserving its entire statement and universes.
The injective clause identifies the source with the stable image modulo zero;
the surjective clause uses the whole space modulo the stable kernel and the
first isomorphism theorem. Both use the existing mixed-subquotient theorem.
The extension clause applies the existing mixed short-exact-sequence theorem.
A left inverse makes a split inclusion injective, giving the last clause.

Four proved private helpers provide stable images, stable kernels, invariance
under equivariant linear equivalence, and the injective-map clause. The invariance
helper applies the extension theorem to a sequence starting with the zero module,
whose mixedness is constructed using a length-zero filtration. No complement,
semisimplicity, or same-universe restriction is introduced.

Added the proof import `Mathlib.LinearAlgebra.Isomorphisms`; updated the node's
proof and proof dependencies to the actual argument. The existing public imports
retain the module's established reexports, including the four existing sheaf
stability declarations. No public signature or definition changes.

Verification: the complete file compiled cleanly through `lcompile.py`. The
explicit zero-module construction handles the empty-filtration case, and the
image/kernel arguments use only invertibility of Frobenius, including zero
sources, zero targets and nonsemisimple actions. Searches ran through `msearch.py`
(LeanFinder, Loogle and grep) and local `rg`; no shorter exact match for the
finite-filtration predicate was found. The upstream `HasWeightsAtMost` map lemmas
use a different spectral predicate; the declared mixedness dependencies fit.

## Proved and sorry left

Closed 1 of 1 original holes:
`FrobeniusModule.mixedOfWeightsAtMost_stability`
(node `lem-a1-mixed-direct-summand`). Added 0 holes; split off 0 statements.
No `sorry` remains in the delivered module or its private helpers.

The proof uses the pre-existing declarations
`FrobeniusModule.IsMixedOfWeightsAtMost.subquotient`
(node `lem-a1-subquotient-extension-bounds`) and
`FrobeniusModule.IsMixedOfWeightsAtMost.of_shortExact`
(node `lem-a1-extension-bounds`). Their existing holes are unchanged and are not
claimed as proved by this delivery.

## No longer needed

Removed the unused proof import `Sheaf.Paper.AdicPunctualWeights`. Removed
`def-weil-punctual-weights` and `def-weil-weil-sheaf-complex` from this node's
proof dependencies: the sheaf clauses already exist in the public upstream
import, while the new proof concerns only Frobenius modules. Both remain
statement dependencies and are not claimed globally unnecessary.

No declared Frobenius proof dependency was pruned: both
`lem-a1-subquotient-extension-bounds` /
`Sheaf.LinearAlgebra.FrobeniusModuleMixedSubquotient` and
`lem-a1-extension-bounds` /
`Sheaf.LinearAlgebra.FrobeniusModuleExtensionBounds` are used.
No module is withdrawn and no further DAG node is made unnecessary.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The subquotient dependency
is formulated for a concrete nested-subspace quotient, rather than an arbitrary
equivariant injection or surjection; the proved image/kernel equivalences and
zero-extension argument supply that glue. The original planned route is kept.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
