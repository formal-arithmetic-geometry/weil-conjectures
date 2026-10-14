## What changed

Replaced the proof of `RingTensorCohomology.exists_balancedTensorUnitModelComparison`
without changing any existing signature, visibility, definition, or public import.
The proof composes an ordinary R-tensor comparison with a mixed-tensor homology
comparison, upgrades the additive equivalences to coefficient-linear isomorphisms
using each model's `cohomologyIso_smul`, and derives the localization-unit square
from naturality and the supplied pure-tensor formulas.

Added `Sheaf.Algebra.Homology.MixedTensorUnderlyingHomology`, fully proved:
Mathlib `cancelBaseChange` gives the degreewise isomorphism, `mapTotalIso` gives
the total chain comparison, nested tensor induction proves generator
extensionality, and exact-functor homology comparisons give the scalar and
cross-coefficient naturality equations. The private constructions contain no holes.
The iterated-homology comparison proof follows the existing private helpers in
`FlatIteratedScalarExtensionHomologySquare`; no existing module was changed.

Added `Sheaf.Algebra.Homology.UniversalBalancedTensorComparison`, isolating the
remaining natural K-flat computation over R. This statement involves only R, B,
F, ordinary tensor products and universal scalar extension. It has no A/Aq,
coefficient action, localization unit, theta, or mixed tensor. It is strictly the
first part of the argument, not a renaming or repackaging of the item.
Updated the original node's proof route and dependencies and supplied nodes for
both new modules. All three modules compile individually in import order through
lcompile.py, without warnings (observed approximately 30, 3 and 11 seconds).

## Proved and sorry left

Original hole closed by a reduction:
`RingTensorCohomology.exists_balancedTensorUnitModelComparison`
(node `new-lem-pc-balanced-tensor-unit-model-comparison`). Its entire assembly is
real Lean and has no local sorry.

New theorem proved without sorry:
`RingTensorCohomology.exists_mixedTensorUnderlyingHomology`
(node `new-lem-pc-mixed-tensor-underlying-homology`), including all private helpers.

One new hole remains:
`RingTensorCohomology.exists_universalBalancedTensorComparison`
(node `new-lem-pc-universal-balanced-tensor-comparison`), with the whole proof
`:= by sorry`. Its docstring gives the functorial K-flat tensor span, the counit
comparison, and both naturality arguments. This is a decomposition: one original
hole closed and one simpler hole added, net zero holes, not a complete
axiom-free proof of the original theorem yet.

## No longer needed

Removed these proof imports and their direct dependencies from the item's route:

- `Sheaf.Algebra.Homology.BalancedDerivedTensorModel`,
  node `lem-pc-balanced-derived-tensor-model`.
- `Sheaf.Algebra.Homology.DerivedTensorActionNaturality`,
  node `lem-pc-derived-tensor-action-naturality`.
- `Sheaf.Algebra.Homology.KFlatScalarExtensionCounit`,
  node `lem-pc-kflat-scalar-extension-counit`.

The counit lemma remains a planned dependency of the smaller universal-comparison
node, not an application in the parent assembly. BalancedDerivedTensorModel and
DerivedTensorActionNaturality are not needed by either new node's route.
No claim is made that these modules disappear from the entire targets' closure:
other modules can still import them. Existing public imports were retained.

The proof does not import MixedTensorRestrictionComparison or
TensorRestrictExtendScalarsModule: their existing signatures provide neither the
same factor order nor the generator equation across coefficient rings needed
here. Instead the proved comparison directly uses Mathlib's cancelBaseChange and
the existing total-complex API. These are search candidates, not removed imports.

## Where the brief, the DAG or earlier work was wrong

The original proof plan correctly specifies an R-K-flat resolution of the
underlying first factor, but its stated balanced-model and action-naturality
packages are expressed in derived categories of A-modules. The item assumes
derived categories only over R and B. Applying those packages directly would
require additional A/Aq derived-category instances and further universal-functor
identifications. The reduction avoids adding hypotheses: the universal step
works over R and B and the coefficient-linearity upgrade is proved in the item.

No statement was disputed or changed. The unit `sk-thm-picard-semicon` has empty
realized statement/step lists; the proof changes only this below-unit tensor
comparison and bypasses no realized unit node. Checked zero rings, zero complexes,
zero chain maps, identity coefficient maps, arbitrary integer degrees and
unbounded complexes. The mixed-tensor lemma imposes no flatness at all, and the
universal lemma retains precisely the K-flat/quasi-isomorphism assumptions on F.

Read Stacks Tags 064L and 06Y6 on their official pages because this checkout omits
literature sources. Mathlib searches were run through msearch.py and recorded
in searches.jsonl: LeanSearch was unavailable (HTTP 500), while LeanFinder,
Loogle and grep returned only infrastructure. Blueprint/DAG and library searches
found no existing theorem with either new statement and both required equations.

## New nodes

`new-lem-pc-universal-balanced-tensor-comparison` records the one remaining
natural additive comparison between universal scalar extension and tensoring
with the fixed K-flat resolution. Module:
`Sheaf.Algebra.Homology.UniversalBalancedTensorComparison`. Its statements and
proof sketch follow Tags 064L and 06Y6; all witnesses are existential in a theorem.

`new-lem-pc-mixed-tensor-underlying-homology` records the fully proved underlying
ordinary/mixed total-tensor homology comparison, its first-factor scalar identity,
and naturality for cross-coefficient maps specified on diagonal generators.
Module: `Sheaf.Algebra.Homology.MixedTensorUnderlyingHomology`. The actual
comparison is constructed from tensor and homology isomorphisms.

No change record is needed: existing interfaces and definitions are unchanged;
no consumer adaptations were made. The delivery adds only new statement modules
and changes the item's proof and proof-only imports.

## Second reading by N2

1. **Interfaces unchanged — pass.** Compared the existing delivered module against
   the repository with `diff -u`: only three proof-only imports and the theorem
   body changed. The original theorem header, visibility, docstring, definitions,
   and all public imports are byte-for-byte unchanged. The existing node changes
   only `proof`, `proof_deps`, and `proof_origin`; no change record is required.
2. **Proof and data — pass.** Independently compiled the three modules in import
   order through lcompile.py (30.1, 2.5, and 9.0 seconds before import cleanup).
   The sole local sorry is the public named theorem
   `RingTensorCohomology.exists_universalBalancedTensorComparison`, exactly
   `:= by sorry`. No forbidden declarations or hollow definitions occur. The mixed
   comparison's private definitions explicitly compose tensor, total-complex,
   and homology isomorphisms. Existential comparisons from the remaining theorem
   are eliminated inside the parent's proof, never used to define public data.
   Explicit `#print axioms` probes show only propext, Classical.choice, and
   Quot.sound for exists_mixedTensorUnderlyingHomology; the parent and universal
   comparison additionally show sorryAx, as expected from the remaining hole.
   The delivery tool's axiom probe additionally checks every declaration.
3. **New statements — pass.** Read both new signatures and their docstrings.
   The universal assertion is precisely ordinary R-tensor computation with two
   naturality equations; it omits the coefficient action and localization square
   which the parent proves, so it is a strict part of the argument. Its K-flat
   tensor span and universal counit construction follow Stacks
   [064L](https://stacks.math.columbia.edu/tag/064L) and
   [06Y6](https://stacks.math.columbia.edu/tag/06Y6), independently read online.
   Tested the mathematics at zero rings, zero complexes/maps, identity maps,
   B=R with F=R[0], and arbitrary integer degrees: no nonzero, boundedness, or
   extra flatness premise is needed. The mixed comparison is proved for all
   complexes and uses diagonal generators which span by balancing and coproduct
   extensionality. Independent LeanFinder, Loogle, msearch grep, and repository
   concept searches found infrastructure but no theorem with these full equations.
   Read MixedTensorRestrictionComparison and TensorRestrictExtendScalarsModule:
   neither supplies the cross-coefficient generator equation; the former also
   uses the opposite tensor order. The remaining universal proof requires a
   substantial natural tensor-span formalization, not a few-minute closure.
4. **Route and pruning — pass after import repair.** Checked the top-down
   assembly: ordinary comparison, mixed comparison, scalar-linearity upgrade,
   and finally the localization square. Every old direct proof dependency no
   longer used is named in `## No longer needed`. The counit remains needed by
   the universal subproblem. The unit's `realized` record is
   `{"statement": [], "steps": [[]]}`; no realized node is bypassed.
   Removed four redundant direct public Mathlib imports from the new universal
   module (Symmetric, Bifunctor, HomologySequence, LeftDerived), whose APIs are
   already exposed by its statement imports. Added the missing proof-only
   KFlatScalarExtensionCounit import required by the remaining node's plan.
5. **DAG agreement — pass.** Checked proof steps, dependency unions, origins,
   sources, created/blueprint records, module/declaration paths, and new Lean
   signatures. The parent records its actual reduction. The mixed node records
   cancelBaseChange, totalization, generator extensionality and exact-functor
   homology naturality. The universal node records its remaining tensor-span
   proof and counit dependency. Existing statement fields were not altered.

Second reading changed only the universal module's imports and this report.
The original hole is closed by a reduction, with one simpler hole added: net
zero holes. The fully proved new mixed comparison introduces no holes.
