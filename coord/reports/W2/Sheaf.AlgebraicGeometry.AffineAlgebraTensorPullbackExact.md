## What changed

Replaced the sorry in `AlgebraicGeometry.affine_algebra_tensorModulePullback_exact`
with a complete Lean reduction, preserving its signature and existing docstring.
The specified object and morphism equalities construct a natural isomorphism to
`RingedSpace.exists_tensorModulePullback`'s additive left adjoint. This proves
finite-colimit preservation without any new obligation. Kernel preservation follows
from the two new intermediate statements, and Mathlib's
`Functor.preservesFiniteLimits_of_preservesKernels` supplies finite limits.
All three modules compile cleanly with lcompile.py.

The two new modules separate the affine geometric stalk calculation from the
kernel part of the general flat ringed-space tensor-pullback argument. They are
strict parts of the argument: neither asserts both finite limits and finite
colimits, and the general kernel theorem requires independent stalk flatness and
additivity. No definition, existing statement, or target changed.
The unit record has empty realized lists; the finite-duality/affine-equivalence
route is retained. Sources read: Stacks Tags 0AVW and 02N4 online; the referenced
local Stacks .tex files are absent on this machine.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.affine_algebra_tensorModulePullback_exact`
(node `lem-sc-affine-algebra-tensor-pullback-exact`). No sorry remains in the item's module.
This is a decomposition, not a complete proof of the transitive obligations.
Added two holes, each exactly a named public theorem with `:= by sorry`:

- `AlgebraicGeometry.affine_algebra_stalkMap_flat`
  (`lem-sc-affine-algebra-stalk-flat`).
- `AlgebraicGeometry.RingedSpace.stalkFlat_tensorModulePullback_preservesKernels`
  (`lem-sc-stalk-flat-tensor-pullback-kernels`).

Thus one hole is closed and two are added (net -1 before any closure-wide pruning).
The new statements were checked on empty source spaces, zero stalk rings/modules,
and arbitrary module sheaves; no quasi-coherence or boundedness assumption is used.
The empty-source stalk condition is vacuous and its module category is trivial;
localizations at primes and flat scalar extension handle the other cases.

## No longer needed

Removed the item's direct proof import `Sheaf.Algebra.Homology.ModuleStalkExact`.
The main theorem no longer directly uses `lem-weil-pbc-module-stalk-exact` or
`lem-weil-pbc-flat-tensor-exact`; both remain needed below the new general kernel
node, so neither node or module is claimed pruned from the targets' closure.
No entire module or node is pruned. All original public imports remain because
the existing signature needs their declarations.
The general kernel module uses `Sheaf.Paper.DerivedHomMayerVietoris` for
`moduleRings`, avoiding an unnecessary public derived-direct-image import.

## Where the brief, the DAG or earlier work was wrong

The original DAG step 1 has no dependencies and hides the entire affine
pushforward-stalk localization calculation. Step 2 additionally needs the natural
inverse-image and change-of-rings stalk comparisons; flat tensor exactness alone
does not identify the tensor construction's scalar map. These are mathematical
gaps in the stated plan, now made into named nodes with complete proof descriptions.
The existing `FlatModulePullbackExact` is only for scheme morphisms and cannot be
applied to the canonical morphism to the direct-image algebra, whose codomain is
only a ringed space. This does not dispute the original theorem.

Searches ran through msearch.py (LeanFinder, Loogle, grep, LeanSearch) and direct
source searches in Mathlib, Sheaf and WeilConjectures. LeanSearch returned an
Internal Server Error. Useful partial matches were
`ModuleCat.preservesFiniteLimits_extendScalars_of_flat`,
`StructureSheaf.isLocalizedModule_toPushforwardStalkAlgHom`, and the existing
`RingedSpace.exists_tensorModulePullback`; none states either new theorem.
Blueprint searches for flat pullback and direct image algebra found no duplicate.

## New nodes

`lem-sc-affine-algebra-stalk-flat`, in
`dag/nodes/sec-picard-framework/lem-sc-affine-algebra-stalk-flat.json`,
is stated in `Sheaf.AlgebraicGeometry.AffineAlgebraStalkFlat`. It isolates the
localization map on stalks from Stacks 0AVW.

`lem-sc-stalk-flat-tensor-pullback-kernels`, in
`dag/nodes/sec-picard-framework/lem-sc-stalk-flat-tensor-pullback-kernels.json`,
is stated in `Sheaf.AlgebraicGeometry.StalkFlatTensorPullbackKernels`. It isolates
only preservation of kernels for a general stalkwise flat ringed-space morphism,
using the tensor formulas and additivity. Its proof describes the natural scalar
comparison and the stalkwise kernel comparison, following Stacks 02N4.

The existing node's proof and proof_deps now match the Lean proof. No change record
is needed because all existing statements and definitions are unchanged.

## Second reading by W2

1. **Statements unchanged.** I diffed the delivered affine tensor pullback module against the repository version. The existing declaration signature and all existing declarations are byte-for-byte unchanged; the two added declarations are separate split nodes.
2. **Proof and axioms.** I compiled all three delivered modules with `lcompile.py --all`; compilation succeeds with no errors. The only remaining `sorry`s are the two named split theorems, each public, documented, and represented by a DAG node. No definitions contain `sorry`, and no forbidden declarations occur.
3. **Split statements.** The stalk-flatness and kernel-preservation statements are true, strictly simpler than the original target, and needed by the proof. They do not duplicate the target; their edge cases (empty source, zero stalks, and arbitrary module sheaves) are addressed in their documentation.
4. **Shortest route and pruning.** The proof uses the existing concrete tensor pullback and additive left-adjoint route, then the general stalkwise-flat kernel lemma and Mathlib's finite-limit theorem. The old proof-only `Sheaf.Algebra.Homology.ModuleStalkExact` import is removed from the target module; no additional reachable module is pruned.
5. **DAG and unit route.** The existing node's proof and `proof_deps` agree with the Lean proof, and each new node records its theorem, source, proof, and dependencies. The affine-equivalence/finite-duality unit route remains the stated route; no target or definition was changed.

I changed only the delivered proof/imports, added the two documented split theorem modules and matching DAG nodes, and appended this review.
