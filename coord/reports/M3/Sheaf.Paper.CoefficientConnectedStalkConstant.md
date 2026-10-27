## What changed

Replaced the sole sorry in `AlgebraicGeometry.Scheme.coefficient_connected_stalk_constant`
by a proof that preserves its complete signature and the definition of `coefficientSliceConstant`.
The proof establishes finite stalk cohomology directly from a finite constant chart through the
geometric point, using the equivalence of the sliced AsSmall sites and the constant-sheaf fiber
isomorphism. It then applies the existing coefficient Tor-amplitude/flat-model equivalence,
takes the exact stalk termwise, and invokes the Noetherian bounded-flat-complex perfectness
criterion. The two geometric steps are isolated as separate source lemmas: a common local model
on the connected component, and globalization of local isomorphisms on a weakly contractible
affine. The final Lean proof combines the resulting covering sieve and the descent theorem.

Added `Sheaf.Paper.CoefficientEtaleStalkFlat`, `Sheaf.Paper.CoefficientConnectedLocalStalkModels`,
and `Sheaf.Paper.CoefficientWeaklyContractibleLocalIso`, with matching nodes. The flat-stalk
module transports flatness through the normalized constant-scalar and AsSmall monoidal
equivalences, and proves the geometric-fiber assertion by testing monomorphisms on constant
sheaves. All new imports in the item are proof imports. No existing public import, definition,
signature, instance, or attribute is changed. No other existing Lean module is adapted.

Validation: the complete four-module sandbox compiles through `lcompile.py --all` with
profiling removed: local models 6.0 s, flat stalks 10.6 s, descent 8.9 s, item 34.1 s.
The sole line-length warning was then corrected by whitespace alone. The item theorem
signature and the complete `coefficientSliceConstant` definition were compared against
the repository and are unchanged. No heartbeat or compiler-time limit was raised.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.coefficient_connected_stalk_constant` (one original hole; zero remain
in the item). Its perfectness conjunct is proved from the existing bounded flat model and the
new flat-stalk theorem, including the explicit finite-cohomology argument.

Also proved `AlgebraicGeometry.Scheme.coefficientEtaleModuleStalk_flat`, with no sorry in its
module. The item contains the proved private helper `coefficient_lisse_stalk_finite` and a
proved private instance transporting the locally-bijective sheafification criterion to the
independent coefficient universe. Separate proved helpers handle derived stalk finiteness and
the bounded-flat-model perfectness criterion; separating these conversions also avoids the
elaborator heartbeat limit without changing any shared definition or raising any limit.

Two new holes remain:

- `AlgebraicGeometry.Scheme.coefficient_connected_local_stalk_models`, node
  `lem-sfb-coefficient-connected-local-stalk-models`. This is the local covering-sieve assertion;
  it has neither a Tor-amplitude hypothesis nor an affine/weak-contractibility hypothesis and
  asserts no global isomorphism or perfectness.
- `AlgebraicGeometry.Scheme.coefficient_weaklyContractible_local_iso`, node
  `lem-sfb-coefficient-weakly-contractible-local-iso`. This is the separate descent argument for
  any pair of derived complexes already known to be locally isomorphic. It does not involve
  an etale input, a geometric stalk, connectedness, Noetherianity, finite cohomology, or Tor
  amplitude.

Thus this is a decomposition, not a claim of a complete new axiom-free proof: one original
hole closed, two strictly smaller source steps added. Neither new hole is the original theorem
with renamed or repackaged hypotheses. Their combination is written in Lean, and the algebraic
perfectness argument and finite-stalk calculation are proved.

## No longer needed

The item no longer directly uses `lem-sfb-connected-etale-perfect-constant` /
`Sheaf.SixFunctors.ConnectedEtalePerfectConstant`. Its coefficient universe is tied to the
successor of the scheme universe, whereas this item allows an independent coefficient
universe; it cannot be applied directly to the present statement. The new local-model lemma
retains exactly the local part of its source argument. The proof of stalk perfectness uses a
bounded flat model rather than the previous proposed tensor-stalk/pseudo-coherence route.

Removed the unused proof imports of `ConstantSheafEquivalence` and `EtaleOver`, and replaced
the broad `Mathlib.CategoryTheory.Filtered.Final` proof import with the precise
`Mathlib.CategoryTheory.Limits.Preserves.Filtered` module. No existing module is withdrawn,
and no entire subtree is claimed pruned. No original public
import is removed. The component-open, comparison and localization facts remain needed in the
local-model or descent steps, whose nodes record them.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement is unchanged and no false statement was found. The existing
connected-etale-perfect-constant declaration is not directly usable at the item's arbitrary
coefficient universe. Explicit sheafification and locally-bijective instances are needed on
the original etale slice to avoid inference choosing a successor-sized coefficient category.
The DAG now records the actual bounded-flat-model perfectness argument and the two separate
geometric obligations. This is not another renaming of the complete connected-stalk theorem.

Edge cases: the flat-stalk theorem includes the zero coefficient ring and zero sheaf. A point
z makes its component nonempty; the test object U may be empty, in which case the two slice
complexes are zero. The local-model lemma needs no Tor bound, and the descent lemma needs no
boundedness of its pair of complexes. The original nonempty interval condition is supplied by
`hTor.1` when invoking the bounded flat model.

## New nodes

`lem-sfb-coefficient-etale-stalk-flat`: normalized stalk flatness, without finiteness assumptions.
Its module has no sorry; its proof follows Stacks 05VB/05VC with the fixed-scalar comparisons.

`lem-sfb-coefficient-connected-local-stalk-models`: the covering-sieve portion of Stacks 09BI,
before its perfectness conclusion, transported to the actual coefficient-model slices.

`lem-sfb-coefficient-weakly-contractible-local-iso`: the finite affine covering, section, and
clopen descent portion of Stacks 090K/09C6, for an arbitrary pair of locally isomorphic derived
complexes. The generic finite clopen argument is also written out in the already-proved
`WeaklyContractibleEtaleConstantModels` source module, whose specialized coefficient universe
prevents directly applying its final theorem here.

Each new node records three actual Mathlib searches from this sandbox's `searches.jsonl`,
its exact Lean statement, source, complete proof plan, and blueprint ancestry. No change record
is necessary: only the assigned existing module/node and new modules/nodes are changed.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
