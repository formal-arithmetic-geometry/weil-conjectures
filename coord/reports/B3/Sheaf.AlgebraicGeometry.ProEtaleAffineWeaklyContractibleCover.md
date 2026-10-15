## What changed

Proved `AlgebraicGeometry.Scheme.ProEt.exists_affine_weaklyContractible_covering_family`
without changing its signature or visibility. The proof takes arbitrary affine charts, applies
a contractible affine extension to each, composes the singleton covers with the chart cover
using `Precoverage.ZeroHypercover.bind`, lifts the index to `Type (u + 1)`, and constructs the
objects and arrows of the full small site over X. The covering clause is transported by the
comap definition of `ProEt.precoverage`. Affineness is definitionally affineness of a spectrum.

Added the proved theorem `AlgebraicGeometry.Scheme.ProEt.exists_affine_contractible_extension`
in `Sheaf.AlgebraicGeometry.ProEtaleAffineContractibleExtension`. This is the local affine step,
with its own node, rather than another arbitrary-site covering theorem. It packages the already
proved source-library `exists_isWContractibleRing` and
`AlgebraicGeometry.Scheme.ProEt.isWeaklyContractible_of_iso`, retaining singleton membership
in the precoverage and the evaluation property for every weakly etale structural map.
It has no `sorry`. All choices are inside theorem proofs; no data definitions were added.
The item imports this helper privately, and the helper imports the source theorem privately.
The existing public import and all existing public signatures are preserved.

Both delivered modules compile cleanly, together in import order, with `autoImplicit = false`.
The target proof before extraction of the local helper was also checked by `#print axioms`:
only `propext`, `Classical.choice`, and `Quot.sound`. The dry run additionally probes both
final delivered modules. The source extension and source affine weak-contractibility theorem
were separately checked to have only those three axioms. Empty schemes and zero rings require
no exceptional hypotheses: the affine cover of an empty scheme has empty index, the extension
theorem accepts the zero ring, and the cover APIs preserve those cases.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.ProEt.exists_affine_weaklyContractible_covering_family`
(node `lem-weil-pbc-proetale-affine-wcontractible-covering-family`).

Also proved the new local helper:
`AlgebraicGeometry.Scheme.ProEt.exists_affine_contractible_extension`
(node `lem-weil-pbc-affine-contractible-extension-full-site`).

No `sorry` remains in either delivered module. No holes were added, and none were split off.
This is a proof, not a decomposition into new unfinished statements.

## No longer needed

Removed the item's original proof imports:

- `Sheaf.RingTheory.IndEtaleStability`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale` (already available transitively).
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.

The actual proof no longer uses these former DAG proof dependencies directly:

- `lem-weil-pbc-wcontractible-ring-extension`, module
  `Sheaf.RingTheory.BoundedWContractibleExtension`: no explicit cardinal bound is needed;
  the proved source extension has its witness in the original universe.
- `lem-weil-pbc-wcontractible-affine-weakly-contractible`, module
  `Sheaf.AlgebraicGeometry.WContractibleAffineEvaluation`: use the proved source-library
  `isWeaklyContractible_of_iso` on the source ring's `IsWContractibleRing` instance.
- `lem-weil-pbc-ind-etale-stability`, module `Sheaf.RingTheory.IndEtaleStability`:
  use proved source `RingHom.IndEtale.weaklyEtale` and Mathlib scheme composition.
- `lem-weil-pbc-open-immersion-etale`, `def-weil-etale-morphism`, and
  `def-weil-open-immersion`: the Mathlib Zariski-to-pro-etale cover inclusion supplies this
  part of the chart-cover argument.
- `lem-weil-pbc-affine-scheme-qcqs`: the finite-affine-open refinement argument is already
  proved inside Mathlib's quasi-compact-cover and precoverage-composition API.

These removals are from this proof route. Other users may still need the named modules/nodes;
no global unreachability claim is made. The definition nodes for schemes, spectra, universes,
weak etaleness and the pro-etale site/covering stay in the updated proof dependencies.
No blueprint unit statement or realized unit step is bypassed: this is a change of tools
inside the subordinate affine-cover construction.

## Where the brief, the DAG or earlier work was wrong

The planned ring-extension and ring-retraction-evaluation interfaces are usable: an initial
complete proof from them compiled. However, the source library already contains fully proved
w-contractible extension and full-small-site evaluation theorems, so neither unfinished
Sheaf interface is needed here. The source `exists_isWeaklyContractible_cover` only exposes
membership of the generated sieve in the topology, whereas this item's signature requires
membership of the presieve in the precoverage. The delivered proof therefore retains the
source ring/evaluation tools and reconstructs the chart composition with Mathlib's stronger
precoverage API. The old docstring's numbered plan is superseded by the updated DAG proof;
its explicit cardinal-bound branch is unnecessary with the proved same-universe extension.
There is no disputed statement, changed definition, changed existing signature, or forced
adaptation.

Searches were run with LeanFinder, Loogle, LeanSearch and source `rg`. LeanSearch returned an
Internal Server Error and is recorded as unavailable, with no verdict assigned to that search.
The other searches and source reading identified the proved tools. The literature files are
not present in this read-only clone; the delivered proof uses the actual proved source-library
APIs, whose docstrings and proofs identify the Stacks tags, and cites those local Lean sources
explicitly in the new node.

## New nodes

`lem-weil-pbc-affine-contractible-extension-full-site` records the proved local affine extension
step. Its statement quantifies over a ring A, constructs a singleton affine cover Spec D of
Spec A, and proves evaluation-surjectivity for every weakly etale map Spec D to every X.
It is strictly the affine input to the chart argument and is fully proved. The node records
source-library theorem locations, the three search kinds, and the full proof in words.
No change record is needed: no existing statement or definition changed.

## Second reading by B3

1. **Signatures and accidental changes.** Compared the delivered item module with the
repository version. The existing theorem signature and visibility are byte-for-byte
unchanged; only its proof and proof-only imports changed. The added helper is a new
public declaration with its own node, and no existing declaration or target statement
was weakened, strengthened, or redefined. Verdict: pass.

2. **Proof and axioms.** Compiled both delivered modules together with
`lcompile.py --all`; both compile without errors or warnings and contain no `sorry`,
`axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. Axiom checks give only
`propext`, `Classical.choice`, and `Quot.sound` for the target and helper. Verdict: pass.

3. **Split statements and prior results.** The helper statement is a strict affine
extension input to the target, with singleton precoverage membership and evaluation
surjectivity for every weakly etale structural map; it is not a restatement of the
target. I searched Mathlib, `lean/`, and the source declarations by concept and by
name (including LeanFinder, Loogle, LeanSearch, and `rg`); no duplicate theorem was
found. The zero-ring and empty-scheme cases are covered by the constructions. Verdict: pass.

4. **Route and pruning.** The target proof uses the existing affine-open cover, the
new affine extension, Mathlib's precoverage bind and reindex operations, and the
source weak-contractibility theorem. The former direct imports and proof dependencies
listed under `## No longer needed` are genuinely unused. The unit
`sk-thm-properbasechange` statement and realized steps remain untouched; this is a
subordinate proof-tool change. Verdict: pass.

5. **DAG agreement.** The two node records match the declarations, proof steps,
`proof_deps`, `proof_origin`, module paths, and theorem statements delivered here.
The new helper node contains its source, search record, and complete proof description.
Verdict: pass.

Changed during second reading: added this review record only; no Lean proof, theorem
signature, definition, node statement, or import was further changed.
