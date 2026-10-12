## What changed

Replaced the sorry in
`AlgebraicGeometry.canonicalModuleBaseChange_isIso_affine_of_isFlatOver` with a complete
Lean reduction. The theorem's signature, visibility, and docstring are unchanged.
The main proof chooses an actual finite affine cover, reindexes it by Fin r, constructs
an explicit sheafified alternating Cech complex, and proves its boundedness directly.
It applies `flatComplexDerivedPullback`, identifies the pinned ordinary functors with
tensorPullback, and proves that the geometric factorization's counit component is invertible
using Mathlib's `isLeftDerivedFunctor_iff_isIso_leftDerivedLift` and
`leftDerived_fac_app`. Rewriting the factorization equation finishes by composition
of isomorphisms. All four delivered modules compile with lcompile.py --all.

Added `AffineAlternatingCechModel`, a real construction using the existing increasing-tuple
complex, restrictScalars, tilde.functor, and extension to integer degrees. No representative
or arbitrary data is chosen from an unproved existence theorem. Added separate modules for
the ordinary termwise-flatness assertion and the geometric factorization equation.
The latter assumes no relative flatness and asserts no invertibility of the counit or the
canonical composite. These are strictly parts of the argument, not the original theorem
with an existential comparison. Updated the item's proof dependencies to match Lean.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.canonicalModuleBaseChange_isIso_affine_of_isFlatOver`
(node `lem-pc-affine-relatively-flat-canonical-module-base-change`).
This is a decomposition, not a sorry-free proof of the mathematical theorem: two holes
were added, and the closure net is -1 before other existing dependency holes are counted.

Added exactly two named public theorem holes:

- `AlgebraicGeometry.affineAlternatingCechModel_flat`, node
  `lem-pc-affine-alternating-cech-model-flat`, in `AffineAlternatingCechModelFlat`.
  Its conclusion concerns only ordinary terms of the specified explicit complex.
- `AlgebraicGeometry.affineAlternatingCech_baseChange_factorization`, node
  `lem-pc-affine-alternating-cech-base-change-factorization`, in
  `AffineAlternatingCechBaseChangeFactorization`. Its conclusion identifies the actual
  canonical map as a composite through a left-derived counit which need not be invertible.

The private helper `affineAlternatingCechModel_bounded` is fully proved: increasing
embeddings Fin (n+1) into Fin r cannot exist for n > r; their product is zero, extension
and the additive sheafification functor preserve zero objects. The proof includes r = 0.
The delivered definition has no sorry; its existing alternating differential uses the
library's named square-zero proof as before. Existing holes in imported modules are not
changed or claimed closed by this delivery.

## No longer needed

Removed the direct proof imports:

- `Sheaf.AlgebraicGeometry.BaseChangeMapCech`, node `lem-pc-base-change-map-cech`.
  Its literal signature contains no equation connecting the chain map with the canonical
  mate, so it is not used anywhere by this reduction.
- `Sheaf.AlgebraicGeometry.CechResolution`, node `lem-pc-cech-resolution`.
  It is still imported by the new factorization module for that remaining geometric step;
  it is not claimed globally pruned.
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`, node
  `lem-weil-pbc-module-pullback-affine-sections`. It remains imported by the factorization
  module for the intersection-wise calculation, and is not claimed globally pruned.

The four existing public imports are retained for the original interface.
`FlatComplexDerivedPullback` is used directly by the main proof. No other original
proof-dependency module is claimed globally unnecessary. In particular the existing
alternating-complex construction is necessary for the actual model.

## Where the brief, the DAG or earlier work was wrong

The prior existence-plus-independence split retained the entire invertibility claim,
created a circular DAG, and never invoked an imported dependency theorem. It is not reused.
The previous report, including its second reading, is superseded by this worker report;
the rejected artifacts remain only in scratchpad and are outside the delivered set.

`baseChangeMap_cech` currently proves a literal existential with no Cech-to-derived-map
equation; the source file itself records this statement-review warning. It cannot provide
the intended final identification. The replacement factorization supplies precisely that
missing equation, including the argument for the comparison c specified in the item.
The ordinary ordered tuple complex of `exists_cechBaseChange_iso` has terms in every
natural degree even for a finite cover; the new model instead uses strictly increasing
tuples so that the bounded-above flat-complex theorem applies.

Edge cases checked in the statements and proof descriptions: empty X and r = 0, zero
rings and zero modules, arbitrary nonflat B over A, and G relatively flat without being
flat over O_X. No conclusion claims the comparison c itself is invertible.
The item's unit `sk-thm-picard-f-representable` has empty realized fields; these were
read and left unchanged. The original finite affine Cech route is retained. The existing
alternating-complex definition is used as a generic construction tool, not to bypass a
unit result. Mathlib searches were tried in three kinds; LeanSearch returned an internal
server error, recorded honestly, and the other services and local source searches yielded
no exact model-flatness or geometric-factorization theorem.

## New nodes

`def-pc-affine-alternating-cech-model`: explicit construction in
`Sheaf.AlgebraicGeometry.AffineAlternatingCechModel`, using the existing
`def-sc-alternating-cech-total-complex`. Its data is specified by actual functors.

`lem-pc-affine-alternating-cech-model-flat`: ordinary termwise flatness in
`Sheaf.AlgebraicGeometry.AffineAlternatingCechModelFlat`. Its complete proof in words
uses finite affine intersections, relative flatness, finite products, and localization.
It does not assume a cover or quasi-coherence, because its terms are sheafifications
of the section modules, rather than restrictions of G at arbitrary points.

`lem-pc-affine-alternating-cech-base-change-factorization`: the map equation in
`Sheaf.AlgebraicGeometry.AffineAlternatingCechBaseChangeFactorization`. Its complete proof
in words describes the augmented alternating resolution, the two acyclic comparisons,
the restriction-compatible affine tensor map, the adjunction-mate equation, and transport
of the specified comparison by H0. No flatness or counit invertibility is assumed.

Each node has a verbatim normalized Lean signature, source, three kinds of search,
blueprint ancestry, and proof dependencies matching its proof in words. None depends
on the item or on its parents. No existing interface changed and no change record is needed.

## Second reading by Q3

1. I compared the delivered item module with the repository version. The target declaration has the same signature byte for byte; only its proof and proof-only imports changed. Verdict: pass.
2. I compiled all four delivered modules with `lcompile.py --all` and checked that the only remaining `sorry`s are the two named split-off public theorems. No forbidden declarations or hollow definitions occur. Verdict: pass.
3. I read both new theorem statements and their docstrings against the proof route. The flatness statement concerns only terms of the explicit model, and the factorization statement gives only the map equation and existence data; neither restates the target or asserts an unproved isomorphism. Their DAG nodes match the declarations. Verdict: pass.
4. I checked the proof from the finite affine cover through boundedness, termwise flatness, `flatComplexDerivedPullback`, and the derived-counit uniqueness argument. The imports removed from the item are recorded above; the factorization module retains the Cech and affine-section imports it uses. Verdict: pass.
5. I checked the unit record and the nodes' `proof`, `proof_deps`, and `proof_origin`. The unit route remains realized through the explicit alternating model and factorization; no target statement or definition was changed. Verdict: pass.

I changed only the report for this second reading; no Lean declarations or node statements were altered during review.
