## What changed

Proved `AlgebraicGeometry.Scheme.finiteTorsionDerivedPullback_isEquivalence_of_isIso`
in `Sheaf.AlgebraicGeometry.IsomorphismDerivedPullbackEquivalence`, with its original
signature and the definition of `finiteTorsionDerivedPullback` unchanged.

The ordinary pullbacks along `g` and `inv g` are quasi-inverse by the published
fixed-scalar pullback composition and identity comparisons, transported to the
intrinsic coefficient presentation. A private proved comparison identifies the
tensor pullback with this presentation by uniqueness of left adjoints. The
canonical coefficient direct-image map agrees with the original constant-section
map by `Equiv.apply_symm_apply`, so the right adjoint is precisely the direct image
in the conclusion. The source-library `Equivalence.mapDerivedCategory` supplies the
derived equivalence. Uniqueness of right adjoints and termwise factorization give
its direct-image comparison; the inverse-pullback comparison is reflexivity.

Added proof-only imports of `ProEtaleConstantRingOperations`,
`SfIntrinsicRealizationTransport`, and the source-library derived exact-functor API.
All original public imports remain. Updated the existing node's proof,
`proof_deps`, and `proof_origin`; removed its obsolete isomorphism inverse-image
tool approval. No signatures, public definitions, or consumer modules change.

The direct large equivalence term caused a kernel-checking timeout. A private
proved general lemma now performs the categorical assembly with abstract functors.
It is applied to the concrete module pullbacks; no module or mathematical proof
obligation was split to evade the compile limit.

Fresh verification on 2026-10-19, resumed session: single-file `lcompile.py` passed
in 2.8 seconds with exit code 0 and no diagnostics. Comparison against the current
shared sources confirms the original signature and public definitions are unchanged;
the sole original `sorry` is closed and no holes are added.

Earlier retained-attempt validation: `deliver3.py S7 Sheaf.AlgebraicGeometry.IsomorphismDerivedPullbackEquivalence
--no-push` returned OK: the final module compiled and passed the preflight, including
the declaration/axiom probe. Review class: CODEX because the existing DAG route changed.
The first fresh dry run on 2026-10-19 failed during delivery worktree setup:
`git checkout -q --detach origin/sheaf-dag` exceeded the tool's 600-second timeout,
before preflight. The fresh retry failed at the same checkout with the same
600-second `subprocess.TimeoutExpired`. Both failures occurred in
`sharedrepo.worktree`, before any Lean preflight or push. Launcher tools were
not changed. Those retained-session attempts were blocked by this repeated tool
failure. The resumed session started with the required fresh delivery dry run.

Continuation verification on 2026-10-19: no interrupted delivery or compile process
remained running, and no completed push appeared in the retained logs or shared
ledger. The fresh required dry run returned `OK (dry run)` at commit `465034cdc3`:
the module compiles and passes preflight. Review class remains CODEX because the
existing node proof route changed. No proof, statement, definition, or DAG changes
were needed in this continuation.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.finiteTorsionDerivedPullback_isEquivalence_of_isIso`
(node `lem-weil-isomorphism-derived-pullback-equivalence`).

Item: 1 original sorry, 1 closed, 0 remaining. Added holes: 0. Split-offs: 0.
Every private helper is fully proved. Existing imported theorems may still depend
on sorry; no claim is made that the entire transitive axiom closure is finished.

## No longer needed

Removed the redundant proof-only imports `Sheaf.CategoryTheory.RingedSiteModules`,
`Mathlib.Algebra.Homology.DerivedCategory.Basic`,
`Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`, and
`Sheaf.Paper.DerivedPullbackTensorHom`. The first two statement-level APIs
remain available through the original public imports; the latter two proof routes
are unnecessary.

This proof does not need `lem-weil-proetale-isomorphism-inverse-image` or its modules
`Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage` and
`Sheaf.AlgebraicGeometry.ProEtaleIsomorphismInverseImage`: ordinary pullback
composition and identity already give a quasi-inverse. Removed this node from
`proof_deps` and from top-level `tool_uses`.

Also removed from `proof_deps`:
`lem-sfb-adjunction-localization`,
`lem-weil-equivalence-map-homological-complex`,
`def-weil-derived-pullback-tensor-hom`,
`def-weil-pbc-proetale-site`, and `def-weil-sheaf-of-modules-category`.
The first two separate assembly steps are subsumed by the existing source-library
`Equivalence.mapDerivedCategory`; the last three are already present in the
unchanged statement/definition dependencies and require no additional proof step.
These are local pruning claims, not assertions that no other target needs them.

The exploratory open-square route is also unnecessary: the final proof does not
import `Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange` or use
`lem-trf-open-square-exchange`. Its pullback-model comparison is replaced by a
proved uniqueness-of-left-adjoints construction. No open-square lemma is introduced
as a dependency.

## Where the brief, the DAG or earlier work was wrong

The old search record predates the existing source-library construction
`CategoryTheory.Equivalence.mapDerivedCategory` in
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
It makes the separate explicit unit/counit localization assembly unnecessary.
The target statement itself is correct and was preserved. No definition repair,
forced adaptation, or new node was required. The unit's `realized` lists are empty;
this change prunes only below the unit level.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
