## What changed

Proved `AlgebraicGeometry.openRestriction_isKFlat` in
`Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel`, with its signature and visibility
unchanged. Added two proof-only imports: `Sheaf.Algebra.Homology.KFlatPullback` and
`Sheaf.AlgebraicGeometry.TensorPullback`. Updated the item's DAG proof and dependencies.
No definitions, public imports, other modules, or target statements changed.

The proof specializes the existing K-flat pullback theorem to the open inclusion.
The explicit tensor pullback and Mathlib's open restriction are left adjoints to the
same pushforward; `Adjunction.leftAdjointUniq` compares them. Mathlib's
`Scheme.Modules.overFunctorEquiv` identifies open restriction with exactly the
canonical over-site composite in the statement. Mapping this comparison to complexes
and through total tensor with an arbitrary acyclic complex transports exactness
in each degree. The tensor-pullback complex and termwise tensor-pullback functor
agree definitionally on terms and differentials; Lean checks this with `convert`/`rfl`.

Sources checked: [Stacks 06YC](https://stacks.math.columbia.edu/tag/06YC) and
[Stacks 0096](https://stacks.math.columbia.edu/tag/0096), together with the existing
Lean declarations and DAG nodes. The proof applies to arbitrary unbounded complexes
and every open, including the empty open, without flat-term assumptions.

This uses `lem-pc-kflat-pullback-preservation` as a generic ringed-space tool, and
`def-pc-module-pullback` for its already constructed tensor functor and adjunction.
Neither replaces a statement or proof step realized at unit level. The item's unit
record has no realized statement or step nodes.

## Proved and sorry left

Closed the only hole: `AlgebraicGeometry.openRestriction_isKFlat`
(node `lem-pc-open-restriction-kflat-model`). Holes closed: 1. Holes added: 0.
No `sorry` remains in the item's module, and no new module or theorem was added.
The proof uses existing library declarations; their transitive proof obligations
remain with their respective items.

Local single-file compilation passed with no warnings using `lcompile.py`.
The delivery dry run performs the required declaration and axiom checks.

## No longer needed

No import was removed. The original public imports are retained for the statements.
The item no longer applies `lem-pc-kflat-stalk-criterion` directly, so that edge is
removed from its direct `proof_deps`. Its module
`Sheaf.Algebra.Homology.KFlatStalkCriterion` is still needed transitively by
`Sheaf.Algebra.Homology.KFlatPullback`; it is not claimed as pruned.
The original open-restriction node is retained for its restriction adjunction.
No node or module is globally pruned by this delivery. No stalk-comparison helper,
new module, or new proof obligation is needed.

## Where the brief, the DAG or earlier work was wrong

The original plan was mathematically correct, but its middle stalk-ring transport
step need not be implemented again. The library already proves K-flat preservation
for the explicit tensor pullback, and already provides its adjunction. Mathlib's
restriction adjunction and `overFunctorEquiv` supply the required comparison.
The unchanged docstring describes the underlying stalk argument, now delegated
to the existing pullback theorem. No statement dispute or tool fault was found.

## Second reading by K2

1. I diffed the delivered module against the repository version. The theorem signature,
   visibility, definitions, and public imports are unchanged; only proof-only imports and
   the proof body differ.
2. I compiled the module with `lcompile.py`; it succeeds without warnings. The proof has no
   `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`.
3. The existing target statement is unchanged. The proof uses the existing pullback
   K-flatness theorem and uniqueness comparison of the two left adjoints; no new statement
   was split off, and no definition contains chosen data from an unproved existence result.
4. The proof follows the DAG route: explicit tensor pullback preservation is applied first,
   then transported across the canonical restriction isomorphism and total-tensor comparison.
   The former direct stalk-criterion edge is removed from `proof_deps` because it is no longer
   used directly, while its module remains a transitive dependency.
5. I checked the unit record and found no realized unit statement or step to bypass. The
   resulting proof handles arbitrary opens, including the empty open, and unbounded complexes.

I changed only the proof imports/body, the corresponding DAG proof metadata, and this report.
