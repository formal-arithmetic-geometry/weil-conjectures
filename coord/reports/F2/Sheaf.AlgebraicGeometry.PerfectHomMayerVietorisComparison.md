## What changed

Kept the signature of `AlgebraicGeometry.perfect_hom_mayerVietoris_comparison` unchanged.
Its proof now constructs the stage Hom functor and colimit, obtains exact geometric
rows with explicitly local neighboring comparisons, proves those comparisons
bijective using the three continuity hypotheses, and converts the bijective group
homomorphisms to isomorphisms.

Added `PerfectHomStageColimit.lean`: the functor laws and colimit construction are
proved. Identity transport is an injective idempotent, hence the identity;
composition follows from `perfectHomMap_trans`. `ULift` supplies the required
universe without changing any Hom set.

Added `PerfectHomLocalComparison.lean`: two concrete predicates record pinned local
Hom-colimit presentations and their closure under products and equivalences. The
recognition theorem `PerfectHomLocalMap.bijective` is proved, including its private
single-comparison helper. For injectivity it moves representatives to a common
stage and then uses eventual equality; for surjectivity it uses a representative
starting at i. Neither predicate asserts bijectivity or continuity.

Added `PerfectHomMayerVietorisLocalRows.lean`: the remaining geometric step is one
named construction theorem, with no local-continuity assumptions and no
isomorphism assertions. It supplies exact rows, central pinning and actual local
presentations of the neighboring maps. This is strictly the construction part of
the original argument; the stage system and deduction of the four isomorphisms
are separate, completed Lean proofs. Updated the parent node's proof route.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.perfect_hom_mayerVietoris_comparison`
(node `lem-pc-perfect-hom-mayer-vietoris-comparison`).

Proved new declarations `AlgebraicGeometry.perfect_hom_stage_colimit`
(node `lem-pc-perfect-hom-stage-colimit`) and
`AlgebraicGeometry.PerfectHomLocalMap.bijective`
(node `lem-pc-perfect-hom-local-comparison`), and both private helpers.

One new hole remains:
`AlgebraicGeometry.perfect_hom_mayerVietoris_local_rows`
(node `lem-pc-perfect-hom-mayer-vietoris-local-rows`). Its proof is exactly `by sorry`.
There are no other delivered sorries and no data definitions containing sorry.
This is a decomposition: one original hole closed, one strictly geometric hole
added, net zero holes. It is not reported as a sorry-free proof of the comparison.

## No longer needed

All old parent `proof_deps` are replaced as direct dependencies:
`def-pc-perfect-complex`, `def-pc-perfect-hom-continuity-on`,
`lem-pc-affine-derived-pullback-tensor-tilde`,
`lem-pc-derived-mayer-vietoris-functorial`, `lem-pc-derived-mayer-vietoris-triangle`,
`lem-pc-localized-pullback-perfect-model`, `lem-pc-perfect-hom-transport`,
`lem-pc-perfect-thick-closure`, `lem-pc-ringed-spaces-derived-adjoint`,
`lem-pc-ringed-spaces-derived-pullback-composition`, `lem-sc-perfect-qcoherent`,
`lem-weil-pbc-filtered-colimit-abelian-groups-exact`, and
`lem-weil-pbc-filtered-colimit-sets-elementwise`. They remain needed through the
new construction and recognition modules; no module is globally pruned.

Removed these direct proof imports from the parent:
`Mathlib.Algebra.Category.Grp.AB`,
`Mathlib.Algebra.Category.Grp.FilteredColimits`,
`Sheaf.AlgebraicGeometry.PerfectThickClosure`,
`Sheaf.AlgebraicGeometry.LocalizedPullbackPerfectModel`,
`Sheaf.AlgebraicGeometry.PerfectImpliesQCoh`,
`Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`,
`Sheaf.AlgebraicGeometry.DerivedAdjoint`, and
`Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial`.
They remain proof dependencies of the geometric construction module; none is
claimed pruned from the targets' import closure. The parent now directly uses
only the stage-colimit and local-row lemmas, the local bijectivity theorem, and
Mathlib's bijective-isomorphism criterion. No original geometric node is globally
unneeded and no unit statement or unit proof step has been bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous attempt treated the absence of a preassembled comparison theorem
as an obstacle. It is a construction step that can be isolated while proving the
stage system and local-continuity step. The remaining construction is explicitly
marked as unfinished, rather than hidden in a partial proof or an equivalent
restatement of the original conclusion.

The literature files are absent from this clone; the cited sources were read at
https://stacks.math.columbia.edu/tag/09RE and
https://stacks.math.columbia.edu/tag/08BW. LeanFinder returned general
Mayer--Vietoris and AB5 results, not the pinned scheme comparison. Loogle found
the filtered-set equality criterion. LeanSearch returned Internal Server Error;
its unavailability is recorded, without a mathematical verdict. Source and DAG
searches found no existing stage Hom functor or local-comparison recognition
interface.

Edge cases checked: the tail contains i, and common upper stages exist for a
directed preorder without antisymmetry. Stage Hom sets may be empty; the
construction does not select elements. The identity proof does not assume that
derived pullback is definitionally the identity. Empty opens and zero perfect
complexes give zero local groups and satisfy the same local presentation. Product
bijectivity uses the two individual bijections, with no nonemptiness assumption.

The unit record `sk-thm-picard-semicon` realizes no statement or step through this
node; the replacement preserves all five steps of this node's Mayer--Vietoris
route. The generic predicates package real stage representatives and canonical
transport equations, and contain no inverse or bijectivity witness.

## New nodes

`def-pc-perfect-hom-local-comparison` records the explicit local filtered Hom
presentation predicate in `PerfectHomLocalComparison.lean`.

`def-pc-perfect-hom-local-map` records its closure under binary products and
conjugation by equivalences, in the same module.

`lem-pc-perfect-hom-local-comparison` records the proved local-bijectivity
recognition theorem in `PerfectHomLocalComparison.lean`.

`lem-pc-perfect-hom-stage-colimit` records the proved stage Hom functor and colimit
in `PerfectHomStageColimit.lean`.

`lem-pc-perfect-hom-mayer-vietoris-local-rows` records the sole remaining
construction theorem in `PerfectHomMayerVietorisLocalRows.lean`. It retains the
original geometric proof dependencies and the complete construction plan in its
docstring and node. No change record is needed: no existing signature, definition,
visibility, or public import has changed, and no other existing module is adapted.

## Second reading by F2

1. **Interface and accidental changes.** Compared the delivered parent module with the repository version. The target theorem signature and all existing declaration signatures are byte-for-byte unchanged. The added modules contain only the recorded new declarations; no unrelated library file is changed. Verdict: pass.

2. **Proof and axioms.** Compiled all four sandbox modules with `lcompile.py --all`; compilation succeeds. The only remaining `sorry` is the named public theorem `AlgebraicGeometry.perfect_hom_mayerVietoris_local_rows`, exactly as listed with node `lem-pc-perfect-hom-mayer-vietoris-local-rows`; no definition contains `sorry`, and no forbidden declaration form occurs. The stage-colimit and local-bijectivity proofs are substantive reductions, not restatements. Verdict: pass subject to the recorded split hole.

3. **Statements and split nodes.** Checked the new predicates and theorems against their docstrings, DAG records, and edge cases (empty Hom sets, empty opens, zero objects, non-antisymmetric directed preorders, and products). The predicates do not assert bijectivity; the recognition theorem uses exactly the three continuity hypotheses. The local-rows statement is strictly intermediate: it supplies exact rows and local presentations without continuity or isomorphism claims. Verdict: pass.

4. **Pruning and route.** The parent removes only proof-only imports that are no longer referenced directly; imports needed by the geometric construction remain in its module. The parent proof follows the stage-colimit, local-row construction, and local-bijectivity route, and does not bypass the Mayer–Vietoris unit steps. Verdict: pass.

5. **DAG and unit agreement.** Verified that each new declaration has a matching node, proof/proof_deps follow the Lean proof, and the parent node records the three actual dependencies. The unit record is unchanged; no unit statement or realized step is replaced. Verdict: pass.

Changed during second reading: completed the removed direct DAG dependency list; appended this review. No declaration signature, definition body or DAG statement changed. Independently searched LeanFinder for "derived Hom base change open cover exact sequence filtered system", Loogle for `Types.jointly_surjective_of_isColimit`, and the library for Hom colimit and Mayer–Vietoris comparisons. The results are generic set-colimit and sheaf Mayer–Vietoris facts, not the pinned geometric rows. Checked the source construction against [Tag 09RE](https://stacks.math.columbia.edu/tag/09RE) and [Tag 08BW](https://stacks.math.columbia.edu/tag/08BW).

The public continuity import in `PerfectHomLocalComparison.lean` is necessary: it
appears in the public bijectivity theorem hypotheses. An attempted privatization
failed the compiler visibility check and was reverted before delivery.
