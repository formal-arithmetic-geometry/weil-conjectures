## What changed

Proved `AlgebraicGeometry.derived_open_cross_components_isIso` without changing its
statement, definitions, universes, or visibility. Replaced the proof-only import of
`Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction` with
`Sheaf.AlgebraicGeometry.DerivedOpenIntersectionMateIso`. The first component is a
specialization of the existing single-mate theorem. For the second component, its
symmetric specialization gives invertibility of the mate with target R_W(sU A),
and adjunction naturality factors the required map through R_W(c.hom). Functors
preserve the composition and the isomorphism c.

Updated the theorem docstring and its DAG proof, proof dependencies, and proof
origin to match this argument. Added only a theorem-scoped unused-variable linter
option: the original statement binds rW but never uses it, and its signature is
preserved verbatim. No file-level options or interfaces changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.derived_open_cross_components_isIso`
(node `lem-sc-derived-open-cross-components-iso`). No sorry remains in the delivered
module. No holes, intermediate statements, or new modules were added. The existing
single-mate theorem is already proved; this delivery reuses its dependency chain
rather than copying its argument. This claim concerns the delivered module, not
closure of every dependency of the targets.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`.
The parent proof no longer directly uses `lem-pc-restrict-derived-direct-image-open`
or `lem-sc-derived-k-injective-restrict-open`; both are replaced in its proof
plan by `lem-sc-derived-open-intersection-mate-iso`. Their theory remains needed
transitively by the single-mate theorem, so no claim that those modules leave the
target import closure is made. The public restriction-maps import and its
statement-definition dependencies remain necessary. No other imports or nodes
can be pruned by this delivery.

## Where the brief, the DAG or earlier work was wrong

The old proof plan requested a fresh K-injective, sectionwise computation and an
explicit comparison of arbitrary adjunction choices. The existing single-mate
interface already handles those adjunctions. Its statement suffices directly,
with `CategoryTheory.Adjunction.homEquiv_naturality_right` for the extra c factor.
The unit record `sk-thm-picard-duality` has no realized node requiring the old
lower-level computation; the unit and chapter route are unchanged.

Read the existing single-mate theorem and its node, and verified that its arbitrary
adjunction hypotheses and lack of a cover premise exactly fit both applications.
Read Stacks Tags 08DG and 08FE on their primary pages: the former factors the A
summand through direct image of c, as this Lean proof does. Empty opens, empty
intersection, and U=V require no case split or extra assumptions.

Searches: launcher leanfinder returned only underived open-counit results; launcher
loogle with the abbreviated identifier returned unknown identifier; launcher grep
and local Mathlib search located the fully qualified homEquiv naturality law.
Local library search located the existing single-mate theorem. No new node needed.

## Second reading by F2

1. **Interface and statements.** Compared the delivered module and node with the repository versions. The theorem signature, definitions, universes, hypotheses, conclusion, and visibility are unchanged byte for byte; only the proof-only import, proof, theorem options, docstring, and DAG proof metadata differ. Verdict: pass.

2. **Proof and trust.** Compiled the module with `lcompile.py`; it succeeds with no errors. The theorem has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or `debug.skipKernelTC`. The proof uses the existing `derived_open_intersection_mate_isIso`, adjunction naturality, functoriality, and the isomorphism `c`; its two factors are registered as isomorphisms. Verdict: pass.

3. **Statements and dependencies.** No statement was split off and no new node was added. The reused theorem is a strictly simpler single-mate result already present in the library, so the delivery introduces no duplicate or weakened restatement. The removed direct proof import is unused after the proof change; the node's proof dependencies now match the declarations actually used. Verdict: pass.

4. **Route and pruning.** The proof retains the unit's existing route through the overlap-mate theorem and does not bypass a realized unit step. It handles arbitrary supplied adjunctions and empty opens through the imported theorem. The old direct-image restriction and K-injective proof dependencies are no longer direct dependencies; their theory remains available transitively. Verdict: pass.

5. **DAG and source agreement.** The node's `proof`, `proof_deps`, and `proof_origin` describe the Lean proof and its Stacks source. The theorem's naturality factorization agrees with the stated cross-component map, including the `c.hom` factor. Verdict: pass.

Changed in this second reading: no Lean code or statements. Added this review section only; no split-off holes remain.
