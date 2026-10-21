## What changed

Reduced both ordinary pasting identities to one single-square coefficient-normalization result. The Lean proofs include finite categorical transport calculations for vertical and horizontal pasting, then use faithfulness of constant embedding and the degree-zero embedding and componentwise extensionality of ordinary system morphisms. Existing signatures and definitions are unchanged. The new module also constructs actual pullback and open comparisons and proves `ordinaryModuleEvalG_comp`, including its sectionwise normalization, for use in the remaining single-square argument.

The new comparison includes zero coefficient rings, empty schemes, identity maps, and non-cartesian proper/open squares: zero and empty components give unique maps, identity comparisons retain their specified normalizations, and the general square is treated through its clopen lift rather than assumed cartesian. Arbitrary coefficient transitions are retained.

Both delivered Lean modules compile together through `lcompile.py --all` (46.5 seconds for the new normalization module and 17.4 seconds for the item).

## Proved and sorry left

Closed the original holes `moduleAlpha_vertical` and `moduleAlpha_horizontal` by decomposition. The original `gamma_evaluation` hole remains unchanged. `ordinaryRealization_existsUnique`, `ordinaryRealization_eq`, and `ordinaryModuleEvalG_comp` are proved without new holes. Added one hole, `AlgebraicGeometry.ProEtale.VaryingRing.ordinaryClopenEvaluation`, in its own module and DAG node. Thus two original holes are reduced to one strictly smaller single-square normalization lemma; this is a decomposition, not a claim that their full dependency closure is proved.

## No longer needed

No existing module is withdrawn. Both arbitrary-ring strict-tower pasting laws remain used. The direct nested-projection calculations previously planned separately for the two ordinary pasting identities are replaced by one shared single-square normalization and explicit categorical transport. No unit statement or unit step is bypassed. No previously present import is removed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original proof plan omitted the Lean compatibility between the actual varying-system comparison and the actual strict-tower comparison. This compatibility needs the specified adjunction and compositor normalizations; objectwise isomorphisms alone do not suffice. Only ordinary morphisms are detected by coefficient evaluation here. No faithfulness of evaluations on arbitrary derived morphisms is assumed.

## New nodes

`lem-sp-varying-ring-ordinary-clopen-evaluation`, realized by `Sheaf.AlgebraicGeometry.VaryingRingOrdinaryClopenEvaluation`: compatibility of ordinary component/constant/degree-zero realization with the specified compositors and one clopen square. Its statement contains no vertical or horizontal pasting identity. The full natural-language proof and source are in the theorem docstring and node.

Change record: `coord/changes/C8-varying-ring-ordinary-pasting-local-commands.md` documents the local proof commands flagged by static preflight.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
