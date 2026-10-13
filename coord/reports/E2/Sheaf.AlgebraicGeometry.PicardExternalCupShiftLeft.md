## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.PicardExternalCupShiftLeft`
with a complete Lean reduction following the left-coefficient induction of Stacks
Tag 0BED (`lemma-kunneth`, after `equation-kunneth-on-cech`). The original theorem's
signature, visibility, and both public imports are unchanged.

The proof constructs the cokernel of an existing acyclic quasi-coherent embedding,
proves both lower cohomological bounds from the full long exact sequence of derived
global sections, chooses normalized realizations, and applies the supplied induction
hypothesis to those two coefficients. It then uses Mathlib's five lemma on an exact
homology ladder and explicitly rewrites the specified homology map as a composite
of three isomorphisms.

Added proof imports for QuasicoherentAcyclicEmbedding, the source library's
QuasicoherentCokernel, FullLongExactSequence, PicardExternalCupLeftHomologyLadder,
and Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four. Added the new ladder module
and its node, and updated the parent node's proof, proof_deps and proof_origin.
No definitions or existing statements changed; no forced adaptations.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.picardExternalCupCochain_isIso_shiftLeft`
(node `lem-sc-picard-external-cup-shift-left`). Its proof has no sorry.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.picardExternalCupCochain_left_homology_ladder`
(node `lem-sc-picard-external-cup-left-homology-ladder`), in the new module
`Sheaf.AlgebraicGeometry.PicardExternalCupLeftHomologyLadder`. Its proof is exactly
`by sorry`; its docstring gives the source and full construction in words.

This is a one-for-one decomposition, not a proof of the whole import closure:
one upper hole closed, one strictly smaller geometric construction left, net zero
holes. The new theorem has no bound, induction hypothesis, or conclusion asserting
invertibility of the specified map. The acyclic embedding/cokernel argument, the
bound calculation, the applications of induction, the five lemma, and the final
transport are all proved in the original module. Existing imported holes, notably
the cochain existence theorem, are used as intended by this stage and are unchanged.

Both modules compile cleanly with lcompile.py --all (no errors or warnings).
The edge cases were checked in the statements and proof: for d=0, d<p still gives
p>=1 and d+1<p+1, so nothing assumes H^0(Q)=0; n=0 uses the initial ladder padded
by two zero objects, rather than any negative-degree induction hypothesis. Zero
coefficients and empty schemes require no exclusion. The ladder's n>0 row has
E^(n-1), Q^(n-1), F^n, E^n, Q^n; the n=0 row has 0, 0, F^0, E^0, Q^0.

## No longer needed

No original imports removed and no whole modules pruned. The original two public
imports are required by the unchanged statement. The second reader removed the
redundant new public import `Mathlib.Algebra.Homology.ShortComplex.ShortExact`
from the ladder module: PicardExternalCupCochain already exposes it transitively.

The parent no longer uses these original proof-dependency nodes directly:
`def-sc-ringed-space-module-cohomology`,
`lem-sc-cech-comparison-map-iso-affine`,
`lem-sc-cech-comparison-map-naturality`,
`lem-sc-cech-comparison-natural`,
`lem-sc-picard-affine-diagonal-intersections`,
`lem-sc-picard-cech-cup-pullback-compat`,
`lem-sc-picard-kunneth-resolution-model`,
`lem-sc-qcoh-cech-total-tensor-nat-iso`,
`lem-weil-pbc-fibre-product-affine-spectra`,
`lem-weil-pbc-module-pullback-affine-sections`,
`lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`,
`pqf-def-coherent`, and `pqf-lem-affine-vanishing`.
These are not claimed to be globally pruned: the geometric dependencies move to
the ladder node, the definitions remain statement dependencies, and affine vanishing
remains behind the affine comparison theorem.

## Where the brief, the DAG or earlier work was wrong

The original module had only its two public imports, despite the standing brief's
description of proof dependencies as already imported. Its planned dependency
statements do not themselves expose a short exact external-cup homology ladder.
The new node records precisely that missing geometric step, including the
connecting-map compatibility. Existing exact affine sections, tensor exactness,
and long-exact-sequence naturality nodes support its construction.

The bound calculation needs only the exact segment H^p(E) -> H^p(Q) -> H^(p+1)(F),
not a separately chosen dimension-shifting isomorphism. Mathlib's zero-outer-terms
lemma proves the vanishing of Q directly. No mathematical error in the original
statement or source was found. The Stacks tex files are absent on this machine;
Tag 0BED was read at https://stacks.math.columbia.edu/tag/0BED. The unit record
sk-prop-av-cube has empty realized lists; the existing unit route is preserved.

The ancestor helper returns None for this parent because its earlier created.item
is a module name; the new node inherits the parent's explicitly recorded blueprint
ancestor thm-sc-theorem-of-cube and adds the parent to the recorded via chain.

FullLongExactSequence is used as a generic homological-algebra tool: it gives the
exact segment of derived global sections needed for the bound calculation. The
source-library quasi-coherent cokernel theorem is also reused, rather than restated.

A source-only dependency traversal found the same four cycles in both the original
parent closure and the sandbox closure; no new cycle was introduced. Existing
cycles to report upward: sheaf-algebraic-structures-objects with its abelian
component, the same objects node with its ring component, horseshoe-delta-functor
with derived-functor-long-exact, and higher-direct-image-presheaf with
flat-base-change-open-choices. These unrelated records were not edited. In
particular, FullLongExactSequence's Lean imports HorseshoeDeltaFunctor, while the
existing DAG points both ways; the library's Lean import graph passes the dry run.

## New nodes

`lem-sc-picard-external-cup-left-homology-ladder`: constructs a five-term exact
ladder from any specified short exact sequence of left quasi-coherent coefficients
and three normalized maps. It returns isomorphisms identifying its center with the
specified tensor-total and product homologies and the central commuting equality.
Its outer-invertibility implications come from the middle and quotient normalized
maps. It does not assert the center is invertible; the parent proves that with the
five lemma. Source: Tag 0BED's short exact coefficient diagram. Searches were run
through msearch.py: LeanSearch was unavailable; LeanFinder and Loogle returned
generic homological-algebra results; Mathlib grep found no geometric ladder.
Repository and whole-blueprint searches found no duplicate. No change records.


## Second reading by E2

1. Interface: PASS. Read the full diff against the repository. The parent changes
   only its proof and adds five plain proof imports. Its theorem signature,
   visibility, original public imports, and docstring are byte-for-byte unchanged.
   There are no existing definitions changed and no forced adaptations. Existing
   node changes are confined to proof, proof_deps, and proof_origin.
2. Proof and trust: PASS as a decomposition. Recompiled both modules with
   lcompile.py --all, and compiled scratch copies with #print axioms for both
   declarations. Each reports only propext, Classical.choice, Quot.sound, and
   sorryAx. The only delivered sorry is the named public ladder theorem listed
   above; there are no definitions, forbidden declarations, or hidden holes.
   The parent eliminates existential witnesses inside a proof of a proposition;
   it introduces no definition choosing arbitrary data from an unproved theorem.
3. Split statement: PASS. Independently read Stacks Tag 0BED's short exact
   coefficient diagram and the normalization/model definitions. Exact affine
   sections and field tensor exactness produce the two short exact complexes;
   connecting-map naturality gives the ladder. Tensor Kunneth cycle spanning
   identifies every specified normalized homology map with the transported cup
   map. For n=0 the two negative-degree terms are zero; for n>0 the source terms
   are tensor-total homology of E,Q,F,E,Q in degrees n-1,n-1,n,n,n (the G factor
   remains fixed), and the target terms are the corresponding product homologies.
   The n=0, d=0, zero-coefficient, and empty-scheme cases require no extra
   hypothesis. This is the geometric exact-diagram construction, strictly a part
   of the parent argument, without its bound, induction, or IsIso conclusion.
   New searches used connecting-homomorphism naturality and tensor-product
   cohomology terms: LeanFinder returned group-cohomology lemmas, Loogle had no
   match for ComposableArrows.Exact, and Mathlib grep found no match. Repository
   searches by ladder, connecting, short exact, and dimension shift found no
   existing geometric ladder. Closing it would require substantial geometric
   formalization, not a short proof repair.
4. Route and pruning: PASS. The parent uses the existing acyclic embedding,
   actual categorical cokernel, full derived long exact sequence, normalized
   cochain existence, and Mathlib five lemma. Checked exactness at Q and both
   arithmetic inequalities, and checked the final central-map conjugation.
   All thirteen old proof dependencies absent from the new parent proof_deps
   are listed under No longer needed. The cube unit's realized fields are empty
   in the repository; no unit realization or chapter route is bypassed. The
   original public imports support its signature; all five new proof imports
   supply declarations used by the proof. Removed one redundant public import
   of ShortComplex.ShortExact from the new ladder and recompiled successfully.
5. DAG: PASS. Both proof_deps lists equal the union of their step uses. The
   parent steps match the Lean proof, including the direct zero-outer-terms
   argument rather than a claimed chosen dimension-shifting isomorphism. The
   new node has its source, complete proof, searches, split status, creation,
   blueprint ancestry, chapter/unit, and verbatim Lean statement. The new
   theorem's docstring supplies the construction and its boundary cases.

Second-reading changes: removed the redundant new ladder import and updated
this report. No proof, statement, definition, or node repair was needed. The
result remains one hole closed and one hole added, a net-zero decomposition.
