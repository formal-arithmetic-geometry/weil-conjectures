## What changed

Proved `AlgebraicGeometry.relativeMayerVietoris` from the canonical relative
Mayer--Vietoris triangle construction and Mathlib's
`CategoryTheory.Pretriangulated.isIso₁_of_isIso₂₃`. Its signature is unchanged.
The two private helpers prove invertibility of a biproduct of two isomorphisms
and transport invertibility along an equality. They contain no holes.

Added `Sheaf.AlgebraicGeometry.RelativeMVCanonicalTriangles`, containing the
single named intermediate theorem `AlgebraicGeometry.relativeMV_canonicalTriangles`.
It constructs the two distinguished triangles and their morphism with exactly
the original theorem's local maps as components. It assumes none of the three
local isomorphism hypotheses and asserts no global isomorphism. This is the
geometric construction/naturality portion of the argument, separate from the
biproduct and two-out-of-three reasoning proved in the delivered main module.
Updated the parent node's proof, proof dependencies and proof origin accordingly.

Sources read: Stacks [Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9),
induction diagram, and [Tag 08HY](https://stacks.math.columbia.edu/tag/08HY),
the definition by adjunction mates; also
[Tag 08BV](https://stacks.math.columbia.edu/tag/08BV) and
[Tag 08HZ](https://stacks.math.columbia.edu/tag/08HZ), the absolute and relative
Mayer--Vietoris triangles. The named theorem's docstring and new node
explain the construction, canonical transports, vertical pasting, and boundary
square. The unit record `sk-thm-picard-semicon` has empty realized arrays;
its route is unchanged, and the original relative Mayer--Vietoris induction
step is retained.

## Proved and sorry left

Closed: `AlgebraicGeometry.relativeMayerVietoris`, the only original hole.
There are no remaining holes in the main module.

Added: `AlgebraicGeometry.relativeMV_canonicalTriangles`, with proof exactly
`by sorry`, node `lem-pc-relative-mv-canonical-triangles`, in the new module.
Its statement requires actual distinguished triangles and an actual morphism,
including the connecting square and all three precise component identities.
It is not an invertibility implication or the main theorem under another name.
The delivery is a decomposition: one upper hole closed, one geometric hole
added; it is not a complete proof without unresolved dependencies.

The combining proof proves that the middle component is invertible by constructing
the biproduct isomorphism from the two supplied inverses, transports the overlap
hypothesis to the third component, applies the distinguished-triangle theorem,
and transports the first component to the original global map. Local compilation
of both modules succeeded. Generic equality transport avoids slow dependent
elaboration of the expanded base-change expressions.

Edge cases checked on the construction: empty U or V gives zero open terms;
U = V = top gives the usual diagonal/difference triangle; zero complexes give
zero triangles. No properness, flatness, nonempty-open or boundedness hypothesis
is needed. The base-change maps are the original canonical maps, not arbitrary
arrows.

## No longer needed

Removed direct proof imports from the main module:

- `Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris`, node
  `lem-pc-rf-mv-triangle-naturality`: its inverse-image-open formulation does not
  expose the exact fibre-product local maps needed by the hypotheses.
- `Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`, node
  `lem-pc-derived-direct-image-composition`: used in the new construction's plan,
  so it is not pruned from the overall mathematical argument.
- `Sheaf.AlgebraicGeometry.DerivedMayerVietorisTriangle`, node
  `lem-pc-derived-mayer-vietoris-triangle`: retained through the new construction's
  dependency `DerivedMayerVietorisFunctorial`; not pruned from the argument.

The parent no longer directly depends on the original naturality node. No claim
is made that it is unreachable from every other target branch. Its affine tensor
comparison and general pre-derived-adjunction modules are not imported solely
for that original formulation. No public import was removed or changed. The second reader also removed the redundant
plain import of `DerivedDirectImageCompositionUnbounded` from the new module: it is
already publicly imported by `DerivedMayerVietorisFunctorial`. This does not remove
the composition node from the construction plan.

## Where the brief, the DAG or earlier work was wrong

The original naturality declaration expresses local components before the
composition identifications, on inverse-image opens rather than the specified
fibre products. It uses `Classical.choice (derivedPullback_openRestriction_iso ...)`
whose theorem only asserts existence of a natural isomorphism. Therefore its
signature supplies neither the canonical comparison identities nor the vertical
pasting formula required to transport the original local hypotheses. The
existing direct-image composition theorem also only asserts `Nonempty` of an
isomorphism, without a base-change compatibility equation. A direct application
of those declarations does not finish the planned step. I did not change their
interfaces or use a claimed equality for arbitrary chosen comparisons.

The old node's description conflates Tag 08BV (the absolute triangle) with
`lemma-unbounded-relative-mayer-vietoris`, which is Tag 08HZ. Both source lemmas
were read, and the new node records the two labels and tags separately.

The new construction theorem states the canonical local component identities
explicitly. Its proof obligation packages the construction and compatibility
steps, while the actual gluing inference is proved in the original module.
This preserves the paper's induction argument and all original hypotheses.

LeanSearch returned HTTP 500 and is recorded as unavailable. LeanFinder, Loogle
and Mathlib grep were run; none supplied the canonical relative triangle
construction. The existing Mathlib two-out-of-three theorem is used directly.
No definitions, target signatures, or modules held by another group were changed.

## New nodes

`lem-pc-relative-mv-canonical-triangles`, in
`dag/nodes/sec-picard-framework/lem-pc-relative-mv-canonical-triangles.json`, records
`AlgebraicGeometry.relativeMV_canonicalTriangles` in
`lean/Sheaf/AlgebraicGeometry/RelativeMVCanonicalTriangles.lean`. This is the
canonical relative triangle construction and comparison morphism from Tag 0DJ9's
induction diagram, with the component identities written in the same encoding
as the original statement. The node lists the construction and mate calculation
as proof steps, with actual search results and the source references. No change
record is needed: all existing signatures and public imports are unchanged.


## Second reading by N3

1. **Existing interface: PASS.** Read the complete repository/sandbox diff.
   The existing `relativeMayerVietoris` signature is byte-for-byte identical,
   including all three local composites and every hypothesis. The original
   docstring and three public imports are unchanged. The existing node changes
   only `proof`, `proof_deps`, and `proof_origin`. No definitions were changed,
   no change record or forced adaptation is required.
2. **Proof and trust: PASS as a decomposition.** Both delivered modules compile
   locally without errors or warnings. Scratch copies with `#print axioms`
   show only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for the
   main and split theorem; the biproduct helper uses only the three permitted
   axioms, and equality transport uses none. The only delivered hole is the
   named theorem `relativeMV_canonicalTriangles`, exactly `by sorry`, with its
   source, full construction proof docstring, and node. There are no definitions
   or forbidden trust escapes in either delivered module. The existential
   triangle witnesses are eliminated inside a proof of a proposition; no data
   definition chooses arbitrary witnesses from this unproved existence theorem.
3. **Split statement: PASS.** Read the Tag 0DJ9 induction diagram and the
   absolute/relative triangle and adjunction-mate source proofs in the sandbox's
   Stacks texts. The triangle assertion has no local invertibility hypotheses
   and no global invertibility conclusion, and is strictly the geometric part
   of the argument. Its component identities use the original precise maps,
   including the pullback composition comparisons pinned by their derived
   universal property. Empty U (necessarily V = top), identical top opens,
   disjoint covering opens, and zero complexes give respectively the elementary
   zero-term, diagonal/difference, split, and zero triangles; none contradicts
   the assertion. Independent LeanFinder search for "Derived direct image open
   cover distinguished triangle comparison morphism natural connecting maps"
   returned general homological-functor and mapping-cone compatibility results;
   Loogle for `CategoryTheory.Limits.biprod.mapIso` found the exact biproduct
   constructor already used; Mathlib grep for
   `isIso₁_of_isIso₂₃|mayerVietoris|mayer_vietoris` confirmed the two-out-of-three
   theorem and ordinary sheaf Mayer--Vietoris results. Searches in both Lean
   source roots found no exact canonical fibre-product component construction.
   Existing naturality/composition declarations leave the stated comparison
   compatibility unexposed; the split theorem cannot be closed in a few minutes
   merely by applying them.
4. **Route and pruning: PASS.** The main proof performs the biproduct and
   two-out-of-three argument directly using Mathlib, after the geometric
   construction. All three removed original direct dependency imports/nodes are
   accounted for under No longer needed; the triangle and composition nodes
   remain in the construction plan. The unit `sk-thm-picard-semicon` has empty
   realized arrays, and the relative Mayer--Vietoris induction step is retained.
   Public imports in the new module provide signature notation and structures;
   the construction-plan imports are plain imports. No global module pruning
   count or positive net hole reduction is claimed.
5. **DAG: PASS.** Checked both delivered JSON nodes against the Lean signatures
   and proof bodies. The new node's `lean.statement` matches the theorem header
   byte-for-byte and includes the source, three search kinds (plus LeanFinder),
   proof steps and their dependency union, origin, created/group/item metadata,
   blueprint, chapter, unit, and Lean record. The parent records construction,
   proved biproduct reasoning, and Mathlib two-out-of-three as actually used.

Second-reading repair: removed the redundant plain direct-image-composition
import from `RelativeMVCanonicalTriangles`, already reexported by the retained
functoriality import. No proof or statement needed rewriting. Holes closed:
`AlgebraicGeometry.relativeMayerVietoris` (1); holes added:
`AlgebraicGeometry.relativeMV_canonicalTriangles` (1). Net zero: decomposition.
