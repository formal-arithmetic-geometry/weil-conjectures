## What changed

`Sheaf.AlgebraicGeometry.RightAdjointTensorLocusLocalizing` now proves
`AlgebraicGeometry.rightAdjointTensorLocus_localizing` with its signature and visibility
unchanged. The proof identifies its existential predicate with invertibility of a canonical
natural comparison by uniqueness of the pinned projection isomorphism (`Iso.ext_inv`). It
proves retract closure by lifting ambient retracts to the full subcategory and using
`NatTrans.retractArrowApp` and `MorphismProperty.of_retract`. Isomorphism closure follows by
applying retract closure to the inverse ambient image of an object isomorphism.

The coproduct clause is proved in the original module. It constructs a quasi-coherent cofan
on the specified B and proves its universal property directly from the given ambient cofan.
The inclusion creates coproducts; pullback preserves them by its adjunction, tensor preserves
them by the smaller tensor obligation, and the target inclusion reflects colimits. Mathlib's
`isIso_app_coconePt_of_preservesColimit` then proves comparison invertibility at B. This uses
exactly the supplied hsums and accepts empty index types.

Three new modules state strictly smaller obligations: canonical projection/comparison
naturality, shift and triangle closure, and tensorRight coproduct preservation. No definition
or existing statement changed. Only proof imports of the original module changed; its public
imports remain identical. Each new theorem has its source and complete proof plan in its
docstring, and a matching DAG node. The original node records the implemented reduction.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.rightAdjointTensorLocus_localizing`
(`lem-sc-right-adjoint-tensor-locus-localizing`). No direct sorry remains in the item.

Added three named holes, each exactly `:= by sorry` in its own public module:

- `AlgebraicGeometry.rightAdjointTensorComparison_natural`
  (`lem-sc-right-adjoint-tensor-comparison-natural`), in
  `Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonNatural`.
- `AlgebraicGeometry.rightAdjointTensorLocus_triangles`
  (`lem-sc-right-adjoint-tensor-locus-triangles`), in
  `Sheaf.AlgebraicGeometry.RightAdjointTensorLocusTriangles`.
- `AlgebraicGeometry.derivedTensorRight_preservesCoproducts`
  (`lem-sc-derived-tensor-right-coproducts`), in
  `Sheaf.AlgebraicGeometry.DerivedTensorRightCoproducts`.

This is a decomposition, not an axiom-free proof of the original theorem: one upper hole
closed and three smaller holes added. The isomorphism, retract and coproduct arguments are
actual checked Lean; shift and triangle closure are delegated together. The new naturality
theorem asserts the canonical comparison and its components, not closure of any locus; the
tensor theorem concerns a single tensor functor on any scheme. Neither repackages the whole
original conclusion. All four delivered modules compile in dependency order without warnings.

## No longer needed

Removed the proof import
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`; its recorded dependency
`lem-pc-projection-formula` supplies only the invertible-module higher-direct-image statement,
which is not used by this proof. The canonical unbounded projection/comparison obligation is
now explicit in `lem-sc-right-adjoint-tensor-comparison-natural`.

Removed the direct proof import `Sheaf.AlgebraicGeometry.DerivedQCohDirectSums` and the original
proof dependency `lem-pc-derived-qcoh-direct-sums`. The actual proof uses its narrower supporting
module `Sheaf.AlgebraicGeometry.DerivedQCohDirectSumsAux`, specifically
`lem-pc-derived-ambient-has-coproducts` and `lem-pc-derived-qcoh-closed-coproducts`, to establish
coproduct preservation by the inclusion. The hypotheses already supply coproducts in both
quasi-coherent subcategories. This is pruning of the item's proof dependencies; no claim is
made that these modules are globally unreachable from other targets.

The definition nodes `def-pc-derived-direct-image`, `def-pc-derived-pullback`, and
`def-pc-scheme-derived-tensor-structure` remain statement dependencies and public imports.
Their duplicated original proof edges are replaced by the new intermediate theorem edges;
these definitions are not pruned from the library. No blueprint unit statement or unit step
was bypassed; the unit's realized arrays are empty, and the source's localizing argument stays.

## Where the brief, the DAG or earlier work was wrong

The original plan says `lem-pc-projection-formula` supplies the displayed derived pf, but its
recorded Lean theorem is
`AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_tensorObj_pullback_iso`.
That theorem covers an invertible module and an individual higher direct image, rather than
arbitrary objects of the unbounded derived category. The source node itself records this
limitation. No weakened replacement was used; the new natural comparison theorem states the
full required pf equation and naturality explicitly.

A short proof via the existing derived monoidal-closed instance cannot simply be applied in
the arbitrary localization universe w: upstream's closedness instance requests
`IsGrothendieckAbelian.{w}`, whereas module sheaves here supply it in universe u. An attempted
proof deriving a tensor-Hom adjunction with K-injective resolutions in u encountered unresolved
K-flat derivability instances and exceeded the single-file compile limit. That attempt is not
part of the delivery. The tensor obligation's proof plan uses termwise coproducts and K-flat
comparisons throughout the chosen universe w, so it adds no universe equality assumption.

Read Stacks Tag 0A9U and Section 48.8, equation (the project server), including the explicit assertions
of functoriality and triangle compatibility. Checked the statements on zero objects, shift
zero, zero triangles and empty coproducts. The new naturality and triangle statements omit
coproduct-existence assumptions and hsums because neither operation needs them. LeanFinder,
Loogle and grep found the component category-theory lemmas used above; LeanSearch was
unavailable and its failures are recorded honestly in searches.jsonl and the new nodes.

## New nodes

`lem-sc-right-adjoint-tensor-comparison-natural` records the first geometric step: existence
and naturality of the canonical comparison, with its concrete source functor and component
formula. It asserts no component is invertible and no closure property.

`lem-sc-right-adjoint-tensor-locus-triangles` records exactly the shift and third-triangle-object
parts of the source argument. It uses the natural comparison but asserts no isomorphism,
retract or coproduct closure.

`lem-sc-derived-tensor-right-coproducts` records coproduct preservation by the shared ambient
derived tensor functor, for arbitrary tensor factors and independent universes. It asserts
nothing about the right adjoint or its comparison locus. Its plan uses
`lem-pc-kflat-derived-tensor-comparison` and `lem-pc-derived-ambient-direct-sums`.

All new nodes belong to sec-picard-framework / sk-thm-picard-duality and descend from the
original node's blueprint ancestry. No change record is needed: existing signatures,
definitions, visibility and public imports are unchanged, and there are no forced adaptations.

## Second reading by C1

1. Compared the delivered item module with the repository version. The target declaration signature and all existing declarations are byte-for-byte unchanged; only proof imports and the target proof body changed. Verdict: pass.

2. Compiled all four delivered modules with `lcompile.py --all`; compilation completed without errors or warnings. The target has no remaining sorry. The three split-off declarations are explicit named theorems with documented sources and no sorry in definitions. Verdict: pass.

3. Checked the three split-off statements against their source descriptions and searched the library for existing declarations. Each is a strictly smaller obligation: comparison naturality, triangle/shift closure, and tensorRight coproduct preservation. Their DAG nodes, docstrings, and source references agree. Verdict: pass.

4. Reviewed the proof from the target downward. The proof uses the canonical comparison, triangle closure, and tensor coproduct obligations, then proves isomorphism, retract, and coproduct closure directly. Removed proof-only imports are recorded above; no shorter existing theorem was found. Verdict: pass.

5. Compared the DAG node proof, proof_deps, and proof_origin with the Lean proof and checked the unit record. The original node records the implemented reductions, and all three new nodes contain the required metadata. The unit route remains intact. Verdict: pass.

Changes made during second reading: added this review section to satisfy the delivery contract; no Lean or DAG changes were needed.
