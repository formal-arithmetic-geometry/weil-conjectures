## What changed

Closed the body of `AlgebraicGeometry.conductorIdealZeroIntersection`, preserving its
existing signature byte for byte. The arbitrary-open zero-intersection conjunct is
proved directly using the component cover, kernel supports, and the reduced-scheme
basic-open criterion. The restriction conjunct applies the new, privately imported
`ClosedImmersionDisjointIdealTwist.lean` helper to `i a` and `j.ker`.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.conductorIdealZeroIntersection`
(node `lem-sc-conductor-ideal-zero-intersection`). Its first conjunct has a direct proof;
the second still depends on the following new hole.

Hole added and left: `AlgebraicGeometry.Scheme.Modules.closedImmersion_disjointIdeal_twist`
(node `lem-sc-closed-immersion-disjoint-ideal-twist`). Its proof is exactly `by sorry`,
and its docstring gives the affine calculation, gluing, adjunction transport, arbitrary
linear comparison, and passage to all opens.

This is a decomposition: one original hole closed and one lower hole added, net zero.
The main theorem is not claimed to be free of `sorryAx`. No other holes were added.
Both modules compile without errors or warnings. Explicit `#print axioms` checks show
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for both declarations.

## No longer needed

Removed the original `Sheaf.RingTheory.ReducedIdealsZeroIntersection` import and the old
proof dependency `lem-sc-reduced-ideals-zero-intersection`: the direct support proof
replaces the affine ring calculation. The other five original proof dependencies are
retained in the two new proof steps, either for the support argument or for the
invertible-module and tensor interfaces of the helper application.

Also removed the redundant private import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct` (already publicly exported by
`TensorPullback`) and the first worker's unused private import
`WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`. No global reachability
claim is made for these modules; the maintainer computes pruning in the full closure.

## Where the brief, the DAG or earlier work was wrong

The original affine route is valid, but unnecessary for the zero-intersection clause:
Mathlib's `basicOpen_eq_bot_iff` already works on arbitrary opens of a reduced scheme.
The sandbox DAG still had an affine reduction not present in the proof, described
applying the helper to `j` instead of `i a`, and did not give `proof_deps` as the union
of the steps' uses. These have been repaired.

The first worker renamed `hcomponents` and `hdistinct`. Their original names have
been restored; explicit proof references preserve a warning-free unchanged interface.
The unnecessary change record was removed: no existing statement, definition, or
public import changes. The new helper's status is now `split`, its ideal-image notion
and definition citations are explicit, and its docstring accurately describes its
actual tensor-power comparison statement.

## New nodes

`lem-sc-closed-immersion-disjoint-ideal-twist`, in
`dag/nodes/sec-curve-estimates/lem-sc-closed-immersion-disjoint-ideal-twist.json`, carries
the remaining restriction-and-tensor theorem in
`Sheaf.AlgebraicGeometry.ClosedImmersionDisjointIdealTwist`. It assumes, rather than
proves, zero intersection and requires no component-cover or reducedness hypotheses.
The statement, source, word proof, search records, creation record, blueprint origin,
and Lean record are present. No change record is needed.

## Second reading by G1

1. Compared the delivered main module with the repository module by `diff` and checked
   the text between the theorem name and `:= by` separately. The first worker's binder
   renamings were the only signature differences; restored them. The final existing
   signature and docstring are byte for byte unchanged. No definitions or public
   imports of the original module change, and no other existing module is adapted.
2. Compiled both modules in import order with `lcompile.py`. Both compile without
   errors or warnings. Inspected both full files for forbidden declarations and hollow
   data: none. There is exactly one named helper `sorry` and no `sorry` in the main
   proof. A scratch copy with explicit `#print axioms` gives the axiom lists reported
   above; the scratch copy was removed. The only chosen object is an adjunction on
   fixed functors; uniqueness of adjoints supplies precisely the transport used in
   the word proof, rather than an arbitrary unspecified geometric witness.
3. Read Stacks Tags 09NW and 09NX at https://stacks.math.columbia.edu/tag/09NW and
   https://stacks.math.columbia.edu/tag/09NX (the local varieties.tex is absent).
   Checked the helper against the quotient calculation: on a trivializing affine,
   K -> (K+J)/J has kernel K intersect J and is onto. The word proof glues sheaf
   morphisms and evaluates their inverse; it never tensors sections on arbitrary
   opens. A different adjunction precomposes the ideal map by an isomorphism, and a
   linear e preserves multiplication by its image ideal, so arbitrary e is allowed.
   Tested I=0, J=0, m=0, empty X, empty opens, and A=k[x,y]/(xy), I=(x), J=(y):
   the quotient map identifies (x) with (x) in k[x]. Empty X forces I=0 from hzero;
   J=0 reduces to an ambient linear isomorphism. Reducedness is not needed by this
   helper. It is a genuine reduction because the zero-intersection hypothesis is
   established by the main proof, with all component hypotheses removed from the
   helper. Repeated LeanFinder, Loogle and grep searches with new queries, logged in
   searches.jsonl. Loogle did not recognize the upstream toModulesι identifier;
   this is recorded as an unsuccessful query, not evidence of a match. Also searched
   local Sheaf and upstream Lean. Read IdealTensorImageComparison,
   ClosedImmersionUnitQuotient, ClosedImmersionUnitKernel,
   ClosedImmersionIdealTensorSections, and the ideal-product/quotient DAG nodes.
   They compute ideal images, kernels, or top-open sections, but do not directly
   supply the required disjoint-ideal restriction isomorphism on every open.
4. Checked the proof from its first conjunct down. For a point in the basic open,
   the cover puts it in i(a) or j; range_subset_ker_support and range_subschemeι
   lift it to the corresponding closed subscheme. Membership in idealOfOpens kills
   the pulled-back section, so preimage_basicOpen is empty, a contradiction.
   basicOpen_eq_bot_iff then gives s=0. This closes the actual algebraic hole without
   restating it. The tensor helper cannot be closed in a few minutes from the nearby
   interfaces. Removed the two redundant private imports and confirmed recompilation.
   The old unused ring lemma is listed under No longer needed. The unit record
   sk-thm-curveestimate.json realizes thm-sc-proper-cohomology and no proof steps;
   neither this item nor the old ring lemma realizes a unit step. The conductor
   equality in the blueprint ancestor's route is still used, so no unit is bypassed.
5. Read both delivered nodes against the final Lean. The main node now has exactly
   the direct support argument and the helper application to i(a), with proof_deps
   equal to the union of their uses and proof_origin describing the actual route.
   The new node explicitly defines I1 and the multiplication images, cites all
   needed definition nodes, records the logged searches, has status split, and its
   Lean signature agrees with the helper. Its proof_deps likewise equals the union
   of its two steps' uses. Existing node changes are restricted to stage-3-owned
   fields. No unit record, target, or maintainer-owned field is changed.

Second reading changed: restored existing binder names; removed redundant imports and
an unnecessary change record; corrected DAG route, dependency union and helper metadata;
clarified the helper word proof and recorded decomposition accounting. The mathematical
support proof and the true remaining helper statement were retained.
