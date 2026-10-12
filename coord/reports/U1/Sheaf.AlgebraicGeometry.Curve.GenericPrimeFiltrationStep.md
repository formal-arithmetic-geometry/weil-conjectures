## What changed

Reduced `AlgebraicGeometry.IsConnectedCurve.subsingleton_generic_prime_filtration_step`
without changing its signature. The proof constructs the two image/cokernel short exact
sequences and explicitly uses Ext exactness in degrees one and two. It proves continuity
of generic-zero sections using the existing function-field limit and section-continuity
lemmas, and transports the normal constant comparison from the residue field to the
function field. Only H¹ of the cokernel is needed.

Added one module `Sheaf.AlgebraicGeometry.Curve.GenericDirectImageCounit` for the geometric
counit isomorphism. All new helpers in the item are private and proved. The two delivered
modules compile locally in import order. No target, definition, or public signature changed.

## Proved and sorry left

Closed the item's sole hole:
`AlgebraicGeometry.IsConnectedCurve.subsingleton_generic_prime_filtration_step`
(node `lem-sc-generic-prime-filtration-step`). This is a decomposition, not a sorry-free
proof: one upper hole closed and one strictly smaller geometric hole added.

The sole new sorry is
`AlgebraicGeometry.Etale.isIso_generic_direct_image_counit`
(node `lem-sc-generic-direct-image-counit`). It asserts an adjunction counit isomorphism
for arbitrary generic sheaves and has no curve-cohomology, prime, affine, smoothness,
vanishing, or short-exact-sequence hypotheses. The item's combination proof is complete.

The proved private helpers are `isIso_constant_generic_unit`,
`genericVanishing_of_isZero_upperStar`, and `genericVanishing_cokernel_lowerStar_epi`.

## No longer needed

Removed direct imports of `Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk`,
`Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`, and
`Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence` from the item.
The unrestricted stalk comparison remains a planned dependency of the new counit lemma;
it is not globally obsolete. The inverse-image module-coefficient theorem
`prop-weil-pbc-inverse-image-modules-exact` is unnecessary on this route: ordinary abelian
inverse image preserves cokernels by its already implemented adjunction. The general
right-derived theorem `lem-weil-pbc-derived-functor-long-exact` is unnecessary here:
Mathlib's proved Ext exact-sequence API applies directly to the definition of Sheaf.H.
The original torsion-specific node `lem-sc-zero-generic-acyclic` is replaced by the precise
existing `lem-sc-generic-vanishing-acyclic`; both use the same source module.
No other import is removed. The image cokernel needs only H¹ vanishing, not H² vanishing.
These pruning claims concern this argument, not other users of these modules.

## Where the brief, the DAG or earlier work was wrong

The original plan's torsion calculation and H²(Q) vanishing are stronger than required.
The existing generic-acyclicity declaration takes a covering-sieve hypothesis rather
than merely a zero generic restriction; the delivered proof now supplies that hypothesis
by section continuity. The generic counit isomorphism was used in the plan but had no
standalone declaration; the new node makes that geometric step explicit.

The unit record has no realized statement or steps, and its route has been retained.
The normal comparison uses `lem-fin-normal-generic-constant` as the same black-box tool
as the original plan; smooth normality is the existing source theorem. Edge cases checked:
zero sheaves, identity epimorphisms, and split exact sequences give a zero cokernel;
when the generic inclusion is an isomorphism its counit is invertible by equivalence.
The new counit statement imposes no finiteness or torsion condition and works in every
characteristic. It does not use the affine cohomological-dimension conclusion.

LeanSearch returned HTTP 500 and was recorded as unavailable. LeanFinder and source grep
returned no matching generic counit theorem. Blueprint search for generic counit and
generic cokernel returned no matching blueprint statement. The named blueprint source
file is absent in this local read-only checkout; its paragraph-3 argument is provided
in the item's node and docstring, which were read in full.

## New nodes

`lem-sc-generic-direct-image-counit`, module
`Sheaf.AlgebraicGeometry.Curve.GenericDirectImageCounit`: the geometric counit for the
generic inclusion, with its stalk-comparison, germ-compatibility, and conservativity
proof written in the node and docstring. This isolates only the geometric input to the
cokernel argument; continuity, image exactness, constant transport, and cohomological
assembly are all proved in the item. No change record is needed.

## Second reading by U1

1. **Visible declarations unchanged — PASS.** Compared the item with the repository using
   `diff -u`. Its existing theorem signature and docstring are byte-for-byte unchanged;
   there are no existing definitions to alter. All added imports in the item are plain
   proof imports. The new module has only one public theorem and no definitions. No
   target or other existing public interface changes, so no change record is required.
2. **Proof and axioms — PASS with the reported open geometric input.** Compiled both
   modules in import order using `lcompile.py --all` (2.3 s and 13.7 s). Read the exactness,
   image factorization, continuity, residue-field transport, and Ext arguments in full.
   The item has no textual sorry. The new counit theorem has exactly the one named public
   `:= by sorry` reported above, with source, full proof docstring, and its node. There
   are no forbidden declarations or hollow definitions. A scratch copy with
   `#print axioms` for the main theorem, all three private helpers, and the counit theorem
   compiled: each uses only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The last axiom is expected from the open counit and existing upstream inputs; this
   is not a proof independent of sorry. The arbitrary affine open in the continuity
   proof is chosen from the already implemented nonempty affine-open type, not from a
   new existence theorem with an unproved proof.
3. **Split statement — PASS.** The counit statement is true for any integral scheme:
   the generic inclusion is affine, since over every nonempty affine open it is the
   fraction-field spectrum; its strict-local base change at a generic geometric point
   is the strict-local field itself. Degree-zero stalk comparison, inverse-image stalk
   compatibility, and the counit germ formula identify the counit stalk map with an
   isomorphism. Conservativity concludes. Zero sheaves and a scheme that is already a
   field spectrum give the zero/identity counits; nonnormal integral schemes still
   have the same generic local field. No curve or cohomology conclusion is hidden in
   this statement, so it is strictly smaller than the original item. Independently
   searched with LeanFinder for direct image along a monomorphism being fully faithful,
   Loogle for `CategoryTheory.Adjunction.counit`, and source grep for counit isomorphisms
   and full faithfulness. The results provide abstract adjunction tools and the existing
   open-immersion counit theorem, not this generic inclusion theorem: a generic inclusion
   need not be open. No duplicate or quick existing proof was found.
4. **Route and pruning — PASS.** The two Ext exactness applications need only H¹(Q)=0
   and H² of the first and third terms. Inverse image preserves cokernels by its existing
   adjunction, without the removed module-coefficient exactness theorem. The normal
   constant and generic-acyclicity inputs remain in use. Compared the old `proof_deps`
   with the new list: the report names all four removed dependencies, including the
   unrestricted stalk lemma that moves to the new geometric node. The unit record has
   empty `realized` entries; no realized node or unit step was bypassed. The reduction
   stays within the original generic-filtration argument. Imports are justified by
   signatures or by the actual proof. One original hole closed and one geometric hole
   added means net zero holes, a decomposition rather than a completed module proof.
5. **DAG agrees — PASS.** Read both sandbox nodes and the repository's old item node.
   Existing node changes are confined to `proof`, `proof_deps`, and `proof_origin`.
   Their steps follow the Lean image sequences, section continuity, normality/constant
   transport, and Ext assembly. The new node's Lean signature matches its theorem;
   source, complete proof steps, dependencies, three searches, creation record, blueprint
   ancestry, chapter, unit, and Lean record are present. Its planned stalk dependencies
   agree with the natural-language proof.

Changes made by the second reader: added this independent review and recorded its
search and axiom evidence. No Lean proof or statement repair was necessary. The existing
item docstring's H²(Q) and torsion discussion describes a stronger original route; the
implemented shorter argument and current DAG correctly require only H¹(Q).
