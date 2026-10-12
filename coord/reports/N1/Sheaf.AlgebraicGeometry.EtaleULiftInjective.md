## What changed

The unchanged theorem `AlgebraicGeometry.Scheme.etale_ulift_injective` now applies a small-valued injectivity criterion and supplies its hypothesis using a proved universe-descent theorem. Added proof imports of `Sheaf.AlgebraicGeometry.EtaleSmallInjectiveCriterion` and `Sheaf.AlgebraicGeometry.EtaleULiftInjectiveExtension`.

The extension theorem is fully proved. Its private helpers transport each small abelian group onto its shrink, descend a presheaf through ULift's essential image, and reflect the sheaf condition through full faithfulness. Given a mono A → B with small-valued B, A is small-valued too. Both sheaves and the extension problem descend; injectivity in the smaller universe supplies an extension, which is lifted and conjugated back. The construction uses proven essential-image witnesses, with no data depending on an unproved theorem.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.Scheme.etale_ulift_injective` (node `lem-sc-etale-ulift-injective`). Also proved `AlgebraicGeometry.Scheme.etale_ulift_injective_extension` (node `lem-sc-etale-ulift-injective-extension`) and both private helpers, `small_group_in_image` and `small_sheaf_in_image`.

One new hole remains: `AlgebraicGeometry.Scheme.etale_injective_of_small_extensions` (node `lem-sc-etale-small-injective-criterion`). This is the generic small-generator injectivity criterion, for an arbitrary large-coefficient sheaf T, with no assumption that T is lifted or that a small-coefficient injective exists. It is strictly the generator/test-object part of the argument. This delivery is a decomposition (one upper hole closed, one lower hole added), with the universe descent part proved. All three modules compile together without warnings. The original module has no sorry.

## No longer needed

None. No original imports were removed and no previously stated proof node is bypassed. The original node's two definitional dependencies remain needed below the two new nodes. Its affine-site and small-generator argument remains in the criterion; its universe-descent argument is now proved in Lean.

## Where the brief, the DAG or earlier work was wrong

The original proof dependencies named only the site and injectivity definitions, not the substantive small-generator criterion or universe descent. The two new nodes make those steps explicit. No target signature or existing statement was changed. The unit `sk-prop-h2` has no realized statement or step assigned to this auxiliary node, and its route remains unchanged.

Edge cases: empty scheme and zero sheaf cause no failure; the descent proof applies to any objectwise small groups, including zero groups. Monicity, rather than an epi or an arbitrary map, is essential to descend A from small-valued B. No smallness assumption is placed on A separately.

## New nodes

`lem-sc-etale-small-injective-criterion`, in `Sheaf.AlgebraicGeometry.EtaleSmallInjectiveCriterion`, is the remaining Stacks 01DO test-object criterion. Its docstring describes affine-site replacement, small free representable sheaves, extension back to the full site, and the generating-family/Zorn argument.

`lem-sc-etale-ulift-injective-extension`, in `Sheaf.AlgebraicGeometry.EtaleULiftInjectiveExtension`, is the proved extension property restricted to objectwise small codomains. Its DAG proof follows the implemented shrink, essential-image, full-faithfulness, and Injective.factors argument.

## Second reading by N1

1. I compared the delivered target module with the repository version. The theorem
   signature is byte-for-byte unchanged; only proof imports and the proof body differ.
   The two auxiliary modules are new declarations recorded by matching DAG nodes.
2. I compiled all three sandbox modules with `lcompile.py --all`; they compile without
   errors or warnings. The only remaining `sorry` is the explicitly named
   `etale_injective_of_small_extensions`; there are no `sorry`s in definitions, and
   the extension and target proofs use ordinary category-theoretic constructions.
3. The split criterion is the generator-extension criterion of Stacks Tag 01DO and is
   strictly more general than the lifted-extension theorem. The extension theorem's
   hypotheses and conclusion match its node exactly. No duplicate declaration was
   found in the repository search.
4. The target proof follows the stated route: the small-valued criterion is applied,
   then the universe-descent extension theorem supplies its hypothesis. The unit route
   is not bypassed. The criterion remains the sole intentional open lower statement.
5. The target node's proof and proof dependencies name precisely the two auxiliary
   declarations used by the Lean proof; the auxiliary nodes record their declarations,
   sources, and split status consistently. No imports or nodes can be pruned safely.

I changed only this report, adding the second-reading record. No Lean source, theorem
statement, definition, or DAG node was changed during review.
