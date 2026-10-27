## What changed

Repaired the return of delivery 28ec3cb6397 against current sheaf-dag. Kept H4's
landed `Sheaf.Paper.CommonProjectionTensorCompatibility` and its node unchanged;
neither file is included in this delivery. Introduced the separately named module
`Sheaf.Paper.CommonProjectionProperTensorCompatibility` and declaration
`WeilConjectures.commonProjectionProperTensorCompatibility`. It supplies one tensor
comparison with the compact-support square for every morphism and the proper counit
projection square for proper morphisms, for that same comparison.

`CommonProjectionProperOnStage` now imports the new module privately, obtains
`⟨t, hp, hq⟩` from the new theorem, and specializes hp to proper morphisms. Its complete
private transport calculation preserves properIdentification, moves the tensor and
target comparisons by naturality, applies inclusion to `hH.proper`, and cancels the
invertible source comparison. Its public theorem statement and public imports are
unchanged from current main. The item's node records the revised proof route.

The new statement has its own module, node, statement dependencies, source and full
proof in words. Its statement dependencies include H4's node because it explicitly
identifies the compact-support conjunct as that node's assertion. Its proof does not
assume that an arbitrary witness of H4's existence theorem satisfies the proper square:
it constructs a common tensor comparison and verifies both squares by adjunction
transposition. It defines no data by choosing an unproved existence witness.

Validation is through lcompile.py for the sandbox in import order and deliver3.py's
compilation, axiom probes and preflight. No other existing module is edited.

## Proved and sorry left

Closed one original hole: `WeilConjectures.commonProjectionProper_onStage`
(`lem-sf-common-projection-proper-on-stage`). The item module has zero holes.

Added one hole, the entire public theorem proof of
`WeilConjectures.commonProjectionProperTensorCompatibility`
(`lem-sf-common-projection-proper-tensor-compatibility`). This is an individual-map
comparison assertion without the finite-stage coherence hypothesis or the proper
coherence conclusion. The item's naturality, application of the finite-stage equation
and cancellation are proved in Lean. This is a decomposition: one original hole
closed, one distinct lower hole added, and no net hole reduction claimed.

H4's `WeilConjectures.commonProjectionTensorCompatibility` remains unchanged on main;
its existing hole is not introduced or moved by this packet. No private theorem or
definition contains sorry.

## No longer needed

The rejected J2 versions of `CommonProjectionTensorCompatibility.lean` and
`lem-sf-common-projection-tensor-compatibility.json` have been removed from the sandbox
packet. This does not delete or withdraw H4's landed files. The item's former private
import of `Sheaf.Paper.CommonProjectionTensorCompatibility` is replaced by the private
import of `Sheaf.Paper.CommonProjectionProperTensorCompatibility`.

No module or node is globally pruned. Direct uses of the coefficient, canonical tensor
and pullback constructions remain isolated in the new individual-map lemma. The item
uses only `hH.proper`, operation comparison squares, tensor naturality and the two
individual-map squares. It uses no composition or pentagon coherence, duality,
faithfulness of inclusion, or invertibility of the projection maps.

## Where the brief, the DAG or earlier work was wrong

The returned delivery collided with H4's independently landed statement under the same
node and theorem names. H4's theorem asserts compact-support compatibility for all f;
the rejected J2 theorem additionally asserted proper-projection compatibility for the
same tensor comparison, but only compact-support compatibility for proper f. Those
statements cannot be merged under one existing name. The proper square cannot be
inferred from H4's square using the proper coherence equation without assuming what
this item must prove.

The repair follows the return precisely: H4's files stay unchanged, the stronger
all-f compact-support plus proper-f proper-projection statement receives distinct names,
and the item uses its two conjuncts with one t. The new node explicitly cites H4's
node in stmt_deps. No existing statement, definition or interface is changed, so no
change record or consumer adaptation is needed.

The new theorem's edge cases use only the same adjunction and normalization equations:
zero inputs, empty schemes, identity opens and identity coefficient extensions require
no additional hypotheses. The compact-support square allows arbitrary f because its
compactification has a proper factor. The proper square explicitly retains properness.
The unit sk-rem-sf-pf-done has no separately realized statement or proof steps; its
route is preserved.

## New nodes

`lem-sf-common-projection-proper-tensor-compatibility`, realized by
`Sheaf.Paper.CommonProjectionProperTensorCompatibility`, states the two individual-map
comparison squares through one tensor comparison, with compact-support compatibility
for all f and proper counit compatibility for proper f. Source: the Compatibility and
common finite coefficient-field paragraphs of the latest thm-sf-pf-field proof. The
retained searches found generic adjunction transport and the rational analogue; the
current-main search finds H4's compact-support-only theorem but no theorem recording
both squares for the same comparison. The new node carries these searches and the
representative-normalization and transpose proof in words.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
