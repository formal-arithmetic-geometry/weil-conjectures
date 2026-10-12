## What changed

Repaired `Sheaf.Topology.ConstantSubsheafNormalizedCore` after the import-prune
check identified `normalized_labelled_closure` and `normalized_zmultiples_range`
as duplicate declarations of the private arithmetic lemmas in
`Sheaf.Topology.ConstantSubsheafLowerImageStalks`. Removed both top-level
private declarations and inlined their proved subgroup arguments as local
proof terms inside `constantSubsheaf_normalized_completion`. The completion
proof and all public signatures are unchanged. The local terms compile and
are used exactly where the former helpers were used.

## Proved and sorry left

`TopCat.Sheaf.constantSubsheaf_normalized_completion` remains fully proved.
The only remaining sorry in the delivered import closure is the pre-existing
`TopCat.Sheaf.constantSubsheaf_unbounded_normalization` in its own new module;
it is unchanged by this repair. No new sorry was added.

## No longer needed

The duplicate top-level declarations
`normalized_labelled_closure` and `normalized_zmultiples_range` are no longer
needed as declarations; their proofs are local to the completion theorem.
No import or DAG dependency was removed. The existing LowerImageStalks lemmas
are private and therefore cannot be referenced by name across module
boundaries; inlining avoids exporting a second word-for-word declaration while
retaining the complete proof.

## Where the brief, the DAG or earlier work was wrong

The returned delivery's checker correctly detected duplicate statements, but
the existing declarations it named are `private`, so an importing module
cannot use them directly. The repair keeps the arithmetic proof local rather
than adding another public or private declaration with the same statement.
No target statement, definition, or public interface changed.

## New nodes

No new nodes were created by this repair. The delivery continues to contain
`lem-sc-constant-subsheaf-divisor-subfamily-epi` and
`lem-sc-constant-subsheaf-unbounded-normalization`, added in the original
returned delivery and unchanged here.

## Earlier second reading (a previous round; superseded)

Pending the independent second reading. The repaired module compiles and the
static delivery checks pass except for this required report section, now
present for the reader.

## Second reading by P2

1. Compared the delivered `ConstantSubsheafNormalizedCore.lean` declarations with the repository version. Existing public signatures are unchanged byte for byte; the only interface additions are the explicitly imported split-node modules. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`. The completion theorem has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; the sole remaining `sorry` is the named theorem `TopCat.Sheaf.constantSubsheaf_unbounded_normalization`, documented by its node. Verdict: pass.
3. Checked the split statements and nodes. `constantSubsheaf_divisor_subfamily_epi` and `constantSubsheaf_unbounded_normalization` are genuine lower-level reductions, have source/docstring proofs, and are not duplicate library lemmas. Verdict: pass.
4. Read the proof from the target downward. It uses the unbounded normalization, selected-stalk-range, and divisor-subfamily results, and the former duplicate arithmetic declarations are pruned by local proofs. The unit route and required imports remain intact. Verdict: pass.
5. Compared each node's `proof`, `proof_deps`, and `proof_origin` with the Lean proof and verified the two split-node records and the completion node agree. Verdict: pass.

Changed only the report by recording this review; no Lean declaration, node statement, or import was changed during the second reading.
