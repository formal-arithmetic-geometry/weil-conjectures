## What changed

Proved the unchanged theorem
`AlgebraicGeometry.Scheme.depth_one_affine_finite_quotient_of_depth_two`
from two narrower geometric lemmas and the existing
`IsLocalRing.depth_in_short_exact`. Added proof-only imports for those modules,
localization exactness and localization finiteness. The original public imports,
existing declaration signature and docstring are unchanged. No existing interface
or definition changed, and no other group's module was adapted.

The target proof constructs the finiteness instance for the localized quotient
from `S.FG`. It localizes the actual maps `K.subtype` and `K.mkQ`, obtaining their
injectivity, exactness and surjectivity directly from Mathlib. It applies the
quotient inequality in the nonzero case. For zero kernel the localized quotient
map is bijective, and the proof transports depth through its linear equivalence.
For zero quotient it unfolds the definition to obtain infinite depth. These are
proved private helpers, not new holes. The two new modules contain one public
statement each, with whole proofs `by sorry`.

Read the source proofs at Stacks Tags
[0AV8](https://stacks.math.columbia.edu/tag/0AV8),
[0AVN](https://stacks.math.columbia.edu/tag/0AVN) and
[0E9I](https://stacks.math.columbia.edu/tag/0E9I).
The boundary lemma follows the finite-basic-open argument of 0AVN directly,
so it does not assume the Hartogs conclusion or vanishing of the quotient.
The source comparison follows the interior stalk isomorphism in 0E9I and the
affine quasi-coherent stalk dictionary. Reviewed the existing affine tensor-stalk
presentation and affine ring-stalk localization statements. The source comparison
uses the tensor-stalk presentation as a general tool from another unit; it does
not replace any step of the spreading unit. The spreading unit's `realized`
entries are empty; no chapter, unit, or target statement is edited.

Local compilation of all three sandbox modules succeeds, with no warnings.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.depth_one_affine_finite_quotient_of_depth_two`
(node `lem-sbc-depth-two-affine-finite-quotient-depth`). No `sorry` remains in the
item's module.

Added two holes, so this delivery is a decomposition, not an unconditional proof
or a reduction in the total number of holes:

- `AlgebraicGeometry.Scheme.depth_one_affine_boundary_submodule`
  (`lem-sbc-affine-restriction-boundary-submodule-depth`). It only concerns the
  intermediate module `S_p` at a boundary point, assumes no depth condition on N,
  and does not mention the restriction source or its quotient.
- `AlgebraicGeometry.Scheme.affine_restriction_source_depth_comparison`
  (`lem-sbc-affine-restriction-source-depth`). It identifies the source's localized
  depth and the zero quotient inside U; it gives no quotient depth at the boundary.

The combination is substantive: the localized exact sequence and the depth lemma,
including all degenerate cases and instance witnesses, are proved in the target.
Neither new theorem has the target's hypotheses and conclusion repackaged.

Existing imported theorems and their transitive proof obligations remain work for
other items; no unproved dependency is treated as an obstacle or counted as closed.

## No longer needed

None globally. No existing imports were removed. The original direct DAG
dependencies for quasi-coherent pushforward, associated-prime submodules and
maximal-not-associated regular elements move below the new geometric lemmas;
they are still needed there and are not claimed as pruned. The depth-in-SES node
remains a direct dependency of the target. No blueprint unit or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted a usable Lean interface for the affine source
comparison, the interior zero quotient, and the boundary associated-point
exclusion. Its four stated dependencies give ingredients but do not themselves
state those geometric conclusions. The new nodes isolate these gaps. The original
module also had no proof imports for its recorded dependencies; the completed
proof now explicitly imports exactly the interfaces it uses.

LeanSearch returned HTTP 500 for both searches, recorded as unavailable rather
than as absence of a match. LeanFinder, Loogle and source grep returned related
localization and module results, but no exact geometric statements. Searches were
run with msearch.py and are recorded in searches.jsonl. Searched the library, DAG
and whole imported blueprint for depth/restriction, associated and stalk/tensor
results before creating the new nodes. Existing tensor-stalk comparison is used
in the new source node's plan; it is not duplicated.

Edge cases: with empty U the direct-image section module and S are zero, so the
boundary depth is infinite. With U all of L the source comparison gives the zero
quotient everywhere and the boundary lemma has no applicable point. With N zero,
P, S and K are zero. More generally S_p zero forces Q_p zero; K_p zero leaves
Q_p isomorphic to S_p. None of the statements excludes these cases.

## New nodes

`lem-sbc-affine-restriction-boundary-submodule-depth`, module
`Sheaf.AlgebraicGeometry.Morphisms.DepthTwoAffineBoundarySubmoduleDepth`, isolates
positive depth of a finite submodule of direct-image sections outside U. Its
proof uses a finite basic-open cover, localized injectivity, and the existing
maximal-not-associated theorem. It does not use the depth-two source assumption.

`lem-sbc-affine-restriction-source-depth`, module
`Sheaf.AlgebraicGeometry.Morphisms.DepthTwoAffineRestrictionSourceDepth`, isolates
the affine source stalk comparison and the interior zero quotient. Injectivity
identifies K with the original source module; the germ scalar actions provide
the precise localization comparison. It does not use the boundary submodule
lemma or the depth inequality for short exact sequences.

Updated only `proof`, `proof_deps` and `proof_origin` of the existing item's node.
No change record is needed: there is no existing statement, definition or public
import change. Both new nodes inherit the item's chapter, unit and blueprint
ancestor, and each remaining hole has its source and proof in its docstring.

## Second reading by H2

1. **Visible changes.** Compared the delivered target module with the repository version. The
existing theorem statement, definitions, and docstrings are byte-for-byte unchanged; only
proof-only imports, private helpers, and the proof body were added. The two new public
modules and node files are declared in the report and are the only added interfaces.
Verdict: pass.

2. **Proof and axioms.** Compiled all three sandbox modules with `lcompile.py --all`.
The target theorem has no `sorry`; the only remaining `sorry`s are the two named split-off
theorems listed above, each with a source, proof docstring, and matching node. No forbidden
constructs occur. The target proof uses only ordinary Lean and imported declarations;
its helper proofs are private. Verdict: pass, with the two documented split-off holes.

3. **Statements and duplication.** Checked both split-off statements against the target:
the boundary statement concerns only the localized finite submodule at points outside U,
and the source-comparison statement gives source finiteness, the interior zero quotient,
and the boundary source depth. Neither restates the target, weakens or strengthens an
existing declaration, or duplicates an existing library theorem. Edge cases (empty U,
zero modules, and zero localized submodules) are included. Verdict: pass.

4. **Route and pruning.** The target follows the recorded route through the localized short
exact sequence and `IsLocalRing.depth_in_short_exact`; the two geometric gaps are isolated
in the new nodes. The spreading unit's realized entries remain empty. No old import is
unused according to the proof, so no global pruning is claimed. Verdict: pass.

5. **DAG agreement.** The target node's `proof`, `proof_deps`, and `proof_origin` match the
Lean proof, and both new nodes contain the required statements, sources, proof plans,
Lean records, chapter/unit/blueprint metadata, and split status. Verdict: pass.

Changed after reading: appended this review only; no code or node changes were needed.
