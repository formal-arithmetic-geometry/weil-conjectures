## What changed

Repaired review point 4 (E2 / H3) by correcting the actual signature in
`lean/Sheaf/Paper/StrictHenselianZariskiEtaleComparison.lean`.
`hi_inclusion` now identifies `i ⋙ Scheme.Etale.forget X` with
`X.restrictFunctor`. The pullback family `fstar` is constrained by all three
clauses of the existing `siteCohomology_pullback` characterization: naturality,
compatibility with connecting morphisms, and the degree-zero adjunction unit.
The new `hc` equality fixes `c q` as `fstar q` on the direct image followed by
cohomology of the adjunction counit. The conclusion remains `∀ q, IsIso (c q)`.
No hypothesis assumes invertibility, and no existence-of-isomorphisms conclusion
replaces the canonical-map claim.

Expanded the theorem docstring with the complete five-step source argument and
an explanation of the defining map conditions. Removed the previous dispute
comment, since its false unrestricted statement has now been corrected. Imports
are unchanged; `Opposite` is opened for the objectwise cohomology maps.

The matching DAG node copy updates `lean.statement` verbatim and records the
repair in `lean.note`. Its mathematical statement, unit route, and proof plan
already specify the canonical map and are unchanged. Added
`coord/changes/strictHenselian_zariski_etale_comparison.md`, with old and new
signatures and a row for every downstream module. Neither direct importer
(`GabberCriterion`, `GabberCriterionDegree`) calls this declaration; no other
module needs adaptation. No target signature or definition changes.

Source checked: [Stacks 09AX](https://stacks.math.columbia.edu/tag/09AX).
The pullback conditions were read verbatim in
`lean/Sheaf/CategoryTheory/SiteCohomologyPullback.lean`. The Leray module was also
read: its present existential-family interface cannot identify the edge map.
This repair corrects the statement without claiming to have filled that proof gap.

## Proved and sorry left

Proved 0 of 1 original sorries; split off 0. The remaining named theorem is
`strictHenselian_zariski_etale_comparison`, node
`lem-weil-pbc-gabber-strict-henselian-zariski-comparison`, with its corrected
signature and complete natural-language proof. No new declaration, new sorry,
hollow definition, or axiom was introduced. The theorem's proof is still exactly
`:= by sorry`.

Local compilation of the corrected module succeeded. Required delivery dry-run
validation is recorded by the final tool output.

## No longer needed

None. This is the requested signature repair, preserving the node's five-step
proof route. No import, module, or DAG proof dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

Review point 4 is repaired in the declaration rather than only in a comment.
The former Lean binders omitted both canonical identifications that the node
already required. For `Spec(k)` with algebraically closed `k` and the constant
integer sheaf, the old arbitrary choice `c q = 0` fails in degree zero. The new
conditions exclude it: degree-zero pullback is the unit, and composition with
the counit is the identity by the adjunction triangle identity. Empty schemes
and zero sheaves are retained; every nonnegative degree is retained.

The previous report's claim that no code repair was possible was incorrect.
The authorized repair permits correcting this intermediate declaration.
The unchanged mathematical node does not need a `statement_change` record;
its `lean.statement` does need the corrected signature and now has it.

The unchanged Leray theorem supplies an unspecified invertible family rather
than invertibility of the characterized edge map. A future proof worker must
repair that dependency's canonical-map interface or prove the identification;
this repair does not use its existential conclusion to infer invertibility of c.
The original theorem remains the single open proof obligation.

## Second reading by V1

1. Compared the delivered Lean module and node with the repository by `diff`.
   The sole existing declaration changes signature deliberately: `hi_inclusion`,
   the additive inverse-image instance, `fstar`, its three characterizing clauses,
   and `hc` are added. Each addition is present verbatim in the change record's
   New section; its Old section matches the old signature. No definition,
   target signature, or public import changed. Searched all of `lean/` for calls:
   only the declaration itself occurs. Read both direct importing modules;
   neither calls it, so there is no missed caller adaptation. Verdict: declared
   correction of an intermediate statement, not a proof-only delivery.

2. Compiled the actual delivered file using `lcompile.py`: exit 0, no warnings.
   Independently compiled a scratch copy with `#print axioms
   strictHenselian_zariski_etale_comparison`: exactly `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The only remaining sorry is the named original
   theorem listed above; no definition, forbidden declaration, or hidden proof
   admission is added. Verdict: well-typed statement repair; 0 of 1 proved.

3. No new declaration, split-off theorem, or node exists. Compared `hfstar`
   clause by clause with `siteCohomology_pullback`: naturality in the sheaf,
   compatibility with Yoneda connecting maps, and the degree-zero unit agree.
   `hc` uses the direct image as the pullback input and then the adjunction
   counit, with the correct source and target. The inclusion equality agrees
   with `zariski_to_etale_is_morphism`. Checked empty schemes, zero sheaves,
   degree zero, and positive degrees mathematically; no case is excluded.
   Over an algebraically closed field the old zero comparison on the integer
   sheaf was a counterexample; the new degree-zero condition and triangle
   identity exclude it. The additive instance is structural, not an IsIso
   premise. Verdict: the repaired statement matches the canonical-map node.

4. Read the five-step node plan and its dependency declarations, and checked
   Stacks 09AX directly (https://stacks.math.columbia.edu/tag/09AX). Read
   `dag/units/sk-thm-p1.json`, including `realized`: this auxiliary node lies
   below the unit realizers; neither the unit nor its route changes. A fresh
   LeanFinder search for canonical counit cohomology comparison after vanishing
   higher direct images found general derived-degree-zero and injective-resolution
   results, not this theorem. A broader `rg` search of the library and Mathlib
   sites found no ready general comparison. The upstream strictly henselian
   local-scheme vanishing is only the local ingredient, not this global theorem.
   The existing Leray interface supplies an unspecified invertible family and
   cannot identify `c`; other dependencies also require Ext/derived-cohomology
   bridges. There is no small proof repair to close here. Imports still carry
   the retained mathematical plan; all proof-only imports are plain `import`.
   Verdict: no pruning or split-off progress claimed; No longer needed is none.

5. Verified programmatically that `lean.statement` is byte for byte the Lean
   signature and the change record's New signature. The node's mathematical
   statement, proof, proof_deps, proof_origin, chapter and unit are unchanged,
   as appropriate for the still-open original proof and the retained source
   route. No new-node fields need checking. Verdict: DAG agrees with the
   repaired statement and honestly records the open proof.

Second reading changed only this report, adding the independent review and
verification evidence. The Lean repair and change record required no further
correction. Scratch axiom checks are outside the delivered lean/ tree.
