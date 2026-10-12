## What changed

Proved `AlgebraicGeometry.Scheme.exists_finiteEtale_henselian_gRing_stage` with its
original signature and public imports unchanged. The proof applies the existing
pair-henselization, finite-type integer G-ring, henselization G-ring, and universal-property
declarations. It constructs the proper base change, the two compatible maps, the
closed-fibre isomorphism, and the transported finite étale cover explicitly in Lean.
The private helper `closedFibre_baseChange_iso` is proved from Mathlib pullback pasting
and base change of an isomorphism; it contains no `sorry`.

Added `Sheaf.AlgebraicGeometry.FiniteEtaleFiniteTypeClosedFibreStage` for the original
plan's steps 1–4. This is a strict subargument: it works for any commutative ring and
ideal, and produces a finite-type integer ring and a descended closed-fibre cover;
it supplies neither a henselian pair nor a G-ring nor the final henselian stage.
The original theorem then performs the henselization and all geometric transport.
Both projection identities for the intermediate closed-fibre map are recorded,
including the second identity needed to check the final square.

Both modules compile locally without errors or warnings. The DAG records the actual
route and the finite-type subargument's complete source proof and dependencies.

## Proved and sorry left

Proved the item's sole original `sorry`:
`AlgebraicGeometry.Scheme.exists_finiteEtale_henselian_gRing_stage`
(node `lem-weil-pbc-finite-etale-henselian-g-ring-stage`).
No `sorry` remains in the item's module.

The only added `sorry` is
`AlgebraicGeometry.Scheme.exists_finiteEtale_finiteType_closedFibre_stage`
(node `lem-weil-pbc-finite-etale-finite-type-closed-fibre-stage`). Its proof is exactly
`:= by sorry`, with the complete approximation, quotient-limit, closed-fibre-limit,
and finite étale descent argument in its docstring and node.
Existing imported theorems may themselves depend on named `sorry` declarations;
this delivery uses them as the stage-3 brief requires.

Edge cases checked mathematically: `I = ⊤` has empty closed fibre and empty covers;
`I = ⊥` uses the inverse-image ideal `ker α` and does not assume α injective;
the zero ring and empty proper scheme require no nontriviality or nonemptiness;
properness is not strengthened to finite presentation. For a finite-type base the
identity stage gives the intermediate statement. Quotient compatibility follows
from the quotient maps, and does not assume the original ring maps are injective.

## No longer needed

No node or module is pruned from the overall mathematical route. The following
proof imports were removed from the parent and are now retained as proof imports
of the open finite-type subargument:

- `Sheaf.AlgebraicGeometry.DescendFinite`
- `Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent`
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`
- `Sheaf.AlgebraicGeometry.ProperLimitNoetherian`
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`

The parent's explicit `Sheaf.RingTheory.PairHenselization` import is redundant:
`HenselizationPairGRing` and `HenselizationUniversalProperty` publicly import it.
Its theorem is still used, and its node remains a direct proof dependency.
The trial import `Mathlib.CategoryTheory.Comma.Over.Pullback` is also unnecessary.
All original public imports remain unchanged.

Every old parent dependency removed from its direct `proof_deps` is listed below.
Each remains a dependency of the new finite-type node, so none is globally pruned:

- `def-sbc-locally-finite-presentation`
- `def-weil-etale-morphism`
- `def-weil-finite-integral-morphism`
- `def-weil-proper-morphism`
- `lem-weil-pbc-affine-morphism-permanence`
- `lem-weil-pbc-closed-immersion-base-change`
- `lem-weil-pbc-descend-etale`
- `lem-weil-pbc-descend-finite`
- `lem-weil-pbc-filtered-colimit-algebras-elementwise`
- `lem-weil-pbc-limit-affine-transition`
- `lem-weil-pbc-proper-limit-noetherian`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `lem-weil-pbc-spec-colimit-limit`
- `pqf-def-affine-morphism`
- `thm-pd-spreading-out`

## Where the brief, the DAG or earlier work was wrong

The `thm-pd-spreading-out` Lean record lists
`Scheme.exists_pullback_hom_of_isLimit` (morphism descent) but the object descent
in step 4 uses `Scheme.exists_isPullback_of_finitePresentation`, in the same existing
module `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit` at line 3164.
That module's own documentation identifies this as Tag 01ZM part (1). The new node
explicitly names the correct clause, so a later worker need not rediscover it.
No statement or definition is changed and no unit route is bypassed.

The local `literature/stacks-project/pione.tex` checkout is absent. The official
Stacks Tag 0GS2 text was read online, particularly the General case. WANTED:
`literature/stacks-project/pione.tex`, Tag 0GS2, and `limits.tex`, Tags 0A0P, 01ZM,
01ZO, 07RP, for the next worker on the finite-type node. No files were downloaded.
The proof-origin records mark the expanded argument as agent-written.

Mathlib searches ran through the required launcher script and are in `searches.jsonl`:
LeanSearch was unavailable (HTTP Internal Server Error); LeanFinder found affine
ring-algebra descent (`Algebra.Etale.exists_subalgebra_fg`) and unrelated permanence
results; its signature was read and does not give proper-scheme/closed-fibre descent.
Loogle and grep found the pullback tools used in the completed geometric argument.
DAG, library, and whole-blueprint searches found no duplicate finite-type compatible
closed-fibre stage theorem.

## New nodes

`lem-weil-pbc-finite-etale-finite-type-closed-fibre-stage`, in
`dag/nodes/sec-proper-base-change/`, states the finite-type descent subargument in
`lean/Sheaf/AlgebraicGeometry/FiniteEtaleFiniteTypeClosedFibreStage.lean`.
Its original approximation/descent dependencies are retained, its projection
identities are explicit, and its proof follows the first four steps of the parent.
No change record is needed because existing signatures and public imports are unchanged.

## Second reading by E2

1. **Visible interface: pass.** Compared the complete parent module with the
   repository using `diff`. The existing theorem signature is byte for byte
   unchanged, as are its docstring and public imports. No definition or target
   changes; no change record is required. The private helper is a proved theorem.
2. **Proof and axioms: pass.** Both modules compile locally without errors or
   warnings. Read the pullback construction, quotient-map compatibility, both
   projection identities, and final isomorphism in `Over`. A scratch-copy
   `#print axioms` check gives only `propext`, `Classical.choice`, `Quot.sound` for
   the private helper; the two public theorems additionally use `sorryAx`, as
   expected from the named open finite-type theorem and existing open inputs.
   There are no definitions with sorry and no forbidden declarations or attributes.
3. **Split statement: pass.** Read the new statement, docstring, and complete
   node proof against [Stacks Tag 0GS2](https://stacks.math.columbia.edu/tag/0GS2)
   (General case) and [Tag 0A0P](https://stacks.math.columbia.edu/tag/0A0P).
   The statement is the approximation/descent portion alone: it has no henselian
   input or G-ring output. The parent actually constructs the henselization,
   extension map, proper base change, and cover transport. Checked the zero ring,
   empty schemes/covers, top and zero ideals, noninjective ring maps, and a
   finite-type base (identity stage). No extra nontriviality or finite-presentation
   assumption is needed. Independent LeanFinder search for a cover defined over
   a finitely generated subring found affine algebra descent only; Loogle with
   `"IsProper", "FiniteType"` found properness consequences, not this theorem.
   Library searches with closed-fibre descent and finite-type-stage variants
   found no duplicate. The remaining subargument requires the full limit and
   descent construction and cannot be closed by a short application found here.
4. **Route and pruning: pass after repair.** Read the existing approximation,
   finite/etale descent, henselization, and upstream object-descent signatures.
   The finite-type theorem follows the original first four DAG steps; the parent
   proves the remaining geometric argument. No shorter valid route was found.
   Read `dag/units/sk-thm-p1.json`: no realized statement or step is bypassed or
   changed. The report now explicitly lists every removed direct dependency and
   import. They are moved below the new node, not globally pruned.
5. **Nodes: pass.** Both nodes' `proof_deps` equal the union of step `uses`.
   The parent node describes the Lean construction, and the new node's statement
   and Lean record match its declaration. Checked its source, origin, searches,
   creation, blueprint ancestry, chapter and unit. Existing node fields outside
   stage-3 ownership are unchanged.

Changed in this reading: restored the five approximation/descent proof imports
in the open finite-type module. Without them, those remaining obligations would
leave the import-based target closure despite still appearing in the DAG plan.
Expanded `## No longer needed` to list all moved direct dependencies and removed
imports explicitly. No theorem statement or proof body was changed.
