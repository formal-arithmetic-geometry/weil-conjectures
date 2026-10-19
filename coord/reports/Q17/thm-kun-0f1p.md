## Files written

- `dag/nodes/sec-smooth-purity/thm-kun-0f1p.json`: the item, split into its two imported proof paragraphs; no new DAG nodes and no Mathlib leaves.
- `dag/units/sk-prop-sf-kunneth-ordinary.json`: realized the unit's statement by `thm-kun-0f1p`; the unit has no separately enumerated steps.
- `citations.json`: verbatim statement quotations for every node used by every proof step.
- `report.md`: this report.

No Lean files were written and no compiler, Lake, or build tool was run.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for `thm-kun-0f1p`, `nonempty_iso_kunneth`, Künneth terminology, and the relevant blueprint tag. The declaration `AlgebraicGeometry.Etale.nonempty_iso_kunneth` in `WeilConjectures/SixFunctors/Etale/Derived/Finiteness/Kunneth.lean` is still proved with `sorry` and has a more general `Finite Λ`/`Nonempty` formulation, so it is not a finished exact attachment. The upstream master checkout is reference material only and likewise has no sorry-free declaration closing this item.

## WANTED:

WANTED: `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/thm-kun-0f1p.md`, the blueprint proof source for `thm-kun-0f1p`. That markdown file and the Stacks checkout are absent from the shared repository. I read the corresponding Stacks source in the read-only launcher literature mirror, `stacks-project/etale-cohomology.tex`, Lemma `lemma-kunneth` (Tag 0F1P), lines 20937–20974; the imported node preserves its two proof paragraphs.

## Problems found and corrected

The imported two-step route is mathematically aligned with the cited source: Tag 0F1P first applies the unbounded base-change result (Tag 0F1N) to the product diagram, then uses Leray and the finite-cohomological-dimension pull-out lemma (Tag 0F12). I retained that route and did not move the item's conclusion into a child node. The existing `uses_not_cited` entry for `def-kun-separably-closed` is a statement dependency rather than a proof input, so no proof step cites it. No statement dispute or source error was found.

## Review by Q17

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md`, `coord/dag-sync.md`, `GOAL.md`, and all of `coord/delivery-errors.md` sections B–E before editing. I read the `sec-smooth-purity` chapter record and the `sk-prop-sf-kunneth-ordinary` unit record, then read the complete item JSON and its imported proof. I searched the whole DAG and blueprint with `tools/blueprint_refs.py search` for Künneth and Tag 0F1P; no alternate blueprint node stated this item.

For step 1 I read the full statement of `lem-kun-0f1n`. It explicitly assumes a field, an invertible integer, finite-type schemes, and says that the canonical map used in the displayed product diagram is an isomorphism for arbitrary derived objects. Those are exactly the hypotheses used in the item's specialization. For step 2 I read each cited statement: `lem-kun-kunneth-via-0f1n` identifies the Künneth map with the composite being used; `lem-kun-leray-unbdd` gives the canonical global-sections/Leray identification for qcqs maps of finite cohomological dimension; `lem-kun-0f10` supplies finite cohomological dimension for the projection and for finite-type schemes over a separably closed field; `lem-kun-0f12` gives the tensor/pull-out isomorphism; `lem-kun-cd-sep-closed-point` gives cohomological dimension zero for the separably closed base point; and `def-kun-kunneth-map` defines the map whose invertibility is concluded. The exact sentence or formula each step takes from these statements is recorded in `citations.json`, and every quote was checked against the node file.

I also read `def-kun-separably-closed` to verify that the item's use of “separably closed field” has an existing definition node, and read `def-kun-kunneth-map` in full to check that the product-square map has the displayed source and target. I checked the finite-type and invertibility hypotheses in the product diagram and checked that no unstated properness assumption enters. The only readable Lean declaration is sorry-backed, so I left the item as a split rather than claiming an attachment. The unit realization records this theorem as its statement node; there are no unit proof-step slots to fill.

## What could not be finished

Nothing remains for this one-level split. The second worker should independently reread the two proof steps and the cited node statements, then deliver the dry-run-accepted sandbox.


## Second reading by Q17

- Item statement: checked every hypothesis, coefficient category, product projection and conclusion against Stacks Tag 0F1P, `etale-cohomology.tex`, `lemma-kunneth`, lines 20937–20974, and the complete blueprint markdown in the read-only launcher literature mirror; PASS. No statement dispute. For a zero complex or an empty factor both sides vanish; for X = Y = Spec(k) this is tensoring complexes over Z/n; n = 1 gives zero module categories, and n = 0 is excluded. No boundedness or properness assumption is introduced.
- Step 1: checked the full statements of `lem-kun-0f1n` (Stacks 0F1N, `lemma-punctual-base-change-upgrade-unbounded`, lines 20878–20900), `lem-kun-kunneth-via-0f1n`, and `def-weil-finite-type-morphism`; FIX then PASS. The substitution now names all six maps, both cartesian squares, and the finite-type product charts. The compatibility statement specifies the canonical product-square map, so its constant-complex identification is cited rather than assumed. The lower right arrow is b:Y→Spec(k), not an identity. The compatibility node repeats the same diagram typo; its textual product-square specialization and canonical-map assertion are used, not that label. This pre-existing node is outside the sandbox edit scope and should have its identity label corrected separately.
- Step 2: checked the full statements of `lem-kun-leray-unbdd`, `lem-kun-0f10`, `lem-kun-0f12`, `lem-kun-kunneth-via-0f1n`, `def-kun-kunneth-map`, `lem-weil-pbc-finite-type-algebra-noetherian`, and `lem-sc-affine-noetherian-underlying-space`; FIX then PASS. Compared the source route with Stacks 0F10 (`lemma-finite-cd`, lines 20040–20050) and 0F12 (`lemma-pull-out-constant-mod-n`, lines 20163–20177). Finite affine covers plus the two existing Mathlib leaves give Noetherian charts; the finite-union argument gives quasi-compact opens, and the affine relative-diagonal calculation gives the projection's quasi-separatedness. The projection is explicitly a k-morphism, as the repaired 0F10 statement requires. Z/n is a torsion ring, the global-sections complex is arbitrary, and 0F10(2) already gives the absolute bound over separably closed k. The canonical-map compatibility node states exactly the composite used; functoriality and composition preserve its inverses.
- New nodes: none; no duplicate, elementary child, restatement, or new Mathlib-leaf claim requires a search. All three additional dependencies (`def-weil-finite-type-morphism`, `lem-weil-pbc-finite-type-algebra-noetherian`, `lem-sc-affine-noetherian-underlying-space`) already exist as Mathlib leaves, so they introduce no unit-route exception. The two original proof paragraphs are retained.
- Source availability and attachment: the previously WANTED blueprint markdown is present in `/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/thm-kun-0f1p.md`; read it completely. Independently inspected slopmaster2 `Kunneth.lean`, lines 72–84: `AlgebraicGeometry.Etale.nonempty_iso_kunneth` has a sorry body and asserts existence of an isomorphism rather than invertibility of this canonical map, so it does not close the item. Blueprint search for 0F1P finds only this theorem and its compact-support corollary, which has a different conclusion.

Changes and reasons:

1. Corrected the erroneous identity label on Y→Spec(k); named the structure maps and the precise 0F1N substitution.
2. Expanded the finite-type product and qcqs checks, citing the existing Hilbert-basis and affine-Noetherian-space Mathlib leaves instead of silently using geometric hypotheses.
3. Specified the torsion coefficient ring, the direction of the canonical tensor map, and the inverses proving that the displayed composite is an isomorphism; removed the redundant point-dimension citation already incorporated in 0F10(2).
4. Refreshed every citation against the current node statements, including the updated canonical Kunneth-map definition. Quotes are verbatim; each proof use has one quote.
5. Removed the proposed unit realization: the unit also states proper-factor, compact-support and projection-formula clauses, which this theorem alone does not realize. Its fixed statement and route are untouched. Removed the stray empty temporary unit file from the sandbox. The earlier sections above are retained as the first reader's record.

Only sandbox DAG/report/citation files were edited. No Lean, compiler, Lake, build, live project edit, or manual git command was used.
