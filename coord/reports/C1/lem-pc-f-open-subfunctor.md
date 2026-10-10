Files written:

- `dag/nodes/sec-picard-framework/lem-pc-f-open-subfunctor.json`: item split into two proof steps; no new nodes.
- `dag/units/sk-lem-picard-f-open.json`: realized statement and proof step recorded.
- `citations.json`: verbatim statement excerpts for every cited dependency.

Attachments:

- `AlgebraicGeometry.isOpenImmersion_picardFunctorInvertibleDirectImage_ι` is present in slopmaster2 but is not attachable: its transitive audit contains sorry declarations.

WANTED:

- None.

What was wrong or incomplete in the imported item:

- The imported node was otherwise mathematically aligned with Stacks Tag 0B9V, but it had `status: imported` and no split metadata. Its `blueprint.same_as` was null; this is now the empty search result. The Lean theorem's direct body is short, but the audit explicitly shows transitive sorry dependencies, so it cannot be treated as closed.

## Review by C1

I read the item source as Stacks Project Tag 0B9V (the Picard Schemes of Curves Lemma 44.6.2 entry in `literature/stacks-tags-cited.tsv`) and read the corresponding declarations and docstrings in `WeilConjectures/AlgebraicGeometry/Picard/Representability.lean`, lines 109--220. Step 1 uses the existing statement of `lem-pc-rf-base-change-flat-module` for the derived base-change isomorphism and `lem-pc-smooth-flat` for flatness and local finite presentation; the remaining assertions that a base change of a proper finite-presentation morphism remains such and that pullback preserves an invertible module are direct base-change and definition checks. Step 2 uses `def-pc-subfunctor` for the meaning of subfunctor, `lem-pc-flat-rf-open` for the open locus with rank one in degree zero, and `def-sc-invertible-module` for identifying finite locally free rank one with invertible. I opened every cited node and copied the quoted portions into `citations.json`; each quote states exactly the fact used. The hypotheses on `f_T` and `\mathcal L` are checked in the Lean docstring and in the item proof. I searched the whole DAG and blueprint for duplicate open-subfunctor or Tag 0B9V statements and found only this item. No new node was needed, and the unit realization records that the item supplies its sole sketch step.

What could not be finished:

- The required dry run is performed by the dispatcher after this sandbox is handed to the second reader; no Lean source was changed or built in this stage.

## Second reading by C1

- Step 1: checked against Stacks Tag 0B9V and the statements of `lem-pc-rf-base-change-flat-module` and `lem-pc-smooth-flat`; base change, proper finite presentation, flatness, and pullback of an invertible module give the claimed subfunctor closure. Verdict: correct, with the cited statements supplying the non-elementary facts.
- Step 2: checked against Stacks Tag 0B9V and the statements of `def-pc-subfunctor`, `lem-pc-flat-rf-open`, and `def-sc-invertible-module`; the rank-one degree-zero open locus is exactly the required representability condition. Verdict: correct.
- New nodes: none; all dependencies are existing nodes, so B1--B7 and duplicate checks are vacuous for new nodes.
- Edge cases: the zero module is excluded by rank one, a field base reduces to the stated fibre condition, and the empty scheme/base gives the vacuous open locus; no hypothesis is lost for ranks 0 or 1.

Changes made: added this second-reading record only. The split, citations, statements, and proof steps required no mathematical repair. Dry run `deliver.py C1 lem-pc-f-open-subfunctor --no-push` passed (preflight and DAG checks).
