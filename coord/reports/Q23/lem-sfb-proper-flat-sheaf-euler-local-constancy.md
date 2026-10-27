# Worker report: lem-sfb-proper-flat-sheaf-euler-local-constancy

Group Q23; stage 1; 2026-10-22. Direct delivery with self-review, as authorized by the brief.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-proper-flat-sheaf-euler-local-constancy.json`: statement, split; no Mathlib match. Four proof steps use existing nodes, with the numerical calculation written out.
- `citations.json`: one entry for every node in every proof step's `uses`, quoting its actual statement verbatim.
- `report.md`: this report. `searches.jsonl` is the unmodified log written by msearch.py.

New nodes: 0. New Mathlib leaves: 0. No Lean files, compiler calls, repository writes or manual git commands.

## Attachments

None. The earlier attachment proposal was rejected because local constancy depends on an unclosed local-model proof. I read `AlgebraicGeometry.Scheme.Modules.isLocallyConstant_eulerCharFiber` in `WeilConjectures/AlgebraicGeometry/Cohomology/DirectImage/BaseChange.lean:112` and its use of `exists_isFiniteFreeComplex_higherDirectImage`, and the latter's statement and proof in `DirectImage/FiniteFreeComplex.lean:204`. The existence statement already has the DAG node `lem-pc-universal-finite-free-complex`; the split cites that node as a prerequisite, without claiming it is finished or proposing ATTACH again. BaseChange.lean:96 also supplies the upstream base-change clause, but it is not used as evidence of completion.

## WANTED

None. All mathematical sources used are present in the read-only literature tree.

## Findings and corrections

The imported statement agrees with Stacks Tag 0B9T (`perfect.tex`, `lemma-chi-locally-constant-geometric`, lines 7961 onward). Its proof was empty. The hypotheses and both conclusions are unchanged, including the absence of Noetherianity or reducedness assumptions. The finite-presentation module condition is the sheaf condition in the cited definition, not merely finite type. Relative flatness concerns the module, not the morphism.

The source reduces to perfection and arbitrary base change via Tag 0B91(2), then to Tag 0BDJ. I read those two lemmas and their proofs in `perfect.tex`, and the precise existing local-model statement. The model packages the perfection reduction as an ordinary finite free complex with cohomology comparisons after every base change. This is the needed interface: we do not need a canonical base-change map or a derived comparison theorem. In particular, the proof never tries to infer an arbitrary base-change isomorphism for individual higher direct images from flatness alone.

The existing node `lem-pc-universal-finite-free-complex` was found by whole-DAG searches for its declaration and finite free complexes. I also searched all blueprint nodes with blueprint_refs.py for “Euler characteristic”, “finite free”, “chi”, “locally constant”, “0B9T”, and “0B91”. Euler-characteristic definitions and special cases about degrees or fixed curves are not the present general statement. The universal model is reused, rather than replaced with a new node for the same construction. No node is created for the two-line rank-nullity cancellation.

I retained the original recorded searches, including their historical mention of the rejected attachment, as provenance. Five additional searches actually ran through msearch.py for Q23: LeanFinder on the full statement; Loogle on Euler/local constancy; Mathlib AlgebraicGeometry grep for eulerCharFiber/local Euler constancy; LeanSearch on the full statement; and a second LeanFinder phrasing about the Euler–Poincare/rank computation. All services returned successfully. I read the returned hits: Module.isLocallyConstant_rankAtStalk concerns the rank of a single flat module, and morphism base-change permanence or locally constant function characterizations do not supply fibre coherent cohomology. The second phrasing also found unrelated condensed/profinite free-module results. There is no exact match or one-line specialization for the item among these hits.

The ancestor command reports a null nearest blueprint ancestor for this existing node. I preserve that inherited metadata and its already-specific `from.place`, rather than inventing an ancestor. Its dependency chain supplies the Euler characteristics in the projective-curve Isom-graph boundedness prerequisite of the direct-image/alteration argument. I read the chapter and unit records and the current main-20261015 direct-images proof. The Picard universal-model citation is declared as a generic tool in split_report.tool_uses; it does not replace a chapter or unit step. This item is not a unit's key statement, so no unit realization record is changed.

## Unfinished work

None in this one-level split. The existing model theorem retains its own independent DAG work; its proof is not copied into this item. Delivery remains subject to the maintainer's independent mathematical review.

## Not duplicates

No new nodes. The general local finite-free model already exists as `lem-pc-universal-finite-free-complex` and is cited directly. The existing degree-local-constancy and fixed-curve perfectness nodes have narrower hypotheses and different conclusions; no replacement copies are created.

## Review by Q23

I checked the split against delivery-errors B–E with the source text and cited statements open. The item is exactly Stacks 0B9T. For its proof I read 0B91(2) and 0BDJ as well, verifying that the base is any scheme and that flatness is imposed on the finitely presented coefficient sheaf over the base. There are no new statements requiring separate source verification. All four steps are below 2000 characters; none hides an independent comparison lemma.

Step 1 uses the full statement of `lem-pc-universal-finite-free-complex`. That statement explicitly assumes proper finite presentation and a finitely presented relatively flat module, produces a neighbourhood and a complex supported in [0,d], and provides the comparison for every cartesian base change. These are precisely the hypotheses in the item. The source and the node do not require a Noetherian base. Its separately existing proof is not being treated as part of its statement or as a finished Lean proof.

Step 2 uses the same universal comparison, `def-pc-module-pullback`, and `def-pc-euler-characteristic`. I checked that the pullback definition actually supplies the tensor formula, and that the Euler definition calls cohomology the higher direct images of the structure morphism. On Spec L there is just one nonempty Zariski open; sheaves of modules are literally vector spaces with the zero value on the empty open, so kernels, images and quotients are computed as vector spaces. Pulling back each free term gives L^{r_i}. For a differential of image dimension b_i, a basis of the kernel extended to the domain gives dim ker = r_i-b_i; a basis of the preceding image extended to the kernel gives dim H = r_i-b_i-b_{i-1}. The finite alternating sum cancels the adjacent b terms. Thus this is an elementary explicit computation from the cited comparison and definitions, rather than an uncited Euler–Poincare theorem. It also proves finiteness and vanishing for the sums it uses.

Step 3 applies the already established formula to each canonical residue-field map. Since the same ranks work on the entire neighbourhood, the resulting function is constant there. No non-elementary topological statement is invoked: this is exactly the local-constancy definition written in the item.

Step 4 uses `def-pc-fibre-product`, whose statement gives the universal property and uniqueness with the projections, and `def-pc-module-pullback`, whose statement explicitly includes composition of pullbacks. I checked that these are the actual statements, not properties only inside their proofs. The nested fibre product represents the same pairs of maps as the composite base change. The composite coefficient pullback is the sheaf in the item. The universal model comparison applies directly to Spec kappa(s') -> V, with the original f and F; it does not require us to first prove relative flatness over S' or a canonical comparison of two derived objects. Its term ranks are the same r_i over either residue field, so the numerical equality follows from the step-2 formula. No separability, algebraic closure, reducedness, or field-degree assumption is used.

I tested the calculation on a zero complex, a one-term complex, and a two-term complex whose differential has changing rank: in the last case the two cohomology dimensions change together and their alternating sum stays r_0-r_1. This checks the sign cancellation and endpoints b_{-1}=b_d=0, including d=0. The empty base is vacuous, the zero sheaf and empty family have zero Euler characteristic, and nilpotents in the base never enter the rank cancellation. Arbitrary, including nonseparable, residue-field extensions give free terms of the same dimensions. All citations are backed by full verbatim statement quotes in citations.json; proof_deps is exactly the union of uses. The statement, sources and maintainer-owned fields are retained. No SGA source is used.
