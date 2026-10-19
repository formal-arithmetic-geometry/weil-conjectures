## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-regular-pinnings-low-base-codimension.json`: statement, split; four proof steps using existing nodes only. The statement is unchanged. No Mathlib match.
- `citations.json`: verbatim statement excerpts for every proof citation, with an additional excerpt specifying the exact fibrewise construction.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searches of `WeilConjectures/` in the read-only slopmaster2 source for the item id, potential/putative dualizing complexes and regular pinnings found no declaration stating this item.

## WANTED

None.

## Findings and route

The item was unsplit, and there was no prior sandbox node or report to preserve. Its definition of regularity uses finite residue-field extensions, as does the current reviewed prime-power theorem. The prime-power node `lem-per-regular-pullback-pinnings` already states a more general theorem with precisely the fibrewise supported comparison followed by the inverse absolute-purity pinning. Reusing it at exponent one follows the brief's instruction to cite an existing generalization rather than create another version. Its reviewed split became visible during this session; I reread the updated statement and checked its full dependency closure for a path to this item. There is none. In particular its low-base-codimension child is the separate existing `lem-per-regular-codimension-one-residues`, not this item's id. This delivery therefore introduces no circular reliance on the item itself and no new lemma restating a clause.

The source read was ILO, *Travaux de Gabber*, Exposé XVII, printed pp. 258–266, 268 and 280–284: Definitions 1.2.3.1, 1.3.1, 1.4.1, 2.1.1–2.1.2; Remark 1.4.2; Propositions 2.4.1.1, 2.4.2.1, 2.4.3.1 and 2.4.3.3; Theorem 3.1.2; Proposition 4.1.1; Lemmas 4.3.1.1–4.3.1.2 and 4.3.2.1–4.3.2.2. The source proves the item by normalization and radicial comparison. Those are already part of the existing general regular-pullback theorem's route. Here the additional argument is the explicit derivation of the all-cohomological-degree formula from potentiality and chain composition. Proof origin is marked agent because this is a DAG reuse argument, rather than a transcription of Lemma 4.3.2.1's proof.

I read the chapter and unit records and the current main-20261015 ancestor file. The chapter and unit route is unchanged. The fine arbitrary-field-duality expansion named in the inherited `blueprint.from.place` is in the intervening DAG; the current ancestor Markdown itself states the affine perverse bound. This non-key auxiliary item does not modify the unit realization. All proof citations belong to the same unit, so no off-unit tool declaration is needed.

## Not duplicates

No new nodes. The item is a specialization of existing `lem-per-regular-pullback-pinnings` followed by composition using `lem-per-general-costalk-transitions`; I reuse both and create no duplicate. Whole-DAG keyword searches, the sibling prime-power files, and blueprint searches for `radicial`, `dualizing`, `pinning`, and `regular pullback` were read. Existing stronger material was preferred to a new radicial comparison node.

## Review by Q27

I checked B–E with the item, both coefficient definitions, both cited theorems and the ILO passages open. No new statements or nodes were introduced, so B1–B8's new-node source, small-case and Mathlib-leaf obligations create no additional work. The unchanged statement is self-contained and retains all its hypotheses, all cohomological degrees, and its unrestricted total codimension. Blueprint provenance and Mathlib records are retained. I ran the mandated logged search command for LeanFinder, Loogle, grep and LeanSearch and read all returned hits. They concern scheme normalization, ordinary stalks, or categorical regular monomorphisms, not these potential-dualizing pinnings. The older searches already in the item were preserved; the newly run searches are also recorded exactly. No unavailable service is claimed to have returned a negative result.

Step 1 cites `def-per-potential-dualizing` and `def-per-potential-dualizing-complex`. I compared their formulas: at exponent one both use the same roots-of-unity line, positive tensor and negative dual twists, localized closed-support costalk, geometric immediate specialization, strict-local normalization degree, and trait map with evaluation at the tame generator followed by inverse evaluation at 1 minus that generator. Thus there is no unstated comparison of distinct coefficient categories or transition normalizations. This step is elementary substitution into the two definitions.

Step 2 cites the statement of `lem-per-regular-pullback-pinnings`. I verified every hypothesis: both schemes are Noetherian excellent, the morphism is flat with geometrically regular fibres tested by finite field extensions, ell is invertible, and K is pinned potential for the given dimension function. Its conclusion expressly supplies the dimension function and potentiality. Its statement, rather than its proof, also expressly supplies the exact supported closed-fibre exchange and inverse absolute-purity class used to define the item's maps. Both constructions use the canonical closed-support comparison, and the absolute-purity class is the same ILO XVII 2.4.1.1 class, used via the item's `lem-per-regular-gysin-calculus` or the prime-power theorem's `lem-per-absolute-gysin-purity`. I reread both class statements; no field trace normalization or arbitrary choice of dualizing isomorphism is being substituted. This is the non-elementary theorem application, correctly marked as such.

Step 3 cites `lem-per-general-costalk-transitions` for the existence of a finite immediate factorization and additivity of its codimensions. It cites `def-per-potential-dualizing` for the dimension-function edge equality. Summing the edge equalities is the whole argument: the dimension function furnished by Step 2 gives exactly the target twist-shift equality. No independent dimension formula is assumed here.

Step 4 cites `def-per-potential-dualizing` for the immediate pinning equality, and `lem-per-general-costalk-transitions` for composition, twists and the codimension-zero transport clause. I wrote the induction with its base, the degree i+2j, intervening twist j, and the final identification of the chain composite with the specified generalized transition. This proves the displayed formula for every i, including degrees where both coefficient-line cohomology groups vanish. Codimension zero is treated separately using naturality of the residue-field-site pinning. The arbitrary-codimension assertion is consequently not hidden behind a vague claim of transport.

For E1–E4 I tested the identity morphism (b=0), a regular scheme over a field (base codimension zero, arbitrary fibre codimension), a trait specialization (c=1), and a specialization with c_P greater than one but c_X=1. The induction covers all four without adding finite type, compactifiability or perfectness. Empty schemes give a vacuous assertion. A codimension-zero geometric automorphism is covered by the residue-field sheaf morphism, rather than by an assumption that the automorphism itself is the identity. Twists accumulate by addition and the difference of the two dimension values equals c, so signs and degrees match the item.

For C1/C4, each non-elementary input is a cited existing statement and each citation is backed by a verbatim excerpt in citations.json. Step 2 additionally quotes the whole construction paragraph. For C6 I checked the current live statement-and-proof dependency closures of all four cited nodes: none reaches this item. No step exceeds 2000 characters. There is no new child that restates the item (D1/D2), no source error or disputed statement to repair, and no SGA source is cited. The work corrected the absent proof and proof dependencies, not the statement or the project's route.

## Unfinished work

None in the stage-1 split. Delivery checks and push are run after this report is written; their results are recorded below.

## Delivery validation

The first dry run rejected a definition excerpt shorter than the required 40 characters. I replaced it with the entire coefficient-and-twists paragraph from that definition; the proof did not change.
