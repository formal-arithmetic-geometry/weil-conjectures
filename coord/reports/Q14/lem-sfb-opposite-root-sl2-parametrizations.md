## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-opposite-root-sl2-parametrizations.json`: statement, now split; unchanged statement and statement dependencies; five proof steps using four existing nodes. Mathlib verdict: no matching group-scheme theorem.
- `citations.json`: six step/node citations, with literal excerpts from the existing statements.
- `report.md`: this report. `searches.jsonl` is the search command's own log. `milne.txt` is a local text extraction of the available PDF, used only for reading.

New nodes: 0. Mathlib leaves added: 0. No Lean files were written and no compiler or Lake command was run.

## Attachments

None. Searches under `lean/WeilConjectures/` for the exact blueprint tag and for SL2, opposite roots, and root subgroups found no declaration of this item. The related `lean/Sheaf/` search also found no attachment.

## WANTED

None. The source book is present as `literature/milne-algebraic-groups_iAG2017.pdf`.

## Problems found and changes

The item was statement-only. Its statement is correct, including the all-characteristics clause. I retained it verbatim. An existing rank-one centralizer node already supplies the upper-root map, the centralizer's semisimple rank, and coroot uniqueness; the existing rank-one classification supplies actual matrix models. Creating another existence lemma for the opposite-root pair would duplicate much of these inputs and risk merely relocating this item's clauses. Instead the proof carries the matrix argument itself.

The old grep record says “No hits” for `coroot|root[Ss]ubgroup|root_subgroup`. The newly run command found Lie-algebra coroot hits. I preserved the inherited search history and appended the actual five current command records. The hits are Lie-algebra/root-pairing and abstract matrix-group results, not algebraic-group-scheme maps. I read the `corootSpace` definition in `Mathlib/Algebra/Lie/Weights/Cartan.lean` and `sl2SubalgebraOfRoot` / `mem_sl2SubalgebraOfRoot_iff` in `Mathlib/Algebra/Lie/Weights/Killing.lean`; they cannot provide this assertion, especially in arbitrary characteristic. The two semantic phrasings, Loogle, LeanSearch, and source grep were all run through the required msearch command; their results are retained in `searches.jsonl` and the node.

The inherited `blueprint.from.node` is null. `tools/blueprint_refs.py ancestor` confirms the broken ancestor chain rather than identifying a blueprint node; I retained this inherited value and the detailed existing place/via information. Searches of the entire imported blueprint for SL2, SL_2, opposite root, and coroot found no matching imported statement. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and current direct-image proof, as well as the recorded chapter and unit. This is an internal supporting algebraic-group argument on the inherited route; no higher-level route was changed.

Milne's printed Theorem 20.33 needs the semisimple-rank-one qualification provided by its section, and its final prose swaps two derived-group labels. The existing classification node explicitly already corrects those source defects. I use its displayed product pairs, not the swapped prose. This does not require correcting the item's statement.

## Unfinished work

None for this stage-1 item. The four cited nodes remain separate DAG work; this delivery does not claim to prove them or to finish Lean formalization.

## Not duplicates

No new nodes were created. Whole-DAG statement searches for SL2 and rank-one groups, and source-place searches for Milne 21.11, 21.24, 20.20, 20.23, and 20.31, found the existing rank-one classification and reflection nodes. Those are cited directly. Root-subgroup uniqueness and the projective-matrix realization are also reused. All four proof inputs have the same unit as this item. Traversing their statement and proof dependencies confirmed that none reaches the item.

## Review by Q14

I read Milne Theorem 21.11(a)--(e), printed pp.428--430, and paragraph 21.24, p.432, for the item, together with Theorem 20.33 and Corollary 20.34, pp.418--419, and the explicit matrix discussion in 20.38--20.40 and 21.3--21.5. I also read 20.31--20.32 to check how the rank-one reduction relates to the source's central covering construction, and Example 5.49 for the scalar quotient convention. There are no new nodes needing an independent source assignment.

For step 1 I opened the statements of `lem-sfb-reductive-rank-one-reflections` and `lem-sfb-split-rank-one-classification`. The former literally states that the centralizer is reductive of semisimple rank one, and supplies an upper-root embedding with tangent space g_alpha. The latter applies to a reductive group with that rank-one quotient and its maximal torus and gives an isomorphism of pairs, not just an isomorphism of groups. Consequently the chosen torus is carried to the diagonal torus, and the model reduction has all its hypotheses.

For step 2 I opened `lem-sfb-projective-frames-pgl`. It explicitly identifies PGL with the determinant-open subscheme of projective matrix space and says multiplication is matrix multiplication, exactly what this step uses. I take S=Spec F and rank 2; no assertion about arbitrary projective bundles or Picard groups is used. In that model the equations a=d,c=0 or a=d,b=0 are homogeneous closed equations and force the remaining diagonal coordinate to be invertible. The displayed normalized coordinates therefore give inverses over every algebra. This checks both closedness and scheme isomorphism, rather than just injectivity on F-points. The SL and GL cases are direct coordinate equations. This is a matrix calculation using an existing projective-matrix realization, not an additional classification lemma hidden in a step.

For step 3 I reread the rank-one node's actual statement for both the tangent-space inclusion and the one-dimensional root spaces, and `lem-sfb-reductive-root-subgroup-parametrizations` for uniqueness among smooth connected closed T-normalized subgroups with the specified tangent space. The equations of step 2 establish these hypotheses. Direct conjugation computes character weights, and the identity chart in PGL makes the calculation valid in characteristic two. Since g_alpha is a nonzero weight space already inside Lie(H), it is one of the two model off-diagonal lines. The one-dimensional assertion ensures equality with the ambient g_alpha, not merely containment. Thus the uniqueness citation says exactly what the identification needs.

For step 4 I checked the entire reflection/uniqueness clause of the rank-one node. The explicit matrix w lies in the model H, swaps the diagonal coordinates, and gives a nonidentity normalizer class. The cited node identifies that class with s_alpha because the rank-one normalizer quotient has exactly two elements. Evaluating the torus identity on each character proves the reflection formula with the candidate signed cocharacter. Its uniqueness gives the canonical coroot itself. I did not replace equality of cocharacters by equality of differentials, which would lose information in small characteristic.

Step 5 uses the preceding steps and three explicitly written 2-by-2 matrix identities. Conjugation by w reverses the two root groups and inverts the diagonal parameter, so the same sign choice simultaneously fixes both restrictions and the coroot. This avoids choosing two unrelated additive parametrizations and then asserting their compatibility.

For the B--E checklist I checked self-contained hypotheses, single TeX escaping, the actual scope of each citation, absence of proof-only constructions taken from another node, no cycles, and no off-unit replacement. All non-elementary inputs are cited: the centralizer/rank-one assertion, classification, projective realization, root-subgroup uniqueness, and coroot uniqueness. The remaining claims are the written matrix and tangent-coordinate computations. No step exceeds 2000 characters. All six citations in citations.json are verbatim substrings of the statements, not paraphrases.

Small-case checks: G=T has no roots, so the assertion is vacuous. For SL2 the upper weight is z^2 and the candidate coroot is h(s); for PGL2 the root is the diagonal ratio while the coroot is its square parameter; for GL2 it is diag(s,s^-1). These distinguish the simply connected and adjoint cases. In characteristic two z^2 is a nontrivial torus character even though its differential vanishes; the proof uses characters and projective coordinates throughout. Extra central torus factors are fixed by w and both root groups. For the negative root, the conjugation formulas show that both subgroup restrictions are reversed and the cocharacter is inverted. Over F[epsilon]/(epsilon^2) the same polynomial identities and coordinate inverses still apply, so the proof does not discard infinitesimal subgroup information.
