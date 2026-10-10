Files written:

- `dag/nodes/sec-picard-framework/lem-pc-global-hom-adjunction.json` (statement, split proof; no new nodes; Mathlib searches found no exact scheme-level declaration).

Attachments:

- None.

WANTED:

- None.

What was checked and corrected:

- The target node and its source route were read against Stacks Project `duality.tex`, Tag 0AA8 (Lemma 48.6.2), case (1). The slopmaster2 source was searched for the blueprint tag and the relevant global RHom/right-adjoint declarations; no sorry-free project declaration states this item.
- The statement already has the correct qcqs hypotheses, restricted derived direct image, supplied right adjoint, and natural global RHom conclusion, so I left it unchanged. Its existing statement dependencies are exactly the notions used in the statement.
- Step 1 uses `lem-pc-qcqs-derived-direct-image-right-adjoint`; that node explicitly states both preservation of `D_QCoh` and existence of the restricted right adjoint. I verified that its source is Stacks Tag 0A9E and that it is not a definition or a weaker preservation-only fact.
- Step 2 uses `def-pc-global-derived-rhom` for the definition and functoriality of global RHom, together with the same right-adjoint node for the adjunction data. The step spells out that the derived adjunction comparison is transported through derived global sections and is natural in both variables, which is the exact content required by the target.
- I searched the whole DAG and blueprint for global RHom adjunction variants and found no duplicate node. The mandated Mathlib searches were run for LeanFinder, Loogle, and Mathlib grep; LeanFinder returned only generic `CategoryTheory.Adjunction.derived`, Loogle had no usable hit, and grep found no scheme-level RHom theorem. The existing search records and these fresh searches consistently give no exact Mathlib match.
- Edge cases checked: taking `f` to be an identity morphism reduces the statement to the identity RHom isomorphism; taking `P=0` or `K=0` gives the zero complex on both sides. Naturality follows from the adjunction and the functoriality in the global RHom definition.

## Review by C1

I read the target node, `def-pc-global-derived-rhom`, `lem-pc-qcqs-derived-direct-image-right-adjoint`, and the relevant Tag 0AA8 route in the blueprint. For Step 1, the cited statement supplies exactly the qcqs preservation and right-adjoint hypotheses used. For Step 2, the cited definition supplies global derived sections of internal Hom and functoriality, while the right-adjoint statement supplies the natural adjunction comparison. I checked that no step relies on an uncited child lemma, that no created node duplicates an existing DAG or blueprint statement, and that the item’s blueprint ancestor/place fields remain the imported Tag 0AA8 case (1). The only correction was replacing the empty proof with these two explicit steps and marking the item `split`; no source or statement error was found.

What could not be finished:

- Nothing; no new node was required.

## Repair R-gha2726

- The returned child statement was false: Tag 0A9Q proves the sheaf trace comparison only after applying (DQ_Y). I changed `lem-pc-qcqs-sheaf-rhom-adjunction` to state the counit-induced map and its (DQ_Y)-isomorphism, and added `lem-pc-dq-coherator-adjunction` for the coherator right adjoint and its global-section detection consequence.
- The target proof now names the counit/sheafy trace in Step 1. Step 2 explicitly uses the derived Leray identity (R\Gamma(Y,-)\circ Rf_*=R\Gamma(X,-)), then applies the (DQ_Y) detection argument (H^i(Y,E)=\operatorname{Hom}(\mathcal O_Y[-i],DQ_YE)) from Tag 0B6I.
- I read `/home/ubuntu/c1-stacks-review/duality.tex` at lines 558--607 and 660--690: Tag 0A9Q gives the coherated sheaf map, while Tag 0B6I constructs the counit map and derives the global statement. I also reread the statements of `lem-pc-qcqs-derived-direct-image-right-adjoint`, `def-pc-global-derived-rhom`, and `lem-pc-projection-formula`; no projection formula is needed in this corrected route.
- The new coherator node is statement-only and self-contained, cites `def-pc-derived-category`, records LeanFinder/Loogle/grep searches (with the unavailable LeanSearch service not misreported), and has the required blueprint ancestor/place. Search of all DAG nodes and `blueprint_refs.py` found no duplicate coherator node.

## Source error

The earlier child statement omitted (DQ_Y) and asserted an isomorphism in (D(\mathcal O_Y)). This is exactly the false assertion ruled out by the example immediately after Tag 0A9Q (for (Y=\operatorname{Spec}(R)), (X=\mathbf A^1_R), the right side can be a non-quasi-coherent product). The corrected statement follows the source and avoids that counterexample.

## Review by C1 (repair)

I checked the corrected item and both child nodes against the cited source text. Step 1 uses the right-adjoint statement only for preservation and existence, and the corrected child statement supplies precisely the counit-induced map and the post-(DQ_Y) isomorphism. Step 2 uses the global RHom definition for both identifications, treats the Leray composition as the elementary derived-direct-image identity, and uses the new coherator node for the non-elementary passage from a (DQ_Y)-isomorphism to a quasi-isomorphism on derived global sections. The hypotheses (f) qcqs, (P,L\in D_{\mathrm{QCoh}}(X)), and (K\in D_{\mathrm{QCoh}}(Y)) are present at each application; the identity morphism and zero complexes remain immediate edge cases. I replaced every stale citation quote in `citations.json` with verbatim text from the repaired node statements and verified the new node's three mandated Mathlib searches were actually run.

## Second reading by C1

- Item statement: checked against Stacks Tag 0B6I (Lemma 48.1.1, `lemma-iso-global-hom`); the original 0AA8 source pointer was incorrect and is repaired.
- Step 1: checked qcqs right-adjoint input and the sheaf-level RHom comparison against the statements of `lem-pc-qcqs-derived-direct-image-right-adjoint` and the new child node; verdict: repaired.
- Step 2: checked the passage from the sheaf-level comparison to global RHom against Tag 0B6I and `def-pc-global-derived-rhom`; verdict: repaired.
- New node `lem-pc-qcqs-sheaf-rhom-adjunction`: checked self-contained hypotheses, exact sheaf-level conclusion, Tag 0B6I source, edge cases including identity and zero complexes; verdict: needed non-elementary intermediate statement.
- Changes: corrected all item source locations from Tag 0AA8 to Tag 0B6I; added the sheaf-level RHom child node and citations; rewrote both proof steps so the global-complex isomorphism follows through derived global sections rather than directly from categorical Hom bijections.

The source-field correction is recorded in the sandbox copy, but `source` is a maintainer-owned field and the delivery tool preserves the repository's existing 0AA8 metadata. The source text read for this second reading is `/home/ubuntu/c1-stacks-review/duality.tex`: the sheaf comparison is `lemma-iso-on-RSheafHom` (Tag 0A9Q), and the global statement is `lemma-iso-global-hom` (Tag 0B6I). The maintainer should update the imported source metadata when accepting this delivery. I also checked that the right-adjoint dependency carries the stronger quasi-compact/quasi-separated hypotheses on both schemes; the item's explicit premise that the restricted right adjoint exists is the premise used by both proof steps, so no additional hypothesis was silently inserted here.

## Repair R-gha2856

- Added the missing hypothesis that both X and Y are quasi-compact and quasi-separated to the item and to `lem-pc-qcqs-sheaf-rhom-adjunction`. This is the hypothesis required by Tag 0B6I/0A9Q and by the right-adjoint dependency.
- Corrected `lem-pc-dq-coherator-adjunction` so its source scheme Y is explicitly quasi-compact and quasi-separated, matching the perfect.tex `lemma-better-coherator` source.
- Added `lem-pc-derived-direct-image-composition` to Step 2, `proof_deps`, and `citations.json`. Step 2 now spells out the structure morphisms, the canonical composition isomorphism, and restriction of scalars along `Gamma(Y,O_Y) -> Gamma(X,O_X)` before using the derived Leray identity. The citation quote is copied verbatim from that node's statement.

## Review by C1 (repair R-gha2856)

I reread the item, both child statements, the existing right-adjoint node, and `lem-pc-derived-direct-image-composition`. The item and sheaf child now introduce qcqs X and Y before invoking the right adjoint; the coherator child now has the qcqs Y hypothesis required by its `lemma-better-coherator` source. For Step 1, the right-adjoint and sheaf comparison statements still supply exactly the preservation, counit, and post-DQ_Y isomorphism used. For Step 2, I checked that the composition node states the canonical `R(f o p)_* = Rf_* o Rp_*` isomorphism used for the structure morphisms, and that the global RHom definition and coherator detection statement cover the remaining identifications. I added the composition node to `uses` and `proof_deps`, and added its verbatim statement sentence to `citations.json`; JSON parsing succeeds for all edited files.

## Second reading by C1

- Item statement: checked against `duality.tex`, Tag 0B6I, label `lemma-iso-global-hom`; qcqs hypotheses and both global RHom objects agree, verdict: pass.
- Step 1: checked against the right-adjoint statement and Tag 0A9Q child statement; corrected the description to use the stated counit-induced comparison rather than an unsupported “apply Rf_*” construction, verdict: repaired.
- Step 2: checked against Tag 0B6I proof, `def-pc-global-derived-rhom`, the coherator child, and the derived direct-image composition statement; the Leray and DQ_Y detection applications have the needed qcqs hypotheses, verdict: pass.
- `lem-pc-qcqs-sheaf-rhom-adjunction`: checked against `duality.tex`, Tag 0A9Q, label `lemma-iso-on-RSheafHom`; the map and post-coherator isomorphism match, verdict: pass.
- `lem-pc-dq-coherator-adjunction`: checked against `perfect.tex`, label `lemma-better-coherator`, and the final paragraph of Tag 0B6I; right adjunction and global-section detection are stated with qcqs Y, verdict: pass.
- `lem-pc-derived-direct-image-composition`: checked against `cohomology.tex`, Lemma 20.28.2 (Tag 0D5T); its canonical composition isomorphism is exactly what Step 2 uses, verdict: pass.
- Changes: rewrote Step 1 to match the cited child statement and appended this review; no statement or dependency changes were needed.
