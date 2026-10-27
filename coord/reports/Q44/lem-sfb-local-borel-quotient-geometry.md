# Stage-1 report: lem-sfb-local-borel-quotient-geometry

Group Q44; direct delivery; 2026-10-24.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-local-borel-quotient-geometry.json`: statement node, now split into twelve proof steps; Mathlib searches found no match. The mathematical statement, its statement dependencies, existing provenance and earlier search entries are retained unchanged.
- No new nodes and no Mathlib leaves. `citations.json` contains a verbatim statement for every step/node citation. `searches.jsonl` is the search command's unmodified log. The sandbox scripts only write the sandbox.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint id and for Borel, reductive, unipotent radical, homogeneous quotient and scheme normalizer terminology. The hits concern Lie algebras or Borel–Moore cohomology, not this assertion. No project declaration gives all the clauses. I wrote no Lean and invoked no compiler or build tool.

## Literature wanted

WANTED: Conrad, *Reductive group schemes*, `https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf`, locally as `literature/conrad-reductive-group-schemes.pdf`, for this item and its already-existing relative structural inputs. I read the primary author PDF online, including Proposition 5.2.3, Corollaries 5.2.5 and 5.2.8 and their proofs (printed pp.152–156), Theorem 4.1.7 (pp.112–114), Proposition 2.1.6 (pp.61–62), and Theorem 2.3.6 (pp.72–75). I did not download or write a literature file. Since there is no local copy, the proof is marked agent-written with that URL and these precise places; the proof adapts Conrad's argument to the local-ring hypotheses.

## Problems found and corrected

No mathematical statement dispute. The imported statement is consistent with Conrad's local split Borel geometry. It had no proof. The split supplies the dynamic construction rather than making new nodes that repeat its conclusions.

The initial candidate prerequisites for quotient representability turned out already to exist in the live DAG: `lem-sfb-relative-smooth-subgroup-normalizer` and `lem-sfb-relative-self-normalizing-quotient` (created for the relative adjoint rank-one flag curve). I opened their complete statements, reused them, and created no duplicates. Similarly the root-support argument uses the existing relative tangent-weight theorem rather than introducing a Borel-specific copy.

I corrected draft Stacks references to the actual tags and labels: 00FN `lemma-Noetherian-permanence`, 00FP `lemma-Noetherian-finite-type-is-finite-presentation`, 00NX `lemma-finite-projective`, 01T6 `lemma-finite-type-noetherian`, and 01OX `lemma-immersion-into-noetherian`. I read their local TeX statements/proofs. The algebraic-group inputs are cited to Conrad or the existing field nodes; no SGA source is used.

I read the latest blueprint's direct-image statement under `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`. The item is a supporting input on its existing alteration/geometric-reductivity route, not a replacement of a unit step. The ancestor command reports `blueprint.from.node = None`; I retained that existing provenance, its detailed place and via chain, rather than inventing an ancestor. Whole-blueprint searches for Borel, Borel pair, torus weight, normalizer, self-normalizing, smooth connected normalizer and quotient sheaf found no matching blueprint statement. No chapter or unit record is changed.

## Not duplicates

No new node pairs to compare: the delivery introduces zero nodes. The item extends field results to a Noetherian local base and includes arbitrary base change. It is not merely the field Borel-pair statement; conversely the general self-normalizing quotient node does not give self-normalization, the Borel semidirect decomposition or constant relative roots.

## Review by Q44

I checked this split against sections B–E of `coord/delivery-errors.md` with the node statements open. The essential distinction is between a field theorem and its relative form; none of the field nodes is used directly as a relative theorem. There are no statement-only new nodes, so the new-node shape and novelty requirements are vacuous. The unchanged item introduces all group, torus, unipotence, Borel, torsor and root-weight notions explicitly, with its existing definition dependencies. Every non-elementary input in the proof is an existing cited node. The two elementary steps are finite-generation bookkeeping (using the actual algebra theorems) and the trivial torus case. No proof step is over 2000 characters; no separate hidden claim is being moved wholesale into a new node.

1. I verified the statements of the two Noetherian algebra nodes: finite-type algebras over Noetherian rings are Noetherian, and finite type over such a ring is finite presentation. They supply exactly the finiteness needed for B, T and maps among affine finite-type schemes. An A-algebra generating set remains a generating set over any intermediate target algebra, so the map claim is elementary. This is valid over rings with nilpotents. Sources: Stacks 00FN and 00FP; Conrad's finite-presentation hypotheses in Proposition 5.2.3.

2. The relative tangent-weight node explicitly permits a general smooth affine group with a split torus action, not just reductive groups. Its statement gives finite projectivity and arbitrary scalar extension for every character summand. The finite-projective localization node gives freeness on a standard neighbourhood of the maximal ideal; the local-ring unit argument makes that neighbourhood all of S. Thus neither constancy of weights nor freeness was assumed. I checked both H and B meet the smooth affine finite-type hypotheses. A closed inclusion is injective on dual-number points, so it gives the asserted tangent injection on each geometric fibre. Source: Conrad's graded tangent-bundle discussion and the weight-subbundle argument in Proposition 5.2.3, together with 00NX.

3. The relative character-duality node describes actual Laurent-monomial characters locally on the base, with no reducedness assumption. The local-ring argument makes their labels global; restriction therefore identifies characters with Z^r. The field opposite-root node explicitly gives one of each opposite pair in the Borel tangent algebra, in every characteristic. It is applied only over the algebraic closure of the residue field. The tangent-base-change node then transports the weight supports to all fibres. This proves the exact root assertions of the item rather than a differential-character substitute.

4. The regular-cocharacter Borel node supplies the chosen cocharacter only on the closed geometric fibre. Character duality supplies its integer tuple, which is then an actual monomial cocharacter over A. The field cocharacter-parabolic node explicitly states Z_lambda=T for a regular cocharacter through a split maximal torus; the relative dynamic node supplies Lie(Z)=weight zero. Its P tangent formula also gives all the B tangent equalities on the closed fibre. Step 2 made every module involved finite free, so invertibility lifts by the determinant-unit argument. This is exactly the local-base form of Conrad's lifting and Lie comparison in Proposition 5.2.3; it does not assume a relative Borel classification.

5. The dynamic node applies to the conjugation action on B as well as H, and gives smooth connected P_B and its tangent formula. The smooth-subgroup tangent-generation node is a theorem over an algebraically closed field; I use it separately on every geometric fibre with one subgroup spanning the whole Lie algebra. The fibre-isomorphism node then gives the relative equality, since the source is smooth and all maps are locally finitely presented by step 1. I did not use equality of fibres alone for a nonsmooth source. Source: Conrad Proposition 5.2.3.

6. The factor B=P_B into P_H is the written orbit-extension/coordinate-ideal argument. For equality I again checked the precise hypotheses of tangent generation and the relative fibre criterion. T into Z_H is an actual morphism, from constant conjugation orbits, and the field regular-cocharacter theorem supplies its fibrewise isomorphism. The dynamic node explicitly gives the normal kernel, semidirect multiplication and evaluation retraction once P_H=B and Z_H=T are established. No clause of the item was assumed under another name.

7. The field Borel-pair node supplies the largest smooth connected normal unipotent subgroup R on each geometric fibre. The dynamic node gives U that has those properties and hence lies in R. The unipotent-to-multiplicative node kills R to T on all test algebras, giving the reverse inclusion in the kernel. It accepts the precise geometric unipotence definition used in the item. This verifies the maximality clause, not merely that the fibre of U is unipotent. Source: Conrad Corollary 5.2.5 and the field radical statements.

8. The relative normalizer node explicitly gives representability, finite presentation, the B inclusion, and arbitrary base change; it makes no flatness claim for N. The field Borel-normalizer node is scheme-theoretic, including nonreduced test rings, so the geometric-fibre equality is available. I checked the fibre criterion allows a nonsmooth target N and needs a flat locally finitely presented source B and a locally finitely presented map. The smooth-flat node gives the former, and step 1 the latter. Source: Conrad Proposition 2.1.6 and the proof of Corollary 5.2.8.

9. The field cocharacter-parabolic statement gives a projective representing quotient, not only a proper variety, for every geometric fibre. The relative self-normalizing quotient node's hypotheses are all now verified: smooth affine finite presentation, nonempty connected geometric fibres, closed finitely presented subgroup, and self-normalization. Its statement explicitly gives a smooth representing scheme, properness from geometric projectivity, the torsor kernel-pair formula and arbitrary base change. The smooth-flat node supplies flatness and local finite presentation of pi. This is the exact application of Conrad Theorem 2.3.6 in Corollary 5.2.8.

10. The relative quotient node does not explicitly state quasi-compactness of pi, so I did not take that clause from it. The finite-type-over-Noetherian node gives Noetherian H, and the Noetherian-open-immersion node gives quasi-compactness of every open inverse image of an affine of Q, since H is itself affine. These statements are exactly what this step uses. Sources: Stacks 01T6 and 01OX.

11. I checked that the dynamic node and the quotient node both state arbitrary, rather than only field, base change. The maps being compared have explicit formulas: contraction/evaluation at zero, multiplication and the right-coset kernel pair. Pulling these formulas back proves the asserted compatibilities; no descent of an arbitrary chosen object is assumed. Agreement on affine overlaps covers non-affine S'. Non-Noetherian S' is allowed by both cited nodes. Source: Conrad Theorem 4.1.7 and the quotient-sheaf formulation of Theorem 2.3.6.

12. I tested H=T, B=H and rank zero directly. Trivial conjugation makes the contraction kernel the identity; the right-coset sheaf is represented by S. Other checks included GL_2 over a field, GL_2 over the dual numbers, a mixed-characteristic local ring, and small positive characteristics. The proof never replaces characters by their differentials or assumes that tangent equality implies subgroup equality without smoothness and connectedness. The excluded zero ring causes no issue; after a base change to the empty scheme the asserted identities are empty pullbacks.

I also traversed statement/proof dependencies of every principal cited structural node and found no route back to this item. The generic algebra and scheme finiteness tools from other units are declared in `split_report.tool_uses`; they do not replace the constructibility unit's route. I copied verbatim full cited statements into `citations.json`, including all needed clauses, and checked each step against those statements rather than the proofs behind them. No fabricated Mathlib search is recorded: item-specific searches and the unsuccessful candidate-prerequisite searches all ran through msearch.py, and I read the displayed hits. The Loogle broad initial pattern produced a parse diagnostic, so I also ran the well-formed quoted-name query; its hits are measurable Borel quotients, not Borel subgroup schemes.

## Unfinished work

None within the one-level stage-1 split. The reused unsplit prerequisite nodes remain their own work items. No attachment is claimed and no new prerequisite was introduced.
