# Stage-1 delivery: lem-pur-constant-purity-frobenius-square

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-constant-purity-frobenius-square.json: statement item, now split into six steps. Mathlib verdict: no match; no new nodes and no Mathlib leaves.
- citations.json: verbatim statement quotations for every citation of every item step.
- searches.jsonl: actual msearch results retained. Existing item searches are preserved and the current queries appended.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag and by purity/Frobenius/constant-Weil concepts. The nearest upstream statement, AlgebraicGeometry.Etale.exists_tateOrientation_isWeilMorphism_untwistedSmoothTrace (TraceEquivariance.lean:57), ends in sorry, uses finite coefficients and existential orientation data, and does not attach this canonical rational comparison. WeilDual.lean's compatibility theorem assumes the relevant equivariance as hγ and consequently does not prove the item.

## WANTED

None. All sources used are present in literature/.

## Corrections and findings

The item statement was retained verbatim. Its seeded proof was empty. The important distinction is that the existing theorem thm-pur-weil-equivariance-of-purity-and-trace explicitly defines its exceptional exchange using the purity composite, whereas this item uses the adjunction mate of inverse compact-support exchange. It would be C4 to cite the purity square alone and silently equate these maps. Step 5 proves equality at the constant input from the theorem's separate exceptional-counit clause, using counit naturality and uniqueness of adjoint transpose.

The strict-datum hypothesis of that theorem is stronger than an arbitrary rational Weil pair. It is satisfied here by the canonical constant pair and its coherent finite coefficient data. Nothing here asserts that an arbitrary rational Frobenius has a stable integral lattice. Geometric Frobenius is semilinear: the proof uses the theorem's underlying-scheme/retagged square and the compact-support transport definition, and does not apply a k-linear square theorem directly to it.

## Unfinished

None within this one-level split. All dependencies already exist; no dependency node was edited or newly created. No Lean code, compiler, Lake command, repository write, or repository git command was used.

## Not duplicates

No new nodes. Whole-DAG and blueprint searches for purity, constant Weil, and purity and trace located the existing equivariance theorem, canonical coefficient data, and the exact constant-composition and completed-operation lemmas used here. The item has no exact imported blueprint duplicate: the general strict-data theorem does not itself state identification with the compact-support mate or the canonical constant-pullback clause.

## Review by Q47

I read the chapter sec-smooth-purity and unit sk-thm-purity-transport, especially its coefficient transport and dualizing-complex steps. For the item I read the current main-20261015 smooth dualizing corollary proof (first sentence, purity at the coefficient unit), prop-weil-operations.proof.md (sentences 1 and 3), and the purity-equivariance proof in sec-six-functors (Steps 1 and 2). The blueprint is agent-written, so proof_origin remains agent. I read the current DAG statements, including their repairs, rather than relying on the older blueprint's blanket exchange identifications. No SGA source is used. There are no new-node sources to review.

Step 1 cites the separated finite-type base-change lemma for precisely those two properties and the smooth permanence lemma for dimension d after base change. The completed-unit lemma explicitly supplies constructibility, uniform Tor bound [0,0], the actual quotient system, and the identification of its rational/common-stage pullback with the usual unit identification. The constant-Weil definition constructs the canonical datum from compatible finite maps. The strict Tate-datum definition admits exactly their rationalized common-stage images, so this input is admissible. Spec k_0 is separated finite type over itself; the item supplies the corresponding hypotheses for X_0. The prime inequality makes the finite rings admissible. Generic permanence nodes are declared as tool uses.

Step 2 uses the constant-ring composition lemma's displayed equation twice for the two factorizations of ag_X=g_sa. Its statement concerns arbitrary scheme morphisms, so semilinearity causes no hypothesis failure. The explicit equality sends each constant section to itself and commutes with actual coefficient reductions. The completed-operation substitution lemma states compatibility with whole-system maps and identifies the actual completed compositor, so applying derived limit is justified for coherent system maps, rather than attempting to infer equality from unrelated levelwise morphisms. The operation definition then specifies precisely their rational/common-stage images. The constant-Weil definition fixes the same finite maps and their integral/rational images. This is a short argument from those cited interfaces, marked elementary, with no additional comparison lemma hidden.

Step 3 uses the tensor-pullback lemma's naturality and compatibility with unitors, which its statement expressly includes at the field stages. The canonical twist definition gives exactly (theta_X tensor tau_d) mu; expanding b and shifting identifies the two composites. This does not replace the Tate comparison with an unspecified rank-one automorphism and does not insert an extra power of q.

Step 4 uses BOTH clauses of the existing purity-equivariance theorem: its purity square and equivariance of the exceptional counit. I checked its statement's explicit E_K formula and strict input restriction. The compact-support transport definition gives F(varphi) beta with the actual compactification exchange, including its completed, rationalized and common-stage conventions. Thus the beta occurring in the counit square is the beta of this item. The geometric input and strict constant datum were checked in Step 1. This theorem is declared as a generic tool use; its lecture-notes purity route is retained.

Step 5 uses the adjunction-mate definition's transpose characterization and uniqueness. With K=Lambda_s, counit naturality changes epsilon_K F(G(theta_0)) into theta_0 epsilon_PK; theta_0 is an isomorphism and can be cancelled. Precomposing by beta_GK inverse gives the required transpose equation. All domains are written: FQGK to PK and its adjunct QGK to GPK. This proves the needed exchange identification instead of presuming it. Naturality and cancellation are elementary category operations, not an additional unproved geometric claim.

Step 6 substitutes the two already proved equalities into the existing purity square. The dualizing corollary explicitly says its identification is the inverse of the transported purity map, so its statement gives precisely the final normalization. The proof stays in the common-stage category throughout. Every citation has its verbatim supporting statement in citations.json; I checked it against the part the step actually uses, not against that node's proof.

I checked B-E against the finished files: no new self-contained-statement, duplicate, tag, leaf, or relabelling issue arises because there are no new nodes. All six proof steps are below 2000 characters. The small cases d=0 and X_0 empty preserve the formulas: the zero twist and zero shift specialize to the constant comparison, while on the empty source all source-category morphism identities are unique. For a point, the coefficient datum is canonical and the unshifted twist is trivial. The tensor-unit calculation retains the prescribed Tate datum for d>0, so there is no lost Frobenius scalar. I also traversed current statement/proof dependencies of the equivariance theorem and the auxiliary comparison lemmas: none reaches this item, hence these citations introduce no cycle. The item's statement and inherited metadata were retained.

Dry-run repair: the first preflight rejected the context-dependent phrase “the item's statement” in Step 4. Replaced it with the typed morphism beta:PF ≅ FQ; the argument and statement are unchanged.
