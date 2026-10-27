# Stage-1 delivery: lem-sfb-polarization-calculus-over-field

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-polarization-calculus-over-field.json: split, with ten complete assembly steps; statement unchanged. No Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-abelian-poincare-biduality.json: new statement-only prerequisite, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-ample-line-polarization-isogeny.json: new statement-only prerequisite, unsplit; no Mathlib match.
- citations.json: 28 verbatim quotations, one for every cited node in every step.
- searches.jsonl: actual msearch.py queries and returned digests, retained unchanged. Local scratch scripts only assemble these sandbox files; they do not replace or run project checks.

## Attachments

None. The search for the exact item tag and for polarization/polarisation, Rosati and Poincare dual abelian geometry in lean/WeilConjectures produced no complete project declaration. The existing Sheaf polarization statement concerns an algebraically closed field, has a sorry proof and omits the rational involution and symmetric kernel clauses. It is not an attachment. No Lean was written or compiled.

## WANTED

WANTED: Mumford, Abelian Varieties (1970), p.81, for the eventual proof of lem-sfb-abelian-poincare-biduality. Milne states biduality here but refers its proof to that page; Mumford is already listed as unavailable in literature/LIST.md. The new node has only a statement, and this delivery uses it explicitly as a prerequisite, rather than pretending Milne supplied its omitted proof.

## Audit and sources

Read AGENTS.md, the worker brief and role, stage 1, GOAL.md, the three blueprint levels in SETUP.md, STATE.md and delivery-errors B–E. The sandbox initially had only dispatcher markers; there was no prior proof/report/search log to overwrite. The item is an agent-created Milne auxiliary. Its blueprint ancestor is null (confirmed by blueprint_refs.py ancestor), so retain the inherited null ancestor and via chain, giving precise from.place text. Read the current latest blueprint at literature/blueprint/latest (main-20261024), especially sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its direct-images proof (3). This auxiliary does not change the current six-functor statement or its unit route; no unit or chapter file changes.

Read Milne AV I §8, printed pp.34–40, especially Proposition 8.4, Remark 8.5, the paragraph after Lemma 8.8 and the biduality discussion, and the normalized difference construction. Read §9 opening p.41, Remark 8.6 for an isogeny inverse, Lemma 10.6 p.45 for torsion-free Hom, §11 opening p.53 for polarization, and §14 opening p.61 for the Rosati formula. The assembly is marked agent-written: the normalized-family proof and the biduality calculation make its arbitrary-field content explicit. The new ample-isogeny statement cites Proposition 8.1, Proposition 8.14 and p.40 (not only the definition of polarization). Its kernel is scheme-theoretic, not just a finite set of geometric points.

No statement dispute with the item: every clause is true as stated. The initial item had no proof and no proof dependencies. Replaced none of its hypotheses, definitions or conclusions. Its earlier NS search records are retained; the N8 additions and every new-node search were actually run with msearch.py and match searches.jsonl. Semantic searches were rephrased before declaring no match. Read all returned signatures: module reflexivity and finite-character double duality are not abelian-scheme Poincare biduality; root-system polarization and affine/Weierstrass models do not give ample abelian-variety isogenies or Rosati calculus. Loogle found no Poincare/AbelianVariety/IsIsogeny declarations, and the prescribed Mathlib geometry greps gave zero hits. No service outage occurred in the N8 searches.

## Not duplicates

lem-sfb-abelian-poincare-biduality vs lem-sfb-abelian-space-poincare-calculus: the existing node constructs the relative dual, the normalized biadditive Poincare family, line homomorphisms and their pullback functoriality, but asserts no identification with the double dual. The new node supplies exactly that missing evaluation isomorphism and its naturality.

lem-sfb-abelian-poincare-biduality vs lem-sfb-abelian-polarization-calculus: the existing node has the normalized difference and pullback over an algebraically closed field, but no bidual evaluation isomorphism. This new node holds over any field and does not repeat the item's Rosati conclusion.

lem-sfb-ample-line-polarization-isogeny vs lem-sfb-abelian-polarization-calculus: the existing statement assumes algebraic closedness and states an ampleness criterion only for effective Cartier divisors. Its proof also handles arbitrary ample lines, but that proof is not its statement and cannot be cited for that stronger assertion. The new statement uses an arbitrary ample line over any field and provides the isogeny, from which the existing isogeny-inverse node gives rational invertibility.

lem-sfb-ample-line-polarization-isogeny vs lem-sfb-rosati-trace-positive: the existing node is over an algebraically closed field and gives rational inverse/Rosati/trace results. It cannot supply an arbitrary-field isogeny with finite scheme-theoretic kernel, and it is not used here.

lem-sfb-ample-line-polarization-isogeny vs lem-sfb-ample-translation-difference-surjectivity: the existing statement concerns realization of homogeneous line classes over an algebraically closed field, not a scheme-theoretic isogeny over arbitrary k.

Whole-DAG searches included titles and statements for dual abelian varieties, Poincare families, biduality, ample isogenies, torsion-free Hom and rational injection. Blueprint searches polarization, dual abelian and ample isogeny returned zero; bidual returned Verdier/module results, none about abelian-variety evaluation. The existing finite-free Hom and isogeny quasi-inverse nodes were reused, not recreated. No Stacks tag is introduced by either new node: these are Milne results, not claims that a Stacks definition proves a duality theorem.

## Review by N8

I checked the actual source and cited statements, not just dependency names. In step 1 the relative Poincare theorem explicitly quantifies over every locally Noetherian base and every parameter scheme; Spec k is such a base, including for imperfect k. The field-extension node supplies the geometric abelian fibres. The group-space theorem really gives a representing scheme for a locally separated, locally finite-type group space; properness gives separatedness here. The abelian-variety characterization converts the resulting proper smooth connected group scheme, and the etale invertible-module equivalence and normalized-datum definition supply the ordinary line and rigidification. Thus a definition node is not being used to assert existence.

In step 2 I expanded all four factors of the normalized difference and checked the cited tensor pullback theorem before using the datum's representing tensor law. Step 3 uses the relative Poincare node's actual equation for the pulled-back universal family, with source and target A, and the composition/tensor pullback statements; uniqueness compares rigidified families, not just geometric points. Step 4 uses the actual first-variable biadditivity formula in that node for a sum of homomorphisms. Pullback composition and classifier uniqueness prove reversal of composition. The rational extension is written on pure tensors and checked against its defining relations.

Step 5 uses the new isogeny prerequisite, not a definition of isogeny. The existing simple-isogeny-decomposition statement explicitly supplies both g lambda=[n] and lambda g=[n] over the original field; dividing g by n proves the inverse claimed here. Step 6 uses the new bidual node's switched-Poincare identity to turn transpose into swapping the two variables of the normalized difference. I checked the factors, the domain A x A and the identity-axis rigidification; uniqueness then gives lambda-dual delta=lambda without supposing L symmetric. This is the argument, not a separate restatement of the Rosati clause.

Steps 7–8 are ring algebra and the bidual node's naturality. I checked that dualizing BOTH inverse identities makes mu-dual a two-sided inverse of lambda-dual; this was made explicit during the self-review. In the double-dagger calculation the middle inverse factor is mu-dual=delta mu, and v-double-dual delta=delta v has the correct direction. The two-sided cancellations give exactly v, also on rational tensors. No Tate pairing, trace theorem or positivity is silently invoked.

Step 9 uses the existing finite-free Hom statement over any field. An integer basis proves torsion-freeness coordinate by coordinate; the rational-injection node says precisely that this torsion-free group embeds in its tensor rationalization. Step 10 then uses actual zero of phi_N to obtain a trivial normalized difference from the datum. Pullback along (1,-1) gives two copies of the constant identity fibre and the inverse lines N and [-1]*N. The constant line has a basis over k. With the item's symmetry hypothesis, this proves N tensor-square trivial over k itself. I checked the sign and both constant factors; geometric triviality alone was never used to descend an arbitrary isomorphism.

I checked B1–B10: the two new nodes have complete, self-contained statement-only content, with no proof/sketch or proof dependencies; their notation and pullback notions are introduced and cite definitions. Sources are precise Milne places, not invented Stacks tags. They are not Mathlib leaves. I checked C1–C8: every non-elementary input is a named cited statement, all 28 quotes are verbatim from those statements, and a read-only transitive check found no cited node depending back on this item. Generic off-unit scheme/module/group tools are declared in split_report.tool_uses for the maintainer to judge; no unit proof is replaced. I checked D1–D5: biduality is the missing comparison of two dual objects, not an item clause; the isogeny prerequisite is only one geometric input and does not package the rational-inverse/Rosati/kernel argument. I checked E1–E7 on k nonperfect, positive characteristic, inseparable polarization, characteristic two and the zero-dimensional abelian variety. The new nodes and the ten steps have no separability assumption; rational denominators live in Q, not in k, and n need not be invertible in k. In dimension zero the zero abelian variety is its own dual, the unique map is an isomorphism, and all lines over Spec k are trivial. No proof step exceeds 2000 characters (maximum under 1000).

## Source caution

Milne's printed Theorem 8.9 must not be used as its unrestricted equivalence of all four conditions: with B=0, A nonzero and the trivial correspondence, condition (b) is vacuously satisfied but (a) and (c) fail. This delivery uses only the standard true biduality consequence for an already universal Poincare datum, as stated in the paragraph preceding that theorem. The new node explicitly records this restriction in its source place. This is not a dispute or a weakening of the item, whose bidual/Rosati assertions are correct.

## Unfinished work

The two new prerequisites are intentionally unsplit stage-1 items, with real searches and no proofs. Nothing in the assembly proof is deferred to an unnamed fact. No Lean compilation is authorized or attempted.
