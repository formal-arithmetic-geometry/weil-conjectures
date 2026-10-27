## Files written

- dag/nodes/sec-trace-formula/lem-trf-affinoid-distinguished-presentation.json: statement, split; no Mathlib match. Statement and original source preserved.
- dag/nodes/sec-trace-formula/lem-trf-affinoid-spectral-banach-norm.json: statement-only, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-affinoid-canonical-reduction-finite-type.json: statement-only, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-tate-reduction-norm-lifting.json: statement-only, unsplit; no Mathlib match.
- citations.json: a verbatim full-statement quotation for every proof citation.
- searches.jsonl: actual msearch records for this delivery. write_split.py is sandbox-local preparation code, not a delivery node.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint id and by affinoid, TateAlgebra, distinguished presentation, spectral norm, and canonical reduction. There is no declaration proving this item. Sheaf/RingTheory/GrauertRemmertPowerbounded.lean only cites this item in its docstring and proves a different finiteness statement, with a postponed proof. Existing restricted-series definitions and analytic comparison statements are not finished proofs of this theorem.

## WANTED

WANTED: Bosch–Güntzer–Remmert, Non-Archimedean Analysis, spectral Banach norm theorem 6.2.4/1, canonical reduction finiteness in sections 6.3–6.4, distinguished epimorphism/reduction criterion in sections 6.4.2–6.4.3, and norm-attainment Corollary 5.2.7/8, for this item and the three new analytic nodes. This book is absent locally. The precise numbering of the specified-map reduction criterion has not been verified, and no invented theorem number is supplied for it.

WANTED: local archival copy of Brian Conrad, Several approaches to non-archimedean geometry, Theorem 1.2.6(1),(5) and Exercise 1.2.8(3), PDF pp.6–7. Read the original PDF online at https://math.stanford.edu/~conrad/papers/aws.pdf on 2026-10-24. It explicitly gives the complete supremum norm on a reduced affinoid, equivalence of Banach norms, power-boundedness characterization, and substitution universal property.

WANTED: local archival copy of Rita Rodríguez Vázquez, Non-Archimedean normal families, section 2.2, printed pp.1685–1686; read https://www.numdam.org/item/10.5802/aif.3432.pdf online on 2026-10-24. It states distinguished-presentation existence over an algebraically closed field and explicitly uses attained norm-preserving lifts. This is confirmation, not a substitute for splitting the theorem.

WANTED: local archival copy of Laurent Fargues, Groupes analytiques rigides p-divisibles, section 1.7.1, printed p.18; read https://webusers.imj-prg.fr/~laurent.fargues/Groupesanalytiques.pdf online on 2026-10-24. Its paragraph defining canonical reduction confirms finite generation and its next paragraph identifies the Tate quotient unit ball with the image of the integral Tate algebra, citing BGR 5.2.7/8. The paper is p-adic; it is not being silently applied in positive characteristic. The arbitrary-characteristic new statements are the standard BGR analytic inputs, left unsplit and explicitly WANTED.

## Errors and repairs

No STATEMENT-DISPUTED finding: the item's original statement is correct with nonzero, reduced, strict affinoid and algebraically closed complete nontrivially valued hypotheses. It was an empty proof. A proof that simply renames the distinguished-presentation theorem would not split it. I instead construct a map: retain the original quotient generators, adjoin lifts of generators of the canonical reduction, and verify reduction-surjectivity for that very map. The three new nodes do not state existence of the presentation: they concern an intrinsic norm, a finite-type residue algebra, and a conditional lifting result for an already specified surjective map.

Two potential gaps were ruled out in the construction. First, a quotient norm is an infimum, so equality of norms cannot on its own justify an attained unit-ball lift; norm attainment is included explicitly in the specified-map lifting node. Second, scaling original Tate generators could destroy restricted-series surjectivity. The proof retains them unchanged; their original quotient norms are already at most one. The inclusion on the first block of variables identifies the old presentation with the restriction of the new map, by uniqueness in the existing substitution theorem.

The current blueprint was read from literature/blueprint/latest (2026-10-24 snapshot ef6f9619fdbffa59e88528fb56483d76c70258c8), including lem-trf-local-term-locality.proof.md. Its route is contracting correspondences; the affinoid node is a historical supporting input in the already-existing normalization chain. The split neither changes the unit nor substitutes an analytic route for its current proof. The existing blueprint from.place and via history is retained and extended for the new nodes. No SGA source is used.

## Not duplicates

The whole DAG, imported blueprint, current blueprint and project source were searched by affinoid, Tate, spectral norm, maximum modulus, canonical reduction, stable field, and the BGR places. blueprint_refs.py ancestor identifies lem-trf-local-term-locality; searches for affinoid and spectral norm found no blueprint statement matching the analytic inputs. Broad searches for canonical reduction/spectral returned coefficient-reduction and spectral-sequence nodes, whose statements concern different objects.

- lem-trf-affinoid-spectral-banach-norm vs lem-trf-spectral-norm-algebraic-extension: the existing Mathlib leaf extends a norm to an algebraic FIELD extension via minimal polynomials; the new result is completeness and norm comparison on an arbitrary reduced strict affinoid algebra, including positive dimension and zero divisors.
- lem-trf-affinoid-spectral-banach-norm vs lem-trf-restricted-series-gauss-completion: that existing statement gives the Gauss norm and completeness only on a Tate algebra itself; it does not give the spectral norm or its equivalence on a reduced quotient.
- lem-trf-affinoid-canonical-reduction-finite-type vs def-trf-restricted-series-presentation: the latter defines restricted series, quotient norms and topological generation of bounded models; it does not assert finite generation of the spectral reduction.
- lem-trf-affinoid-canonical-reduction-finite-type vs lem-trf-valuation-grauert-remmert-powerbounded: the existing node is module finiteness over a GIVEN integral model; it depends on this item, so invoking it here would also be circular. The new node is residue-algebra finite type and needs no such model.
- lem-trf-tate-reduction-norm-lifting vs lem-trf-affinoid-distinguished-presentation: the new node assumes an already specified continuous surjective contractive map and surjectivity of its canonical reduction. It constructs no generating set or epimorphism. The item's steps construct and verify those inputs.
- lem-trf-tate-reduction-norm-lifting vs lem-trf-affinoid-powerbounded-integral: the existing statement only supplies a monic equation for each bounded element, relative to an arbitrary presentation; it supplies no norm-preserving lift and does not require the same field/reducedness hypotheses.
- Each new node vs lem-per-tate-banach-substitution: the latter is the generic convergent substitution theorem for bounded coordinates; it gives neither spectral Banach completeness, reduction finite type, nor exact norm lifting. It is reused directly, with a declared generic tool use because its unit differs.

No new statement uses a Stacks theorem or tag. These analytic results are from BGR/Conrad, and assigning an unrelated Stacks tag would misidentify their source.

## Review by Q104

I read the B–E delivery-error checklist in full. For the item I read its source description, its parent Grauert–Remmert statement and proof dependencies, the chapter and unit records, the latest locality blueprint proof, and the original Rodríguez Vázquez PDF section 2.2 online. The BGR book itself is not present; I have not claimed to read it. The assembly is therefore explicitly marked proof_origin.by=agent, and the analytic inputs remain separately stated unsplit nodes. I read Conrad's Theorem 1.2.6 and Exercise 1.2.8, and Fargues's section 1.7.1 to cross-check the meanings and restrictions of those inputs.

For new lem-trf-affinoid-spectral-banach-norm, Conrad 1.2.6(1),(5), PDF pp.6–7, gives exactly the complete supremum norm, power multiplicativity and bounded equivalence used. A reduced nonzero quotient is essential: nilpotents would have zero spectral norm; a zero algebra cannot satisfy rho(1)=1. Algebraic closedness allows the character formula to use K-valued characters. The lower comparison rho<=quotient norm follows from evaluations, and equivalence gives the upper bound. General Mathlib spectralNorm instead assumes a field algebraic over K, as checked directly at SpectralNorm.lean lines 629–679. SmoothingSeminorm's abstract power-multiplicative smoothing does not establish reduced-affinoid completeness or equivalence.

For new lem-trf-affinoid-canonical-reduction-finite-type, I read Fargues section 1.7.1's exact paragraph defining A-tilde and the finite-type assertion, and distinguished that paragraph's BGR input from Fargues's p-adic conventions. The node states its field, restricted quotient, spectral function, valuation residue field, closed unit ball and strict-small ideal explicitly. It says ordinary finite polynomial generation of the quotient, not topological generation of the integral ball; those are distinct and converting them is precisely the non-elementary next input. General residue-field finiteness and quasi-finite algebra results from searches do not prove this finite-type spectral reduction theorem.

For new lem-trf-tate-reduction-norm-lifting, I checked the specified-map reduction criterion against the BGR route and the norm-preserving-lift conclusion explicitly used in Rodríguez Vázquez Proposition 2.2's proof. It is formulated conditionally on a continuous surjective contractive map and surjective canonical reduction, under algebraically closed complete nontrivial valuation and reduced nonzero quotient hypotheses. It does not conflate reduction-surjectivity with unconditional existence of a presentation. Exact norm attainment is explicit, not inferred just from an infimum. Its precise BGR proof/number is WANTED and its proof is postponed as required for a new node.

Step 1 cites only the full spectral Banach norm statement. It supplies completeness, power multiplicativity and both norm bounds. The identification of bounded powers with rho<=1 is written out in both directions, with the power zero included. Nothing about the proof of that cited node is used.

Step 2 cites only the finite-generation statement for the canonical reduction, exactly for the finite list b_j that its statement promises. Its other inequality uses the definition of the original quotient norm and step 1. It makes no spherical completeness, discrete valuation or characteristic-zero assumption.

Step 3 cites lem-per-tate-banach-substitution and lem-trf-restricted-series-gauss-completion. I opened and read both complete statements. The first really gives convergent substitution, the continuous algebra map, uniqueness and contractivity for a finite tuple in the closed unit ball of a complete algebra. Step 1 checks every algebra norm axiom in that hypothesis and step 2 checks each coordinate bound. The second really gives coefficient realization, isometric regrouping, finite truncation density and completeness of Tate rings, justifying the isometric first-variable-block inclusion; it is not cited for any assertion about a quotient. Uniqueness proves q restricted to the first block equals q_0, so the original surjectivity is retained. The off-unit substitution lemma is a generic tool, recorded in split_report.tool_uses.

Step 4 cites the exact statement of the new norm-lifting node. All its hypotheses are checked in the step: base K, reduced C!=0, the specified q's continuity/surjectivity/contractivity from step 3, and reduction surjectivity from the b_j generation in step 2. Coefficients lie in V exactly when the Gauss norm is <=1. Contractivity and step 1 prove the reverse inclusion, so equality of the image and C^circ, not merely surjectivity onto a larger ring, is proved.

I tested K itself (zero original variables), a Tate polynomial disc (Gauss norm and polynomial reduction), and K x K (idempotents, zero divisors but reduced). The finite reduction list may be empty; s=r+t is permitted to be zero. The actual assembly works in all of these cases. The zero quotient is deliberately excluded by the original item; nonreduced quotients are excluded by the spectral norm input. A complete algebraically closed rank-one field can have a dense value group and need not be spherically complete; no convergent-digit argument assuming a smallest positive valuation is used. Ramified finite field extensions over a non-algebraically-closed base show why the base-field hypothesis in the lifting result must not be silently dropped.

Every new file has only a statement, no proof steps, no proof dependencies and no proof sketch embedded in the statement. None of the four non-elementary assembly steps exceeds 2000 characters. citations.json quotes the full exact statement of each cited node, retaining its hypotheses. Every recorded new-node Mathlib query was actually run via msearch.py; two semantic phrasings, Loogle and grep are recorded and the hits were read. No source was downloaded, no Lean was written, no compiler or Lake was invoked, and no repository git operation was run.

## Unfinished work

No requested assembly work remains. The three analytic lemmas intentionally remain unsplit for future workers. Their source archival requests and the unverified exact BGR reduction-criterion numbering are explicitly recorded above; this delivery does not present those postponed statements as proved.

## Validation

The mandatory server dry run exited 0 and printed OK (not pushed) at 736f797723d: preflight passed. The server ran its delivery preflight, including check_dag.py and review_split.py; the delivery citation/search checks passed. This final report records that result. Direct push follows a final dry run of this report-bearing package.
