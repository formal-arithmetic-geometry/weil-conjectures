# Stage-1 delivery: lem-sbc-common-stage-inverse-through-karoubi

## Files written

- dag/nodes/sec-smooth-base-change/lem-sbc-common-stage-inverse-through-karoubi.json: statement, now split into ten steps; Mathlib searches find ingredients but no whole-item match.
- citations.json: verbatim excerpts for every node used by every proof step.
- report.md and searches.jsonl: this report and actual Q15 search log.

No new nodes; zero new Mathlib leaves. The statement and its four statement dependencies are unchanged. All inherited metadata, blueprint provenance and earlier searches are retained. There was no earlier item copy or report in this sandbox.

## Attachments

None for the item. The project has CategoryTheory.StageSystem.Morphism.isIso_descNatTrans_app at lean/WeilConjectures/CategoryTheory/StageSystem/Functor.lean:269, with a three-line proof. It states the local invertibility after pair descent only: it does not state the two Karoubi restrictions, raw inverse formula, scalar conjugations or presentation formula. Hence it is a partial ingredient, not an attachment for this item. I also read the compatible transformation and descent definitions in that file:184-265. The item tag, raw inverse and Karoubi/inverse searches under WeilConjectures did not find a declaration proving the complete item.

## WANTED

None. The needed sources and the cited node statements are present locally.

## Changes and source review

The unsplit item already states the correct local version: invertibility is required at the displayed raw object only. Its inverse must be restricted twice, and the inverse products are the projectors, not the ambient raw identities. These distinctions are retained explicitly. No statement dispute or hypothesis change was needed. No unit or chapter record is changed: sk-rem-rest is a remark without proof steps, and this item serves the ancestor's raw-inverse/common-stage argument.

I read sketch32, literature/blueprint/slopmaster2/src/version/sketch/32_smooth_base_change.tex:1291-1359 and 1412-1455, as named by the item, including the finite common-stage principle and the definitions of the coefficient categories. I also read sketch42:140-250 (representatives, transport and equality) and :800-880 (functor descent and the two universal properties). These sources describe the pair/quotient route. The proof is marked agent-written because the projector and inverse equations are supplied here, rather than falsely attributed to an external theorem.

## Source error

The current main-20261015 ancestor proof at blueprint/sec-smooth-base-change/sk-thm-sbc-coefficients/sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch.proof.md calls the coefficient passage a derived inverse limit over finite fields. That is not the pair-category coefficient construction: arrows are common-stage classes in a filtered colimit. I do not use that inference. The live ancestor's split already uses coherent pair descent and this local-inverse lemma instead. The item's statement itself needs no repair. This observation does not change any unit route; the detailed sketch32 source and live ancestor give the required route.

## Mathlib and duplication searches

I searched the project by the item's exact tag and by common-stage, raw inverse, Karoubi and inverse terminology, and searched the DAG and blueprint for raw local inverse and common-stage inverse. The existing lem-sbc-coherent-pair-functor-descent gives the full coherent quotient and transformation construction needed here; def-weil-karoubi-envelope gives the exact morphism and identity equations. Their statements were read, not merely their proofs or Lean records. The finite subextension and size statements, plus the additive-category and additive-functor definitions, were read to check the ambient hypotheses.

The Q15 msearch log contains LeanFinder with two different formulations, Loogle functorExtension₂, grep of Idempotents, and LeanSearch. All services answered. I read Mathlib/CategoryTheory/Idempotents/FunctorExtension.lean:130-225, including functorExtension₂ at line 185 and its comparison at line 193. These are ordinary Karoubi extension facts. The other returned Dold-Kan and filtered-colimit-of-morphisms results do not give this item's full common-stage quotient/local-object conclusion. The actual queries and returned declaration names are appended to mathlib_searches. No nonexistent searches are claimed. There are no new nodes requiring a Not duplicates pair list.

## Review by Q15

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the written item, the two cited statements and the sources above. There are no new statement-only nodes, no renamed clauses replacing the argument, and no use of a cited node's proof as if it were its statement. All ten proof steps are shorter than 2000 characters. The only non-elementary construction used is the existing coherent pair descent theorem in step 3; the other steps explicitly multiply projectors, apply naturality, or check inverse equations in a few lines.

Steps 1-2 use def-weil-karoubi-envelope precisely for u=due, identities e and inherited composition. I verified both absorption equations, naturality of a restricted transformation, multiplication of restricted transformations, and inverse restriction. This makes the unit/tower/pentagon equations survive restriction because extension preserves composition and whiskering; in a unit case the identity is the projector. The explicit direct sum construction shows additivity needed for pair descent. No raw idempotent completeness is needed.

Step 3 uses the coherent descent statement's additive categories, functor and transformation constructions and its last displayed outer-restriction formula. The small directed index, normalized associators, unit and tower equations and transformation compatibility are exactly the item hypotheses, with their extensions checked in steps 1-2. It does not use its general-isomorphism version or assume all components invertible.

Step 4 uses the Karoubi morphism equation and calculates da=ae, vd=ev, wc=e and cw=d. Step 5 uses the descent statement's common-stage composition prescription to pass those actual equations into the quotient, with identities [E,e] and [E,d]. Step 6 uses its naturality clause for an arbitrary pair-category idempotent q, not a presumed stagewise q. It derives kg=fk from kh=1,hk=1 and gh=hf, then verifies the outer absorption and both products. This does not assume that q lifts to an idempotent at E or that the inverse extends globally.

Step 7 uses only the given comparison equation and functoriality, writes a_M=cV(a)b⁻¹, and checks both products of v_M explicitly. Step 8 uses the cited representative-equivalence formula, whose endpoint associators a^B_(M,E,E) are identity unit cases. The conjugated arrows are V(a) and V(v), so the class independence really holds in the fixed endpoint Hom set. I checked domains at every occurrence of b and c. Step 9 proves uniqueness of the raw inverse by v'=v'av=v. Step 10 uses the descent theorem's outer naturality and checks both products after conjugation by t; all inverse symbols on functor images of t exist because functors preserve its given two inverse equations.

Small cases checked: p=0 gives c=w=0 and identities 0 in the inner zero summand; p=1 recovers a,v; q=0 gives the outer identities 0; q=1 recovers the pair inverse; M=E gives b=c=1 and the original representatives; t=1 gives the original component. For a concrete nonidentity test, take the additive category of finite-dimensional rational representations of Q[t,t⁻¹], let F=G be the forgetful functor to rational vector spaces and let η be multiplication by t. On the representation A with t=diag(2,3), take p=diag(1,0): restricted products are p. The same calculation on a two-dimensional block with equal eigenvalues permits a non-diagonal idempotent q and still gives q as each product. These checks expose why raw ambient identity equations cannot be substituted for Karoubi identities.

The first dry run rejected the phrase “the item's” in step 10 under its standalone-statement wording check. I replaced that phrase by the explicit conjugation equation. No corrections to the statement were needed. The substantive addition is the explicit algebra that the source leaves implicit. No tools, repository files, Lean source or compilation artifacts were written.

## Unfinished work

None for this one-level split. The existing descent dependency keeps its own independent proof/Lean obligations; this delivery uses its complete natural-language statement.
