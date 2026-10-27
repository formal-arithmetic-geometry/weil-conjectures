# Stage-1 delivery: lem-trf-degree-zero-derived-bidual-model

## Files written

- dag/nodes/sec-trace-formula/lem-trf-degree-zero-derived-bidual-model.json: existing statement split into six steps. No statement or statement-dependency changes. Retained all original source, blueprint and Mathlib-search records; appended the five searches actually logged for Q11.
- citations.json: fourteen step/node entries, each quoting the cited statement verbatim.
- report.md: this report.

New nodes: 0. Mathlib leaves: 0. All non-elementary tools already exist. Each proof step is below 1000 characters.

## Attachments

None. Searched the live WeilConjectures source for the exact blueprint tag, degree-zero bidual keywords and bidual declarations. PresheafOfModules.bidual and SheafOfModules.bidual describe underived sheaf objects; the derived perfect-dual files impose perfectness. None states this arbitrary-module K-injective comparison with all its clauses.

## WANTED

None. All sources used are present locally.

## Audit findings

The imported item had no proof. Its statement is correct, including its apparently unsigned post-exchange formula: for a homogeneous x outside degree zero, r(x)=0, so both signed and unsigned evaluations vanish. In degree zero the sign is 1. This is not a sign cancellation for arbitrary complexes or an assumption that F is concentrated in degree zero. No source or statement correction is necessary.

Read the Trace Formula chapter and sk-i-curve-zero unit, and the current main-20261015 file for lem-trf-local-term-locality. That blueprint file states the contracting-local-term theorem rather than this algebraic lemma. The inherited creation chain locates the present item inside its nearby-cycle/algebraic-shriek tool branch. This split establishes that local algebraic tool and does not replace a chapter or unit argument. The same_as field remains empty: searches of the blueprint and DAG locate biduality for perfect objects and signed ordinary Hom models, not this exact arbitrary-module resolution assertion. Existing general tools are cited instead of duplicated.

The existing lem-trf-derived-evaluation-resolved-model treats a more general iterated evaluation operation, not exactly the degree-zero bidual map requested here; the existing signed-bidual-localization result uses ordinary Hom into P[0] and extra comparison quasi-isomorphisms, which need not hold for arbitrary M. Neither can simply be substituted for the present item. The normalized general chain-transpose theorem is the appropriate smaller tool.

Mathlib searches used the prescribed msearch command: LeanFinder twice with different formulations, Loogle, LeanSearch and grep. All five succeeded. The semantic hits are Ext-class representatives or underived evaluation. Read Module.Dual.eval in Mathlib/LinearAlgebra/Dual/Defs.lean:80 and ModuleCat.ihom_ev_app in Mathlib/Algebra/Category/ModuleCat/Monoidal/Closed.lean:71. They do not identify unbounded derived tensor/Hom models. Retained the older searches and their unavailable LeanSearch verdict accurately; the new LeanSearch call succeeded. searches.jsonl records the new calls.

## Review by Q11

I read sites-cohomology.tex Tags 0A90 (lemma-compose), 0A95 (lemma-RHom-well-defined), 0A96 (lemma-RHom-from-K-flat-into-K-injective), and 0A97 (lemma-internal-hom-evaluate), including their proofs. I also read dualizing.tex Tag 0BZW (lemma-relative-dualizing-algebraic), proof (1)(c), which motivates the scalar biduality application but whose Noetherian and perfect hypotheses are not used to prove this general model lemma. The explicit sign calculation and final transposition argument are supplied here, so proof_origin is agent. No SGA source is used.

For step 1 I opened def-sc-module-total-hom-complex, def-pur-hom-complex and def-pur-derived-internal-hom. Their product terms and differentials coincide on the one-object site; the last statement expressly computes derived Hom using any K-injective target and any representative of its first variable. Thus both identifications are in the derived category, without assuming V is K-injective. The site is small and module sheaves really are modules, so the stated site hypotheses hold.

For step 2 the module-Hom definition supplies exactly d(f)=d_target f-(-1)^deg(f) f d_source. I computed d(delta(m)) on each product component h, with delta of degree zero and d_M=0. The two terms cancel. Linearity and the zero maps in the other source degrees give an actual chain map. This is elementary from that definition, not an unproved biduality theorem.

For step 3 I opened lem-pc-kflat-resolution, lem-pur-rhom-well-defined and lem-pur-hom-kflat-into-kinjective. The resolution theorem expressly gives flat terms as well as K-flatness and a quasi-isomorphism, so it supplies both F and T. The resolution-independence statement permits an arbitrary source quasi-isomorphism and a quasi-isomorphism between K-injective targets: its target map is 1_I, so it applies separately to r and t. The Hom theorem requires K-flat source and K-injective target, which hold separately for F,I and T,I. It proves precisely the two K-injectivity assertions requested.

For step 4 I opened lem-sfb-hom-kflat-chain-transpose. Its statement permits arbitrary A, flat-term K-flat P, K-injective E, and states both the formula a tensor p maps to f(a)(p) and compatibility with inversion of representative quasi-isomorphisms. Substituting V,F,I,r* therefore gives coefficient evaluation, and precomposing with t gives the required formula. The resolution-independence node ensures r* is the canonical comparison, rather than a merely abstract isomorphism with the same endpoints.

For step 5 I applied that same transpose statement to M[0],T,I,t*delta; here M need not be flat because only T occupies the K-flat slot. Its explicit Koszul clause and the direct-sum tensor definition justify checking all homogeneous summands. I checked separately p=0 and p nonzero rather than omitting the sign. This proves equality of actual chain maps on F tensor T.

For step 6 I opened lem-sfb-ringed-site-duality-maps and used only its general characterization of b_A as braided coefficient-evaluation transpose. I did not use its more restrictive ordinary-representative normalization. The normalized chain-transpose theorem gives naturality and quasi-isomorphism compatibility; the derived-Hom definition gives contravariant functoriality and identifies the t* comparison. Thus transposition is applied to the same source and target, followed by cancellation of the actual isomorphisms Qr and Qt-induced Qs. No claim is inferred merely from equality on cohomology.

I checked B1--B10: no new-node sketches, missing notions, ambiguous objects, or alleged Mathlib leaves; source labels/tags and blueprint provenance retained; exact Lean attachment not found. I checked C1--C8 against every cited statement, recorded the necessary off-unit tools in split_report.tool_uses, and wrote verbatim citations. I checked D1--D5: no relabelled clauses or outsourced entire proof; the argument remains in the six item steps. I checked E1--E7 against the actual hypotheses and maps. In particular no boundedness of I or V, no perfectness of M, and no underived Hom(P[0],-) acyclicity is smuggled in.

Small cases checked directly: M=0 gives zero evaluation; P a field and I=P[0] gives ordinary evaluation, including infinite-dimensional M where invertibility is not asserted; P=Z and M=Z/2 is permitted because the target is resolved, so no invalid replacement of RHom by Hom(M,Z) occurs. Nonzero positive and negative degrees of F both map to zero under r, verifying the sign argument even for unbounded models. There are no new statements needing separate edge-case checks, and no proof step exceeds the 2000-character long-step threshold.

## Repair of returned delivery (2026-10-23)

The return names head `191cd353a09` and says the reader approved the mathematics but landing refused a side completion that had not been promoted into the live DAG. I retained that sandbox split, report, citations and five logged searches. I compared its node with the current shared repository: the current item has the same statement and statement dependencies, but no proof and status unsplit. The retained six-step proof is therefore still required. The first required dry run completed successfully at `4e16f51f1a0`; it rebuilt the delivery on freshly fetched origin/sheaf-dag rather than reusing the returned commit. Promotion is the maintainer's operation; this delivery supplies the reviewed split again against the current baseline.

I reread every currently cited statement, rather than relying on the previous approval. In steps 1--2 the total-Hom and derived-Hom definitions still give the product differential and computation with arbitrary K-injective targets. In step 3 the current K-flat resolution statement still supplies flat terms, the resolution-independence statement still allows arbitrary source quasi-isomorphisms with target map identity on I, and the Hom theorem still has precisely K-flat source/K-injective target hypotheses. In steps 4--5 the current normalized chain-transpose statement still allows arbitrary A, requires flat terms only of its K-flat P, and explicitly supplies naturality, representative inversion and the Koszul sign. In step 6 the current duality-maps statement still defines general biduality as exchanged coefficient-evaluation transpose, independently of its more restrictive ordinary-Hom normalization. The tensor definition still uses direct sums. All fourteen retained citation quotes remain verbatim parts of these current statements, so no citation or dependency needs replacement.

I adjusted step 6 to name the target comparison kappa explicitly as precomposition by Qt, identify it with Q(t*) using resolution independence, and write the equality of transposes and the two cancellations. This makes the rechecked comparison visible in the proof instead of merely re-pushing unchanged content. The source statement, hypotheses, proof route, blueprint metadata, original citations and search results are retained. I reread Stacks 0A90, 0A95, 0A96 and 0A97 and the motivating 0BZW(1)(c); no stronger hypothesis from 0BZW is imported. The small-case and B--E reviews above still apply. No new node, Mathlib leaf or long proof step was introduced. The final dry run and push use the delivery tool's current-origin overlay, preserving maintainer-owned fields.

## Not duplicates

No new nodes were created. Existing general resolution and transpose statements are reused explicitly.

## Unfinished work

None in this stage-1 split. No Lean was written and no compiler, Lake or build command was run.
