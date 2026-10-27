# Worker report

## Files written

- dag/nodes/sec-six-functors/lem-coef-finite-site-hom-transport.json: statement item, split into six argument steps; no Mathlib match.
- citations.json: thirteen verbatim statement excerpts, one for every proof-step citation.
- report.md: this report and direct-delivery review.

New nodes: 0. Mathlib leaves: 0. No unit file changes: the item is not the unit's key statement.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for site/Hom transport, Hom comparison and bidual comparison terminology. Existing Etale/Derived files discuss different geometric/duality comparisons and do not state all three clauses for an arbitrary compatible target family. No complete project declaration was found for attachment.

## WANTED

None. The source blueprint proof and the Stacks source used for the closed derived structure are present.

## Statement and proof audit

The item's statement is retained verbatim. The added statement dependency def-sf-evaluation-hom-site-comparison specifies the evaluation-defined comparison on arbitrary derived first arguments, as used in the transpose calculation. The imported item had no proof. Its three clauses require an actual calculation of the transported target cocycle, the target-change square, and both untransposes of the bidual equality; merely asserting that these transport would leave the substance unproved.

I read the chapter record sec-six-functors, unit sk-prop-sf-biduality-general, and the source cor-coef-finite-verdier.proof.md in main-20261015. The relevant source sentences are the two comparison/evaluation sentence, transposition of evaluation, and the quotient cocycle. This is a formal finite-coefficient comparison argument; no exceptional adjoint is constructed, and no SGA route is used. The chapter's historical references are not proof citations in this delivery.

Before considering new nodes I searched the DAG for quotient cocycle, target-family/site transport, evaluation and bidual comparison, and ran tools/blueprint_refs.py search for Hom comparison, evaluation, coefficient-compatible, double-dual and site comparison. Existing lem-coef-finite-hom-site-descent supplies the underlying square and coherence, so no duplicate lemma is created. Existing lem-sf-evaluation-bidual-comparison-transport assumes that duality preserves a chosen subcategory and that the site functor restricts to an equivalence. Those extra assumptions are unnecessary for an arbitrary target here; the proof instead writes the two transposes out using the ambient closed adjunction. The existing scalar-only lem-coef-finite-bidual-transpose has a different functor and is not silently applied to a site change.

Mathlib searches were run with the required msearch command, and their results are in searches.jsonl. I retained the item's inherited searches and appended exactly the five actual searches of this attempt: leanfinder with two phrasings, loogle for expComparison_ev, grep of CategoryTheory/Sites, and leansearch. I read Mathlib/CategoryTheory/Monoidal/Closed/Functor.lean lines 55-114: expComparison_ev at line 85 requires Cartesian monoidal categories and binary-product preservation, so it is not a specialization giving module-derived tensor transport. Other hits concern ordinary module duals, free sheaf pullback, and condensed Hom. They do not state the entire item. No search was recorded as absent when unavailable; all five returned hits.

## Not duplicates

No new nodes were created. In particular, the scalar/site square is cited from lem-coef-finite-hom-site-descent rather than duplicated. The target-change naturality and cocycle cancellation are steps, not newly named nodes.

## Review by Q05

I read the complete item and the statements of every proof dependency with the source blueprint open. For the supporting closed structure I also read sites-cohomology.tex, lemma-internal-hom (Tag 08J9) and lemma-symmetric-monoidal-derived (Tag 0FPT), including the signed-symmetry convention. The proof is marked agent-written because the source only gives terse assembly instructions; the expanded computations are not attributed as a verbatim Stacks theorem.

Step 1 uses the precise preservation and natural linear isomorphism clauses of lem-coef-finite-hom-site-descent. Its finite-field, invertible-prime, finite quotient-ring, separated finite-type and finite-Tor hypotheses match the item. No constructibility condition is inferred merely from a definition. Functors preserve the given target isomorphisms, and their composites with inverse chi are isomorphisms.

Step 2 uses the same node's unit and successive-quotient coherence. I checked the orientation: chi goes from F after etale scalar extension to pro-etale scalar extension after F. Its inverse therefore occurs in u^p. The displayed naturality equation moves precisely this inverse past S^p(F(u)); substituting the original target cocycle then gives u^p_{i,r}. Scalar associators and units are explicitly the canonical identifications already authorized by the statement. This argument works for repeated indices, not just strict quotient chains.

Step 3 cites def-sf-evaluation-hom-site-comparison for its actual definition as an evaluation transpose and lem-sf-ringed-derived-closed-symmetric-monoidal for the natural adjunction and its counit. The few-line argument untransposes both sides to F(u) after pulled-back evaluation, so the naturality used here is proved rather than smuggled into a definition citation. Both second arguments are ordinary derived objects and the definition imposes no Tor or invertibility condition. This is the sole step marked elementary.

Step 4 uses the literal scalar/site square of lem-coef-finite-hom-site-descent, not material in its proof. I checked its common source and the contravariant first variable. Postcomposition by H(chi_K,u^p) cancels chi_K^{-1} in that variable, while u^p chi_Omega is exactly F(u). Bifunctoriality is explicitly provided by def-pur-derived-internal-hom. Step 3 then gives the desired left side. The item has K and Omega_i finite-Tor constructible; step 1 places their pullbacks in the same pro-etale category, satisfying thm-coef-finite-hom on both sites. The argument does not assume quotient flatness.

Step 5 checks evaluation for T and for its first dual Q. The defining evaluation transpose applies to all ambient derived objects. For the site-descent lemma's finite-Tor clauses, the identity-quotient case A=B of thm-coef-finite-hom explicitly places H(T,Omega_j) tensor A_j in D^b_ctf; the scalar unit identifies it with Q. Thus the proof does not assume unproved preservation of D^b_ctf by duality for arbitrary targets. The relevant theorem's statement says its Hom comparison is an isomorphism in D^b_ctf, which is the exact fact used. This is not a biduality-isomorphism assertion.

Step 6 uses the ambient natural closed adjunction of lem-sf-ringed-derived-closed-symmetric-monoidal and the evaluation/transpose-preservation clause of lem-coef-finite-hom-site-descent. I checked both untransposes have domain FT tensor FQ and codomain F(Omega_j). The first uses evaluation at Q and the definition of delta_T; the second uses naturality of evaluation in its first variable, followed by evaluation at T. Both become F(ev_T) after the symmetry on FT tensor FQ. The cited comparison explicitly preserves transposes; the underlying derived symmetry is signed, so shifting either factor does not lose the Koszul sign. Injectivity of the adjunction bijection proves equality without asserting invertibility of delta or invoking an ambient pro-etale exceptional adjoint.

I tested the statement on N=1 and i=j (the coefficient comparison and cocycle reduce to scalar units), on a three-index chain with repeated indices, and on the zero target/zero argument and empty scheme (all displayed equations become the unique zero maps). For X a geometric point and degree-zero finite free modules the square reduces to substitution into an ordinary Hom map and the final identity evaluates a functional on a vector. Shifting a factor checks that the symmetry occurs on both untransposes with the same sign. None of these cases requires the targets to be dualizing or quotient maps to be flat.

Against delivery-errors B-E: no new statement-only leaf needs a source or hypothesis repair; no new node duplicates an existing lemma or a clause of the item; every non-elementary input is a cited statement whose relevant sentence was read and quoted in citations.json; the actual transported maps, inverse orientations, target changes, scalar units and symmetry are written out. All six proof steps are below 2000 characters. No hidden sublemma is parked inside a long step. The only off-unit tool declared in split_report.tool_uses is the generic closed derived tensor structure, which provides the adjunction and symmetry without changing the unit's geometric route.

## Unfinished work

None in the stage-1 split. The existing dependencies retain their own current statuses; this delivery makes no claim to prove them or to supply Lean code.

## Validation repairs

The first dry run rejected the finite-Hom excerpts as shorter than 40 characters. I expanded both to the full quantified comparison formula and its D^b_ctf conclusion, preserving verbatim statement text. No proof or statement changed for this citation-format repair.

## Repair of returned delivery 986ca407e81

The 2026-10-22 09:57 UTC return names one defect: landing detected that the statement of lem-coef-finite-hom-site-descent had changed since the reviewed delivery. I retained the returned sandbox's six-step argument, citations and five logged Mathlib searches. I compared its item with the current shared DAG: the live item remains unsplit, has no reviewed record or released repair note, and its statement, source and blueprint provenance agree with the retained item. The delivery tool rebases the retained split onto the current DAG; the initial mandatory dry run exited successfully at 32d01075f8e before these repairs.

I reopened the full current statement of lem-coef-finite-hom-site-descent, whose reviewed record is by NT-cc-Q133-b16e4e447 (Q133). It is stated for n >= m >= 1 and the finite quotients of the fixed valuation ring, on separated finite-type schemes over the fixed field. Its constructibility/Tor conventions explicitly include def-kun-tor-amplitude for the etale site and def-weil-finite-tor-amplitude for the pro-etale site. Our item defines its Tor interval directly against all degree-zero module sheaves on both sites, so the meanings agree. The current statement supplies preservation of every Tor interval, the natural B-linear h, its monoidal and successive-quotient coherence, the evaluation-defined Hom square, and transport of evaluation and transposes on finite-Tor constructible pairs. It expressly neither assumes nor concludes invertibility of the quotient Hom maps v. I checked these claims in its statement, without using the newly expanded proof as an additional interface.

The proof now spells out the applications to that interface. Step 1 uses n=m=j for preservation and n=i, m=j for chi; its hypotheses are checked explicitly. Step 2 uses A=A_i, B=A_j, C=A_r, retaining the inverse-chi naturality calculation and the transported cocycle. Step 4 substitutes (K,M)=(K,Omega_i), identifies the current h with our chi, and states explicitly that the square itself needs no v invertibility. Its existing postcomposition calculation has exactly the required contravariant chi_K inverse and covariant chi_Omega. Step 5 now states that n=m=j gives evaluation/transpose transport for both (T,W) and (Q,W); Q's finite-Tor constructibility is provided separately by thm-coef-finite-hom with the identity quotient. Thus the revised statement's restricted finite-Tor domain is respected even for the first dual. Step 6 keeps both explicit untranspose calculations, whose common target is F(W), and uses only that revalidated evaluation/transpose clause.

I also reread the current statements of the other four proof dependencies: def-sf-evaluation-hom-site-comparison defines the comparison for arbitrary derived objects by the evaluation transpose; lem-sf-ringed-derived-closed-symmetric-monoidal supplies the natural closed adjunction, evaluation counit and signed natural symmetry; def-pur-derived-internal-hom supplies bifunctoriality with the required variance; thm-coef-finite-hom supplies the D^b_ctf-valued comparison on either site, including n=m. Every retained quote remains a literal substring of its current cited statement. I expanded the site-descent quotes to capture the current square's domain and the no-invertibility qualification. There are still thirteen citation entries, one for each proof-step citation.

I reread the item's main-20261015 cor-coef-finite-verdier proof and the supporting Stacks lemmas 08J9 and 0FPT in sites-cohomology.tex. No source, statement, proof route, new node or Mathlib verdict is changed by this repair. The recorded Mathlib search questions have not changed; I read their retained results instead of repeating the queries. A renewed whole-project Lean search by the exact item id and site/Hom/bidual transport terminology found no complete attachment.

Repair self-review by Q05: the preservation, quotient coherence and typed square are still literally provided by the current site-descent statement (C4); the additional Hom closure fact is still separately cited (C1). There is no appeal to an implicit exceptional adjoint, flatness of A_i to A_j, or dualizing property of an arbitrary target. The repeated-index cases n=m=j and i=j=r are expressly allowed by the current hypotheses. Empty X and zero targets/arguments still give the unique maps, and a shifted finite free argument uses the same signed symmetry on both untransposes. All six steps remain below 2000 characters, with no new hidden lemma or duplicate. The final dry run and push are performed only after this updated proof and citation audit.
