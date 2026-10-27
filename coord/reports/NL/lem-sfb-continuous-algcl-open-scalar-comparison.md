# Repair of lem-sfb-continuous-algcl-open-scalar-comparison (NL)

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-continuous-algcl-open-scalar-comparison.json: statement unchanged; three-step assembly, 1997 proof-text characters.
- dag/nodes/sec-six-functors-basics/lem-sfb-derived-scalar-mate-thick-locus.json: new statement-only lemma, status unsplit; projection normalization, restricted connecting-map compatibility, and thick closure. No Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-derived-scalar-mate-composition.json: new statement-only lemma, status unsplit; K-flat normalization of the actual counit mate and its geometric composition/square identity. No Mathlib match.
- citations.json: eight step/node entries, each quoting the cited statement verbatim, including its hypotheses.

All modifications are in the assigned sandbox. No Lean was written, no compiler or Lake was run, and no git command was run by this worker. The sandbox initially contained only dispatcher marker files, not a node, report or searches.jsonl. I copied the current live item, retained its metadata and prior Mathlib records, read the ND report in coord/reports/ND, and retained that report as prior-report.md in the sandbox. The current live proof has precisely the returned step lengths 937, 659, 656, 1424, 795 (4471 in total), so it is the returned argument to repair. The original node is also preserved as original-item.json. The delivery tool rebases the owned split fields on current server main and preserves all maintainer fields.

## Attachments

None. Searches in lean/WeilConjectures for the exact blueprint tag, continuousAlgCl, continuous_algcl, scalarComparison, scalar_comparison, scalar mates and comparisons found no declaration proving the item. I read lean/Sheaf/Paper/ContinuousAlgClOpenScalarComparison.lean: continuousAlgClOpenScalarComparison_isIso still has `sorry`. The resolution-open scalar comparison in WeilConjectures is about resolution/section cohomology, not the all-continuous coefficient mate here. Existing general pullback and mate lemmas are used rather than treated as a proof of this item.

## Wanted sources and retained source limitations

The route is the current main-20261015 direct-images proof paragraph (3); that proof is agent-written and the all-continuous comparison is a separate obligation below it. I read that proof, the scalar-six pullback proof, the chapter record, the unit record, the retained item's complete proof and every statement it cites. The new nodes are explicit extractions of its formal subarguments, not alleged quotations of a source theorem. Their source.place identifies the returned steps and the blueprint paragraph precisely; proof_origin is null because their proofs are deliberately deferred.

For the thick-locus extraction I read Stacks sites-cohomology.tex, Tag 0B56 (equation-projection-formula-map), which defines the projection morphism using the counit, and Tag 07A6 (lemma-adjoint). For the composition extraction I read Tags 0D6D (lemma-derived-pullback-composition), 07A4 (lemma-pullback-tensor-product), 07A6 (lemma-adjoint) and 0D6E (lemma-derived-pushforward-composition). I checked these tags against literature/stacks-project/tags/tags. These are supporting constructions, not an assertion that Stacks already packages either extracted result. The actual normalized coherence and connecting-map tools are the existing DAG statements named in the retained argument below.

WANTED: an exact reference for the finite-E tame-pair proper-image finite thick-generation input. The retained ND report read ILO, Travaux de Gabber, IX Theorem 1.1 and XIII 2.2.2; it correctly distinguished their alteration geometry from the full agent-stated coefficient generation input. That existing node has since been split independently; this repair reuses it and does not deliver it again.

WANTED: an exact reference packaging the proper and tame-boundary all-continuous coefficient comparisons in ordinary ambient internal-module derived categories. The retained report distinguished these obligations from finite-coefficient and filtered-finite-extension results, including Bhatt–Scholze Lemma 6.8.2/Example 7.1.7 and Hemo–Richarz–Scholbach Lemma 5.3. This repair retains that scope distinction; those existing nodes are now split independently and are reused by their statements. No forbidden SGA route is used.

## Repair of the return and distribution of work

The return requests at least two comparable independent jobs and an assembly of at most 3000 characters. The new statements have 2308 and 2485 characters. They state genuinely different formal results and both have empty proof, empty proof_deps and null proof_origin. Neither asserts invertibility of the open comparison for arbitrary constructible inputs. Neither includes the geometric generation argument or the proper/tame coefficient computations.

The first job owns all of old step 1, together with the thick-closure part of old step 2, including the explicit retract inverse. The second owns all of old step 4, including the identification of lambda with theta inverse, the normalized direct-image compositors and the commuting-square equality. Those two jobs carry comparably sized portions of the original proof. The parent retains the application of the existing geometric generation theorem, old step 3 verbatim (checking the two already-cited finiteness statements), and old step 5's application/cancellation of the now stated comparison square. These remaining operations are the actual assembly, not a hidden third large argument. In particular no new node is created just for two applications of known finiteness statements or cancellation of invertible arrows. The full original proof is reproduced below so none of its arguments is lost or blurred.

## Not duplicates

lem-sfb-derived-scalar-mate-thick-locus vs lem-fix-proetale-scalar-mate-normalization: the existing result is for finite constant coefficient rings and only identifies the projection arrow. The new result permits arbitrary Cartesian sheaves of rings, including the nonconstant condensed all-continuous coefficient sheaf, and states restricted exactness with connecting arrows and thick closure.

lem-sfb-derived-scalar-mate-thick-locus vs lem-sfb-ringed-projection-first-shift: the existing node supplies exactness of a specified projection arrow, but does not identify the scalar mate after coefficient restriction or state its thick isomorphism locus. This normalization is the substantial extra work.

lem-sfb-derived-scalar-mate-thick-locus vs lem-coef-etale-hom-thick-locus: the old locus concerns a contravariant internal-Hom evaluation comparison on the etale site with constant rings; the new one concerns a covariant direct-image scalar mate on the pro-etale site with arbitrary sheaves of rings.

lem-sfb-derived-scalar-mate-thick-locus vs lem-sc-right-adjoint-tensor-locus-localizing: the old result concerns quasi-coherent derived categories, a proper morphism and its further right adjoint; it does not identify the scalar mate or cover the ordinary pro-etale module categories used here.

lem-sfb-derived-scalar-mate-composition vs lem-pur-etale-direct-image-scalar-composition: the existing node assumes finite constant commutative rings and the small etale site. The new one covers arbitrary pulled-back ring sheaves on the pro-etale site and identifies the exact K-flat geometric mate. Finite constant rings do not specialize to the coefficient ring B used by this item.

lem-sfb-derived-scalar-mate-composition vs lem-sf-scalar-pullback-composition: the old node concerns constant-ring inverse-image comparison coherence; it does not identify the geometric direct-image counit mates or their adjunction-normalized compositors.

lem-sfb-derived-scalar-mate-composition vs lem-sfb-kflat-scalar-comparison-normalization: the old node fixes theta and inverse-image composition; the new conclusion is about the direct-image mates with the canonical composite geometric adjunction, including the proper/open square.

lem-sfb-derived-scalar-mate-composition vs lem-weil-pbc-mate-pasting: the existing Mathlib leaf is a categorical two-square formula for already specified adjunctions and squares. The new node must identify the K-flat sheaf comparison with theta inverse and match the independently normalized geometric direct-image compositors with composite adjunctions. This is not a one-line specialization of categorical pasting alone.

lem-sfb-derived-scalar-mate-composition vs lem-sfb-ringed-derived-monoidal-comparisons: the old node supplies adjunction-compatible geometric compositors and monoidal pullback coherence, not compatibility of the coefficient-change direct-image mate itself.

Whole-DAG searches used rg for scalar/mate, scalar/composition, thick/projection and isomorphism-locus terminology, followed by reading the candidate statements just distinguished. Whole-blueprint searches used tools/blueprint_refs.py search with scalar mate, scalar composition, scalar direct composition, scalar thick, isomorphism locus and thick comparison. No existing statement covers either extracted result. The blueprint ancestor command still returns None, as for the original item; the new via lists prepend this item to its existing chain, and place fields explicitly locate direct-images paragraph (3). No new Stacks tag is assigned as though it were the extracted theorem's exact source, so there is no fabricated tag-level match.

## Review by NL

I read delivery-errors B–E in full and checked this repair against the mathematical content, not just the JSON layout. The node statement, coefficient topology, canonical beta, ordinary unbounded categories and absence of a constructibility claim over B are unchanged. I corrected no mathematical statement of the item. In particular, B includes every continuous map into norm-topology Omega; it is not the filtered union of finite-field coefficients. The Cartesian identifications in both new lemmas come from inverse image of ring sheaves, so they apply to the pulled-back A_E and B without an admissibility or flatness assumption on B.

Parent step 1 uses the exact conclusion of lem-sfb-derived-scalar-mate-thick-locus: closure under all the finite thick operations specified by lem-sfb-tame-pair-proper-generators. The latter's statement explicitly gives p and q proper, V the inverse image of U, the regular strict-normal-crossing pair, an outer subset and tame lisse L, and generation using finitely many shifts, sums, cones and retracts. I checked that this is generation of the original finite-E bounded-constructible C, not a theorem about B or a different coefficient category. The extracted beta has exactly the adjunct in the item, so its locus is the needed one. Passing between internal modules and module sheaves uses the explicit equivalence cited in both new statements, preserving underlying abelian sheaves.

Parent step 2 retains old step 3 word for word. I opened all three cited statements. The generator node explicitly states Noetherianity and quasi-compactness of the opens. L is locally A_E^r and therefore has the finite constant E^r model required by the constructibility definition. Lem-sfb-scalar-model-immersion-extension gives exact b_! and retained models on a Noetherian scheme; finite E is explicitly among the admissible rings in sk-prop-sfb-cartesian-coefficients. Its zero complementary model gives the required degree-zero bounded-constructible K. Lem-sfb-rational-open-direct-image-constructible explicitly includes finite E and gives bounded constructibility of Rj'_*K for quasi-compact j'. I use only its finite-E branch. These checks supply exactly the two input hypotheses of proper comparison; no constructibility over B is inferred.

Parent step 3 uses the exact commuting-square formula of lem-sfb-derived-scalar-mate-composition. I checked arrow types: both sides run from T_X Rj_* Rq_* K to Rj_{*,B} Rq_{*,B} T_V K, identified with the p,j' path by adjunction-compatible compositors. The left factor is Rj_B(beta_q), and beta_j is the factor cancelled for, so the order is correct. The proper comparison node applies to q on K and p on Rj'_*K, using step 2 and the properness already supplied. The tame-boundary node allows the outer subset to omit components and uses exactly K=b_!L, so its hypotheses match the generator's data, including the inner boundary. Both cited statements specify the same counit mate. Functors preserve inverse arrows; multiplication by the inverse of Rj_B(beta_q) is then elementary cancellation. The thick-locus conclusion from step 1 finishes the finite generation argument.

For the first extracted statement I checked the underlying comparison against the old four cited tools, reading their statements: ring-sheaf-change-adjunction provides conservative exact restriction and its counit-compatible d; sheaf-ring-derived-coefficient-adjunction provides the normalized x tensor a maps on K-flat representatives; ringed-projection-first-shift gives exactness in the K variable and the connecting arrow with P fixed as r_T B_T; triangle-two-out-of-three supplies triangle closure. I intentionally state shift compatibility for the RESTRICTED transformation: conservativity is enough to infer invertibility, and there is no invalid assertion that scalar restriction is faithful on all derived morphisms. Retract closure includes the explicit inverse, checked with naturality and ri=1. These are the argument this unsplit node's future worker must formalize, preserved below.

For the second extraction I checked the three tools of old step 4: K-flat scalar comparison normalization says chi equals theta inverse and gives inverse-image coherence; ringed-derived-monoidal-comparisons explicitly matches the geometric adjunction of a composite to the composite adjunction and its counit; mate-pasting clause (2) is the relevant formula, not merely Yoneda or a fully-faithful claim. The new node states both the formula with kappa written and the square formula after these identifications. It adds neither invertibility nor a base-change theorem. The intended proof and original formula are preserved below.

I tested the new statements when f or g is the identity, when the coefficient map is identity, when K is zero and when the source scheme is empty. The adjunction counit definitions give identity comparisons in the identity cases and zero-object isomorphisms in the empty cases. The retraction formula specializes to beta_G inverse when i and r are identities. Composition has the right domain/codomain and reduces to a unit law when either map is identity. For the parent, j=id, rank-zero L, empty divisor, empty outer subset and all-outer boundary cases agree with the original comparisons. No new assertion about singular or wild pairs has been introduced.

For B1–B10, both new nodes are self-contained TeX statements with definitions/dependencies, precise agent-extraction provenance, and no proof steps or proof sketches. They are unsplit, not mislabeled Mathlib leaves. Each has LeanFinder, LeanSearch, Loogle and logged Mathlib grep searches plus a second semantic phrasing; the complete results remain in searches.jsonl and search-*.txt. I read the actual hits. The promising composition hit CategoryTheory.mateEquiv_hcomp was located by msearch grep at Mathlib/CategoryTheory/Adjunction/Mates.lean:209 and its statement/proof read; it needs identified composite squares. The shift-adjunction hits at Mathlib/CategoryTheory/Shift/Adjunction.lean:210,229 were also inspected. Neither supplies the actual sheaf comparison normalization. Incidental matrix/Lie/CStar grep hits have no relevant derived sheaf statement. No unavailable search was called a negative result, and no unrun search was recorded.

For C1–C8, every parent step's non-elementary input is a cited statement with a verbatim quotation in citations.json. The new nodes do not depend on the item. Off-unit generic finite-E constructibility tools retained in the parent are declared in split_report.tool_uses; no maintainer-owned tool approval was changed. For D1–D5 the two new jobs split different formal arguments rather than restating the target or moving everything into one node. For E1–E7 I checked Cartesian ring maps, exact module inverse image, the scalar/geometric adjunction distinction, composition order and the proper/tame/Noetherian/boundedness hypotheses above. Parent steps have lengths 511, 656 and 830, so none hides an unchecked step over 2000 characters. The two independent jobs are deliberately left statement-only for parallel future work.

## What remains unfinished

Only stage 1 is authorized. The two new nodes are independent unsplit work; no Lean proof or completed subargument is claimed. The existing geometric and coefficient-specific nodes remain the previously established DAG inputs rather than being rewritten in this repair. Required dry-run and delivery results will be recorded below after the tools finish.

## Original argument retained in full, with new ownership

The following is the returned proof verbatim, retained as future-worker briefs, not as proof fields on the new unsplit nodes. Each part is assigned to its extracted job or to the short parent assembly.

### Original step 1; owner: lem-sfb-derived-scalar-mate-thick-locus

Write $T$ for the scalar functors in the statement. For any $f$ define $\beta_f$ by exactly the displayed counit mate, not by choosing an isomorphism. The locus where $\beta_{j,C}$ is invertible is closed under shifts and triangles: restrict scalars from $B$ to $A_E$, which reflects isomorphisms and commutes with derived pushforward by lem-weil-pbc-ring-sheaf-change-adjunction. On K-flat representatives the restricted scalar extension is $C\otimes^L_{A_E}B$, by lem-pur-sheaf-ring-derived-coefficient-adjunction. Its stated formula $x\otimes a\mapsto a g(x)$ identifies the restricted counit mate, after tensor symmetry, with the projection morphism for $j$ and the fixed $A_{E,X}$-module $B_X$. Therefore lem-sfb-ringed-projection-first-shift supplies exactness and compatibility with connecting arrows; lem-sf-triangle-two-out-of-three gives triangle closure. This argument uses no invertibility assertion for a projection formula.

Cited statements: lem-weil-pbc-ring-sheaf-change-adjunction, lem-pur-sheaf-ring-derived-coefficient-adjunction, lem-sfb-ringed-projection-first-shift, lem-sf-triangle-two-out-of-three.

### Original step 2; owner: lem-sfb-derived-scalar-mate-thick-locus (closure and retract formula); parent step 1 (application of existing generator theorem)

The same locus contains zero and is closed under finite sums, isomorphisms and retracts. For the last assertion write $F=T_XRj_{*,A_E}$, $H=Rj_{*,B}T_U$. If $C\xrightarrow{i}G\xrightarrow{r}C$ has $ri=1$ and $\beta_G$ is invertible, the inverse of $\beta_C$ is $F(r)\beta_G^{-1}H(i)$, by naturality and $ri=1$. Apply lem-sfb-tame-pair-proper-generators: it suffices to prove the assertion for $G=Rq_{*,A_E}K$, where $K=(b_!L)[0]$, $p:Y\to X$ and $q:V\to U$ are proper, $j':V\hookrightarrow Y$ is the inverse image of $j$, and $(Y,D,W,L)$ is the specified regular tame pair. Thus the extra geometric assumptions are imposed on generators, not on the given $C$.

Cited statements: lem-sfb-tame-pair-proper-generators.

### Original step 3; owner: parent step 2 (two applications checking constructibility)

For such a generator, finite-rank lisse $L$ is pro-etale locally isomorphic to $A_{E,W}^{r}$, so it has the finite constant scalar model $E^{r}$ on the trivial stratification. The schemes of the generator are Noetherian. The exact extension-by-zero assertion of lem-sfb-scalar-model-immersion-extension gives $K\in\Dbc(V,A_E)$. The finite-$E$ case, and only that case, of lem-sfb-rational-open-direct-image-constructible gives $Rj'_{*,A_E}K\in\Dbc(Y,A_E)$. These are precisely the two bounded-constructible hypotheses needed below for the proper comparison input. No corresponding constructibility assertion for the all-continuous coefficient ring is used.

Cited statements: lem-sfb-tame-pair-proper-generators, lem-sfb-scalar-model-immersion-extension, lem-sfb-rational-open-direct-image-constructible.

### Original step 4; owner: lem-sfb-derived-scalar-mate-composition

First, for any $f$ and a K-flat complex $P$ with flat terms, the pullback/tensor comparison $f_B^*T_T\cong T_Zf_{A_E}^*$ used in the statement is represented by the ordinary sheaf map $f_B^*(B_T\otimes_{A_{E,T}}P)\to B_Z\otimes_{A_{E,Z}}f_{A_E}^*P$, which is the comparison $\chi_f$ of lem-sfb-kflat-scalar-comparison-normalization; by that node it equals $\theta_f^{-1}$, so $\beta_f$ is exactly the mate of the square $\theta_f^{-1}$ along $f_{A_E}^*\dashv Rf_{*,A_E}$ and $f_B^*\dashv Rf_{*,B}$. For composable $Z\xrightarrow{g}T\xrightarrow{f}S$, scalar/pullback coherence in lem-sfb-kflat-scalar-comparison-normalization and adjunction-compatible composition in lem-sfb-ringed-derived-monoidal-comparisons allow mate-pasting, clause (2) of lem-weil-pbc-mate-pasting. Applying its formula to the scalar/pullback squares gives
$$\beta_{fg,K}=Rf_{*,B}(\beta_{g,K})\circ\beta_{f,Rg_{*,A_E}K},$$
under the normalized derived-direct-image compositors. Indeed both sides are mates of the same composite inverse-image square; the counit of the composite is the composite counit specified in those nodes. Since $jq=pj'$, applying this identity twice yields
$$Rj_{*,B}(\beta_{q,K})\circ\beta_{j,Rq_{*,A_E}K}=Rp_{*,B}(\beta_{j',K})\circ\beta_{p,Rj'_{*,A_E}K}.$$
The two domains and codomains are identified using those adjunction-compatible compositors. This proves the equality for the canonical counit mate required by the item.

Cited statements: lem-sfb-kflat-scalar-comparison-normalization, lem-sfb-ringed-derived-monoidal-comparisons, lem-weil-pbc-mate-pasting.

### Original step 5; owner: parent step 3 (application of the new square identity and existing proper/tame comparisons)

Apply lem-sfb-continuous-algcl-proper-scalar-comparison first to $p$ with input $Rj'_{*,A_E}K$, then to $q$ with input $K$; properness is part of the chosen generator and step 3 verified bounded constructibility. Both proper comparisons are isomorphisms. The map $\beta_{j',K}$ is an isomorphism by lem-sfb-continuous-algcl-tame-boundary-comparison: its regularity, strict normal crossings, selected outer components, and tame $L$ are exactly the generator data. Derived direct image preserves isomorphisms, so the right side of the equality in step 4 is invertible, and its left postcomposition $Rj_{*,B}(\beta_{q,K})$ is invertible. Consequently $\beta_{j,G}$ is invertible. Steps 1 and 2 and finite generation give invertibility for the original $C$, with the prescribed counit normalization.

Cited statements: lem-sfb-continuous-algcl-proper-scalar-comparison, lem-sfb-continuous-algcl-tame-boundary-comparison, lem-sfb-tame-pair-proper-generators.

## Validation

The first server dry run completed successfully with durable success receipt at temporary commit a27334c04a7. After that check I added the explicit ring-sheaf-change-adjunction citation to the first new statement to fix the normalization of its d comparison, regenerated its verbatim parent citation, and reran the full dry run before pushing. No proof or statement of the parent changed during this citation clarification.
