# Q80 re-split repair, 2026-10-22

This is the repair of the human's batch-5 re-split return. The previous report is retained below as historical material; its old file list and “no new nodes” statements are superseded by this repair. The sandbox initially contained only dispatcher marker files, so I recovered the current parent node and NS report from the read-only repository. The current parent is the maintainer-fixed four-step split described by the return (3982 characters); its statement, provenance, audit and recorded Lean declaration are retained unchanged. The initial dry run exited 1 because the recovered report lacked Review by Q80; the new review below repairs that diagnostic.

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-weil-smooth-dualizing-complex.json: same statement; three-step assembly, 1661 characters (one step reference corrected afterwards), with two new dependencies.
- dag/nodes/sec-smooth-purity/lem-pur-fixed-pair-right-adjoint-comparison.json: statement, unsplit, no Mathlib match. Generic counit-transpose identification of a supplied lifted right adjoint's structure, together with a counit-normalized comparison to any other right adjoint.
- dag/nodes/sec-smooth-purity/lem-pur-constant-purity-frobenius-square.json: statement, unsplit, no Mathlib match. Geometric constant-object purity, its constant/Tate/shift structure identification and its square with the actual exceptional adjunction mate.
- citations.json and report.md: updated step citations and this repair report. Searches are preserved in searches.jsonl. No unit or Lean files changed.

## Attachments

None. I searched the project for the item and its concept. WeilConjectures/WeilSheaf/VerdierDual.lean:196-201 still has sorry in AlgebraicGeometry.WeilComplex.nonempty_dualizingComplex_iso. Its use in VerdierDualLocalization is not a proof of the item. IsoAlgebraAdjunction.lean:88-139 constructs the specified mate lift and its unit/counit; it does not identify the structure of an independently supplied lift and compare an arbitrary right adjoint with it as the new comparison statement does. No project declaration found states every clause of either new node.

## WANTED

None. No SGA material is used. These auxiliary statements make precise parts of the existing agent-written Weil refinement, rather than claiming that a Stacks tag states the whole refinement.

## What changed and why

The only return point asks for at least two statement-only children of comparable workload and an assembly below 3000 characters, retaining all arguments. The new comparison task receives old step 2 and the middle of old step 3 (the counit-transpose identification). The new geometric task receives old step 1 and the beginning and end of old step 3 (constant pullback, Tate/shift structure and rational purity naturality). Old step 4 remains explicit in the parent, with its reference updated to the new step 2. Neither child asserts the parent's conclusion: the first has no schemes or purity, and the second has no arbitrary equivariant right adjoint or dualizing object defined by that adjoint. They are independent tasks and do not cite each other or the parent. This distributes roughly 1500-1800 characters of old categorical work and 1500-1800 characters of old geometric-comparison work, with the old inversion left in the assembly.

I did not remove the existing statement-dispute report or pretend that the retained Lean record now matches the fixed-pair statement. The point/Jordan-block test below remains relevant. This repair is the authorized re-split of the already corrected statement, with no further statement change.

## Source reading and search results

I read the parent and its full maintainer review, the unit sk-thm-purity-transport (especially step 4), the main-20261015 cor-pur-adic-and-rational-smooth-dualizing-complexes statement and proof, and prop-weil-operations.proof.md sentences 1 and 3. For the categorical child I also read the actual statements of cor-coef-verdier-weil-equivariance, det-sp-unique-right-adjoint, lem-sf-fixed-pair-adjunction-lift and lem-pod-constructible-mate-coherence, and the source sk-prop-sp-unique-adjoint-categorical.md. For the geometric child I read lem-pur-rational-weil-naturality-mate, both canonical constant and Frobenius coefficient twist definitions, the geometric dualizing corollary, and the strict-data equivariance theorem to distinguish its hypotheses. Thus both children retain the parent's actual counit and rational/common-stage comparisons.

I searched the whole DAG's statement fields for fixed-pair/adjunction/counit combinations and searched all blueprint nodes with blueprint_refs.py for “adjunction equivariant”, “fixed adjoint”, “purity Frobenius”, “constant Frobenius” and “dualizing smooth”. I read the plausible matches above, rather than treating their titles as sufficient. Source/keyword searches in the live Lean library included IsoAlgebraAdjunction, MateTransport, fixed-pair forgetting, and the WeilSheaf modules. The item's blueprint reference to lem-a1-local-boundary-duality is retained; new children retain the exact argument place and via=[parent]. Their from.node is null, matching the ancestor command and the dry-run diagnostic. The ancestor command mechanically returns None because the maintainer-created parent's created.item is null; I report this existing broken created chain rather than altering the maintainer's created record. The first full preflight rejected my attempted inheritance of the parent's explicit ancestor (B9); I corrected only the children's from.node to the actual computed null, leaving the parent record untouched. Both new from.place fields specify the portion of the old argument they carry, and same_as is [] after the whole-blueprint search.

Each child has actual msearch entries for LeanSearch, LeanFinder, Loogle and grep, including a second natural-language formulation. All returned signatures were read. Categorical searches found generic uniqueness in Mathlib/CategoryTheory/Adjunction/Unique.lean (rightAdjointUniq at 102; counit characterization at 105-108 and 127-130) and adjoint triangle lifting in Adjunction/Lifting/Right.lean, not the fixed-structure assertion. The grep hits at Limits/Shapes/SingleObj.lean:21,62-71 concern fixed elements of monoid actions. Geometric searches found ordinary scheme-module pullback adjunctions, the unrelated monoidal frobeniusMorphism_mate, and Witt-vector isocrystals; no exceptional purity/Tate twist statement. The Tate/dualizing grep and both Loogle searches had no hits. The child search fields copy the exact executed tool/query strings. Existing historical parent searches are retained.

## Not duplicates

lem-pur-fixed-pair-right-adjoint-comparison vs det-sp-unique-right-adjoint: the latter compares adjoints in an arbitrary category but has no fixed structure or mate/counit formula; the child also determines an independently supplied lifted structure from its counit.
lem-pur-fixed-pair-right-adjoint-comparison vs lem-sf-fixed-pair-adjunction-lift: the existing theorem constructs a particular lift from a supplied invertible mate; the child starts from any counit-normalized lift, identifies its structure and compares every independently chosen right adjoint to it.
lem-pur-fixed-pair-right-adjoint-comparison vs lem-pod-constructible-mate-coherence: the latter constructs the geometric exceptional lift and proves its operation coherence; it does not give the new abstract recognition/comparison theorem for an arbitrary supplied right adjoint.
lem-pur-constant-purity-frobenius-square vs cor-pur-adic-and-rational-smooth-dualizing-complexes: the corollary has only the underlying geometric dualizing formula and trace; the new statement identifies the actual canonical constant/Tate/shift Frobenius arrows with the adjunction mate square.
lem-pur-constant-purity-frobenius-square vs lem-pur-rational-weil-naturality-mate: the latter supplies naturality and the mate formula for general K; it does not identify pullback of the canonical constant Weil object and its twisted/shifted structure. That identification, specialization and geometric typing comprise the complementary task extracted from old steps 1 and 3.
lem-pur-constant-purity-frobenius-square vs thm-pur-weil-equivariance-of-purity-and-trace: the theorem assumes the specified strict datum; the child uses the rational canonical constant datum and the actual exceptional adjunction mate, without a stable integral lattice.
lem-pur-constant-purity-frobenius-square vs prop-pod-dual-tate-data-compatibility: the latter assumes geometric connectedness and strict perfect data and gives a duality formula, not the canonical constant pullback and mate identification here.
lem-pur-constant-purity-frobenius-square vs prop-weil-operations: the operations package says comparisons are equivariant but does not give the explicit normalization of constant/Tate/shift structures with the specified geometric gamma and mate.

## Review by Q80

I checked the single return point against the actual old proof, rather than replacing it by a shorter explanation. The two new files have status unsplit and empty proof/proof_deps/proof_origin, and their statements introduce all their objects. Their proof work is retained below verbatim as a specification for the future workers, not hidden as proof steps inside the child statements. The parent statement is byte-for-byte unchanged. It now uses the two children to assemble the result in three steps below the prescribed length.

Step 1 cites the separated finite-type base-change lemma and the smooth-relative-dimension permanence lemma. Their statements explicitly give these properties under arbitrary base change; the field extension to k is such a base change, including d=0 and an empty X. The geometric child supplies the canonical gamma, the structure equality and its mate square exactly as used. Step 2 cites the coefficient-equivariance corollary, whose statement lifts the geometric exceptional adjunction with equivariant unit and counit. The operations statement describes the compact-support structure via exchange, so its lifted left adjoint is exactly the one in the new categorical statement. With C=D^b_c(X,Lambda), D=D^b_c(s,Lambda), Q and P the respective Frobenius pullbacks, all functors have the required variance. The chosen right adjoint J need not have a prescribed carrier; the child supplies its canonical comparison in fixed pairs. Its first formula identifies the structure of the normalized lift, allowing substitution into the square of step 1. Step 3 uses the actual morphism condition and composition rule in def-weil-weil-sheaf-complex. Multiplication by gamma inverse and Q(gamma inverse) proves the inverse is equivariant; its two composites are identities. The final composition is an isomorphism in fixed pairs, with no promotion to D(Weil).

For the comparison child I checked the counit calculation itself: equivariance gives epsilon_K F(vartheta) beta_GK = theta P(epsilon_K). Counit naturality and the displayed mate identity give epsilon_K F(G(theta)e_K) = theta epsilon_PK F(e_K) = theta P(epsilon_K) beta_GK^-1. The two maps QGK to GK thus have identical adjunction transposes, hence coincide. Ordinary uniqueness of right adjoints is then applied inside the same fixed-pair categories, giving the unique counit-compatible alpha and its carrier equation. This is the old maintainer fix, not an assumption that an unspecified exchange is automatically the correct mate. The statement supplies the invertible e and the lifted adjunction as hypotheses; it does not erroneously assert that an arbitrary mate of an isomorphism is invertible.

For the geometric child I checked the constant comparison at finite coefficients: all inverse-image structure maps send a constant section lambda to lambda, so the two composites for a g_X = g_s a coincide. Integral inverse limits and rational/common-stage images are precisely the constructions in the constant definition. Tensoring with the canonical Tate line and using the pullback-shift comparison yields theta_H=H(theta0)b. The mate lemma supplies e=gamma_PK b (Qgamma_K)^-1 and naturality for the rational map theta0. Substitution gives G(theta0)e Qgamma=G(theta0)gamma_PK b=gamma_K H(theta0)b, the required square. This preserves the explicit constant-object argument and the common-stage qualification, with no Frobenius-stable lattice hypothesis. The hard geometric purity input stays the lecture-notes reconstruction/transport route already used by the parent.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against these two allocations. In particular, the new comparison task has two linked arguments (recognition by transpose, then adjoint comparison); the geometric task includes the coefficient-level canonical-structure comparison as well as the mate square. They are not new copies of the parent's isomorphism or of its two clauses, and no single existing statement states either task in full. Existing construction/uniqueness/mate results remain the inputs for their future splits. No new Stacks tags or finite-purity route were invented. The generic off-unit inputs retained in the parent are declared in split_report.tool_uses; removed direct inputs are assigned to the child work plans below. No new child depends on the parent, and there is no new dependency cycle by construction.

Small cases: in the comparison child take P=Q=id and beta=e=id, which gives the usual G(theta) structure; if F=G=id and theta is arbitrary (including a nontrivial Jordan automorphism), the formula forces precisely theta, showing why the counit normalization matters. For the geometric child X0=Spec k0,d=0 makes gamma the identity with no twist or shift; an empty scheme gives the zero object and its unique structure; disconnected smooth schemes are allowed, since no step uses geometric connectedness. The twist is +d and the shift +2d, so the underlying constant sheaf lies in degree -2d. The existing Jordan-block category warning is retained below.

Every parent citation has an exact substring from the statement in citations.json, including the new children's formulas. No step exceeds 2000 characters. All substantive old argument text follows below, so an independent reader can check that no work was discarded or blurred.

## Preserved old argument and allocation

The following are the exact text of the four maintainer-fixed old steps. Old step 1 is assigned to the geometric child (the parent also keeps explicit permanence typing); old step 2 to the categorical child; old step 3 is divided between them at the counit-transpose calculation as described above; old step 4 stays in the parent. These are work plans retained in the report; the new nodes deliberately contain no proofs.

### Old step 1

Base change along $k_0\to k$ preserves separated finite type and smoothness of relative dimension $d$, by [lem-pod-separated-finite-type-base-change] and [lem-sbc-smooth-relative-dimension-permanence]. Thus $a:X\to s$ satisfies the hypotheses of [cor-pur-adic-and-rational-smooth-dualizing-complexes] at $\Lambda=\overline{\mathbf Q}_\ell$. Denote the canonical purity isomorphism by $\gamma:H\xrightarrow{\sim}G(\Lambda_s)$, where $G=Ra^!$ and $H=\Lambda_X(d)[2d]$. Its inverse is exactly the geometric dualizing identification in that corollary. This uses the already transported integral/rational purity, without introducing a new finite-coefficient proof route.

### Old step 2

By [cor-coef-verdier-weil-equivariance], the geometric constructible adjunction $Ra_!\dashv G$ lifts to the categories of Weil pairs with equivariant unit and counit. Write $\widetilde G$ for this lift. Its left adjoint is the compact-support lift used in the statement, by [prop-weil-operations]. The assumed right adjoint $Ra_0^!$ and $\widetilde G$ are therefore right adjoints of the same functor on these same fixed-pair categories. Apply [det-sp-unique-right-adjoint] there: the transposes of their counits give mutually inverse natural transformations. At the constant Weil sheaf this yields $\omega_{X_0}\cong\widetilde G(\Lambda_s,\theta_0)$. In particular no identification of a derived category of Weil sheaves with a category of fixed pairs is used.

### Old step 3

Put $P=Lg_s^*$, $Q=Lg_X^*$, $F=Ra_!$, $G=Ra^!$ and $H(K)=La^*K(d)[2d]$. For $K=\Lambda_s$ write $b_K:QH(K)\xrightarrow{\sim}H(PK)$ for the pullback-composition, twist and shift comparison. Here $La^*\Lambda_s=\Lambda_X$, and $La^*(\theta_0)$ composed with pullback composition for $ag_X=g_sa$ is the canonical constant structure on $\Lambda_X$ of [def-weil-constant-weil-structure]: both are composites of inverse-image structure maps of constant sheaves, which send a constant section $\lambda$ to $\lambda$. Hence, by [def-weil-frobenius-coefficient-twists], the Weil structure on $H(K)=\Lambda_X(d)[2d]$ is $\theta_H=H(\theta_0)b_K$. Let $\beta:PF\xrightarrow{\sim}FQ$ be the compact-support exchange, so that the lifted compact-support functor gives $FM$ the structure $F(\theta_M)\beta_M$ [prop-weil-operations]. By [lem-pur-rational-weil-naturality-mate],
$$e_K=\gamma_{a,PK}\,b_K\,(Q\gamma_{a,K})^{-1}$$
satisfies $\varepsilon_{PK}F(e_K)=P(\varepsilon_K)\beta_{GK}^{-1}$. Now let $\theta_G$ be the Weil structure of $\widetilde G(\Lambda_s,\theta_0)$ from step 2. Its counit is equivariant [cor-coef-verdier-weil-equivariance], i.e. $\varepsilon_K F(\theta_G)\beta_{GK}=\theta_0P(\varepsilon_K)$. Naturality of $\varepsilon$ and the mate equation give $\varepsilon_KF(G(\theta_0)e_K)=\theta_0\varepsilon_{PK}F(e_K)=\theta_0P(\varepsilon_K)\beta_{GK}^{-1}$. So $\theta_G$ and $G(\theta_0)e_K$ have the same transpose $QGK\to K$ under $F\dashv G$, and therefore $\theta_G=G(\theta_0)e_K$. The naturality clause of the same mate lemma, applied to the rational morphism $\theta_0:PK\to K$, gives
$$\theta_G\,Q\gamma_{a,K}
=G(\theta_0)\gamma_{a,PK}b_K
=\gamma_{a,K}H(\theta_0)b_K
=\gamma_{a,K}\theta_H.$$
So the adjunction-lift structure agrees with the purity structure. At $\overline{\mathbf Q}_\ell$ these equations hold in the common-stage category, as the mate lemma states. No Frobenius-stable integral lattice is assumed.

### Old step 4

The equality in step 3 is precisely the morphism condition of [def-weil-weil-sheaf-complex]. Since $\gamma$ is an underlying isomorphism, multiply $\theta_G Q\gamma=\gamma\theta_H$ on the left by $\gamma^{-1}$ and on the right by $Q(\gamma^{-1})$. This gives $\gamma^{-1}\theta_G=\theta_H Q(\gamma^{-1})$, so its inverse also is a morphism of fixed pairs. The two composites are identities because composition in the fixed-pair category is the underlying composition. Thus $\widetilde G(\Lambda_s,\theta_0)\cong\Lambda_X(d)[2d]$ in $\mathrm{WC}(X_0)$. Compose with the isomorphism of step 2 to obtain the asserted isomorphism.

## Unfinished work

The two new argument nodes are intentionally unsplit tasks for other workers, as the return requests. The parent assembly is complete. The historical mismatch with the retained derived-Weil Lean record remains a maintainer issue, unchanged by this repair.

## Earlier report retained verbatim

# Stage-1 delivery: lem-pur-weil-smooth-dualizing-complex

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-weil-smooth-dualizing-complex.json: statement, split into four steps, using existing nodes only; not a Mathlib leaf.
- citations.json: one verified verbatim statement excerpt per step/node citation.
- report.md: this report. searches.jsonl contains the actual msearch results. No new DAG nodes, no new Mathlib leaves, no unit changes.

## Attachments

None. The project declaration AlgebraicGeometry.WeilComplex.nonempty_dualizingComplex_iso at lean/WeilConjectures/WeilSheaf/VerdierDual.lean:196 has a sorry at line 201. Searching the entire WeilConjectures tree for the item tag and declaration found its call in VerdierDualLocalization, not a finished proof of the item. The finite-coefficient etale dualizing isomorphism is a different assertion.

## WANTED

None: all material used is available locally. No SGA source is used.

## Statement corrected

STATEMENT-DISPUTED: the imported statement identifies the category of def-weil-weil-sheaf-complex with Lean `WeilComplex k₀ ℓ X`. They are different categories. The former explicitly defines Frobenius-fixed pairs over a geometric derived category and explicitly denies being a derived category of Weil sheaves. The latter is a full subcategory of the derived category of pro-etale Weil sheaves, as lean/WeilConjectures/WeilSheaf/Category.lean:61-76 explicitly states.

Here is a point test: let X₀ = Spec(k₀) and let Λ = Qbar_l with trivial Frobenius. A two-dimensional Jordan block with Frobenius matrix [[1,1],[0,1]] defines a nonsplit extension of the trivial Weil sheaf by itself: an invariant splitting would be a vector projecting to 1 and fixed by that matrix, which is impossible. It therefore gives a nonzero Ext¹ and a nonzero morphism Λ → Λ[1] in the derived category of Weil sheaves. In the fixed-pair category every such morphism has underlying morphism in Hom_D(Spec(k),Λ)(Λ,Λ[1]) = 0. Thus these categories cannot be identified as asserted while preserving the indicated objects and forgetful functor. This exact issue is recorded in the definition node itself; it is not a conjectural failure of purity.

I repaired the statement faithfully to its blueprint/definition meaning: X₀ denotes the original scheme, X its geometric fiber; WC(X₀) explicitly denotes fixed pairs; the compact-support functor is the equivariant lift; the constant object and its Tate twist have their canonical Weil structures. The hypotheses (finite field, different prime, separated finite type, smooth relative dimension d, existence of the chosen right adjoint) and the isomorphism conclusion are retained. The shift is explicitly the shift of the underlying complex and Weil arrow and makes no triangulated-category assertion. The misleading Lean parentheticals and reference to a raw E-only twist definition were replaced by the definition nodes that actually define the qbar fixed-pair objects and operations.

The existing `lean` field is maintainer-owned and has been retained verbatim, but is NOT a claim that the repaired statement matches the upstream signature. The maintainer needs to reassess that attachment. This delivery proves the source-intended fixed-pair assertion; it supplies no equivalence with the upstream derived category and does not claim to remove the upstream sorry. The read clone has one DAG citer, lem-a1-local-boundary-duality. Its statement already uses the fixed-pair coefficient conventions, and its smooth-curve duality step directly cites geometric rational purity; that mathematical formula is unaffected. Its upstream Lean proof uses the derived-Weil declaration, so that implementation route still needs the separate reassessment just described. I did not edit the citer.

## Sources and route

I read the main-20261015 unit sk-thm-purity-transport, the matching corollary in sk-cor-sp-all-coefficients (statement and proof), prop-weil-operations (statement and proof), thm-pur-weil-equivariance-of-purity-and-trace (statement and proof), cor-coef-verdier-weil-equivariance (statement and proof), and det-sp-unique-right-adjoint's categorical source. The current corollary is located in sk-cor-sp-all-coefficients, rather than its older sk-thm-purity-transport directory. The split realizes the unit's specialization to the constant coefficient object, followed by the existing Frobenius-equivariant adjunction lift. It does not replace the lecture-notes finite-purity route.

The generic tools from other units are declared in split_report.tool_uses: geometric base-change permanence, equivariant adjunction, equivariant operation comparison, right-adjoint uniqueness, and the rational purity/mate identification. These supply typing and categorical transport; none replaces the geometric smooth-purity theorem of this unit.

## Searches and duplicate check

There are no new nodes. I searched the DAG and blueprint for dualizing complexes, smooth dualizing formulas, and Weil equivariance, and read the actual statements of every node subsequently cited. The geometric corollary is reused: it proves the geometric formula but has no Weil datum. The equivariance theorem alone defines smooth exchange through purity, so I also use the existing rational Weil naturality/mate lemma, which identifies that exchange with the actual adjunction mate. No new copy of those statements was made.

The item's Mathlib searches were run using msearch: LeanFinder with two phrasings, Loogle for `"dualizingComplex"`, grep for `dualizingComplex|upperShriek|WeilComplex`, and LeanSearch for smooth purity. I read the returned hits: scheme-limit, smooth-dimension and ordinary module-pullback results, with no matching Weil dualizing assertion. All new records copy the executed query texts and actual results from searches.jsonl. The imported historical searches are retained rather than silently rewritten.

## Not duplicates

No new nodes. The blueprint same_as entry is retained as the provenance of the underlying smooth dualizing formula, not an assertion that forgetting the Weil datum is a category equivalence.

## Review by NS

I checked delivery-errors B through E against the four steps, the cited statements and the source text. Step 1 uses separated finite-type base-change permanence and fixed-relative-dimension smooth base-change permanence, both of which explicitly allow precisely this field extension; it then applies the existing dualizing corollary at Λ = Qbar_l to the geometric structure map. That corollary identifies its isomorphism as the inverse of transported purity, so the later use of gamma is justified by its statement, not its proof. The geometric corollary supplies the hard purity calculation already on the required route.

In step 2 the coefficient-equivariance corollary explicitly says the constructible exceptional adjunction lifts to Weil pairs with equivariant unit and counit. The operations node identifies the compact-support lift in the same category. I apply uniqueness of right adjoints within the fixed-pair categories themselves, so the chosen right adjoint in the statement is covered even if it is not the canonical lift. The uniqueness lemma's statement supplies mutually inverse transposes of the counits. I did not cite an exceptional-inverse-image definition as a substitute for this theorem.

Step 3 uses the twist node that covers qbar coefficients, not just the E-only raw-coefficient definition. Its tensor Weil map and pullback/shift comparisons identify the source structure. The rational naturality/mate node explicitly supplies BOTH naturality for every rational morphism and identification of e with the adjunction mate. The operations node says the exceptional lift uses exchange and adjunction maps. Substitution into the three displayed equalities proves the required square without assuming a stable integral lattice. This corrects the potential gap of treating the purity-defined exchange as automatically the actual exceptional exchange.

Step 4 is elementary algebra on that commuting square. I wrote the inverse morphism equation explicitly, used functoriality Q(gamma^-1) = (Q gamma)^-1, and used the stated definition of composition and morphisms of fixed pairs. Nothing is promoted to a derived-category morphism by faithfulness alone. Every cited statement was opened and every citations.json quote was checked by exact substring membership. All four steps are below 2000 characters; no long step hides a new comparison lemma.

The small cases are consistent: d = 0 gives the untwisted unshifted etale formula; X₀ empty gives the unique zero objects and isomorphism and needs no dimension maximum; X₀ = Spec(k₀) gives the constant object and trivial twist. The sign is [2d], hence the resulting sheaf is in cohomological degree -2d. The Jordan-block point test specifically prevents the incorrect identification of coefficient categories. No hypothesis of properness or a Frobenius-stable lattice is introduced. There are no new statements to test, no new same-tag pairs, and no new unsplit child hiding a clause of this item.

## Unfinished work

No unfinished stage-1 argument for the corrected fixed-pair statement. The upstream derived-Weil interpretation requires a separate comparison or an independently justified derived-Weil purity argument; the retained Lean attachment must not be accepted as an exact rendering of this node.
