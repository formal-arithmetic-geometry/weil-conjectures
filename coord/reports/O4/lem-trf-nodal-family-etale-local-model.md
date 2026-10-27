# O4 repair: lem-trf-nodal-family-etale-local-model

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-nodal-family-etale-local-model.json`: unchanged statement, five-step assembly; 2712 proof-text characters, below the 3000-character return limit.
- `dag/nodes/sec-trace-formula/lem-trf-nodal-family-split-point-neighbourhood.json`: statement, unsplit; no Mathlib match. Carries old steps 2--3: splitting the nonsmooth fibre point and realizing its field in an affine etale base neighbourhood.
- `dag/nodes/sec-trace-formula/lem-trf-split-node-algebraization-finite-type.json`: statement, unsplit; no Mathlib match. Carries old steps 4--6: verifying the formal lemma, constructing the universal-model formal base map, and relative algebraization.
- `dag/nodes/sec-trace-formula/lem-trf-pointed-etale-diagram-pullback.json`: statement, unsplit; no complete Mathlib match. Carries old steps 8--9, including the iterated-product identifications, compatible model morphism, open restrictions, pulled-back function and point over the originally specified x.
- `citations.json`: a verbatim statement quote for every node used by each parent step.
- `searches.jsonl`: actual msearch.py records retained as emitted. New-node records use those exact tools and query strings. Scratch scripts and `returned-node.json` are sandbox handoff material only.

## Attachments

None. The node's project theorem `AlgebraicGeometry.exists_etale_nodal_local_model`, at `lean/Sheaf/SixFunctors/TraceFormula/NodalFamilyEtaleLocalModel.lean:182`, has proof `sorry` (line 201); it is not an attachment. Searching the entire `lean/WeilConjectures/` for the item tag, nodal local models, split nodes and ordinary double points found no finished declaration stating the item or any new child. The matched Sheaf module's full statement and nine-step docstring were read; no Lean file was changed.

## WANTED

None. The source files needed here are present locally: `literature/stacks-project/curves.tex`, `more-morphisms.tex`, and `morphisms.tex`, with the exact tag-to-label map in `literature/stacks-project/tags/tags`.

## What was wrong and what was repaired

The return asks to spread the 6998-character nine-step argument into at least two comparable statement-only nodes, rather than shorten it. I added three independent proof tasks with self-contained statements of approximately 1500--1700 characters each. The parent retains old step 1 and old step 7; its other steps assemble the new interfaces. The proof text carried by the children is 1756 characters (old 2--3), 2817 (old 4--6), and 1417 (old 8--9); every original sentence, source and dependency list is preserved below for their future workers. No child's statement has a proof sketch or proof steps. Each has `proof: []`, `proof_deps: []`, `proof_origin: null`, and status `unsplit`.

This is a substantive decomposition: child 1 concludes only a split fibre point, child 2 assumes an already rational split node over a finite-type affine integer base, and child 3 is a general pullback lemma for an already supplied diagram. None states the entire original assertion. Child 3 handles a whole compatible diagram through two product identifications and open restrictions, not merely the elementary existence of a point in one fibre product. The existing field-splitting, formal-equation, approximation and base-change tools are retained in the proof handoff rather than recreated as duplicates. The mathematical parent statement, statement dependencies, prior source/search records, Lean metadata and ancestry remain unchanged. There is no statement dispute and no change of proof route.

The sandbox initially had only dispatcher marker files, despite the repair brief's expectation that the delivered version was retained. I recovered the returned nine-step proof from the live read-only node and preserved it in `returned-node.json`. There was no prior report or search log in this item's sandbox to overwrite. The current read-clone node is the returned baseline; the delivery tool rebases the owned fields against current server main and keeps maintainer metadata. No repository git command was run.

## Review by O4

I read the complete first proof of Stacks 0CBY (`lemma-etale-local-structure-nodal-family`) against the unchanged parent statement. It first approximates by a finite-type integer base, then splits the node through a finite separable residue extension, then applies the formal node equation and relative approximation. I read 0CBX's statement and its formal-equation setup, and 0GDX's full hypothesis/conclusion block (`lemma-relative-map-approximation-pre`). The latter requires an isomorphism of completed local rings over the completed base, not just an abstract ring isomorphism. I retained that distinction in the handoff and did not claim the eventual algebraic smoothing function equals the original formal one. For the pullback child I checked the first paragraph of 0CBY and the base-change-surjectivity statement 01S1 (`morphisms-lemma-base-change-surjective`). The current blueprint `main-20261015` locality statement/proof was read for ancestry: these are historical nodal-model inputs, not a new proof of its contracting-correspondence theorem. No prohibited SGA route was used.

For parent step 1 I opened `lem-trf-nodal-family-noetherian-approximation`: it explicitly gives the affine Cartesian model, flat finitely presented finite-type integer morphism, the same geometric-fibre condition, and nonsmooth x_0. Thus its statement, not its proof, supplies every datum used. The unchanged geometric hypotheses and chosen nonsmooth x match it exactly.

For parent step 2 I checked the new split-point-neighbourhood statement: its hypothesis includes finite presentation of f_0, finite type of both integer schemes, the fibre condition and nonsmooth x_0. Step 1 supplies them all. Its conclusions explicitly include V_1 affine of finite type over Z, the etale pointed base map, the point above x_0 and v_1, rationality, completed fibre equation and flat local finite presentation of f_1. These are exactly what step 3 takes. In the old-argument handoff, `lem-trf-nodal-point-finite-separable-splitting` really states the finite separable extension with a rational split node, `lem-trf-nodal-family-fitting-singular` really identifies the nonsmooth set after arbitrary base change, and `lem-weil-pbc-etale-neighbourhood-prescribed-residue-field` really realizes the extension as a pointed etale base neighbourhood. I opened all three statements. The finite-type fibre calculation, affine restriction and finite-generator argument are retained rather than hidden by a bare nodal definition.

For parent step 3 I checked the new algebraization statement: it needs only a flat locally finitely presented map, affine base finite type over Z, a rational point in its fibre and the displayed completed fibre equation. Step 2 supplies each. The conclusion states all three etale arrows, w, tau, both commuting triangles and the required distinguished point; it also identifies the algebraic target by h=tau^*a. In its handoff, I opened the formal-local-structure node and checked its additional closed-in-fibre and Noetherian-stalk hypotheses. Rationality makes the point closed: on an affine containing it the map to K is a surjective K-algebra map, so its prime is maximal; any proposed specialization has an affine neighbourhood containing both. The finite-type-over-Z theorem, affine-open Noetherianity, Spec-stalk identification and localization theorem explicitly give Noetherianity of the base stalk. Dropping finitely many relations proves local finite type. The formal theorem explicitly includes the completed local ring of M_h at its origin as an equivalent conclusion. Substituting a by the formal parameter in the universal presentation and localizing at the closed-point image gives the local sigma required by the relative approximation statement. Both bases are finite type over Z, so that node's G-ring reduction is within its stated hypotheses. I read that statement, not merely its title.

For parent step 4 I reopened `lem-weil-pbc-etale-base-change-finite-limits`, clause (1), and `lem-weil-pbc-etale-composition-cancellation`, clause (2). The first applies to X_1 -> X_0, which is the base change of V_1 -> S_0; the second composes it with U_0 -> X_1 and composes V_2 -> V_1 -> S_0. Both triangles already commute by step 3. No etaleness of X_0 -> S_0 is assumed.

For parent step 5 the new diagram-pullback statement has all required inputs: etale p_0 and e_0 from step 4, the etale model map and commutativity from step 3, the Cartesian open presentation and x projecting to x_0 from step 1. Its conclusion gives the canonical U-identifications, the base-changed model morphism, composition with the two open inclusions, both triangles and a point projecting to the prescribed original x. The final reversal of the two factors of Y times_T V and evaluation of the presentation are fibre-product universal-property substitutions; they introduce no new geometric lemma. I checked the old `lem-weil-pbc-surjective-base-change` statement for the handoff's residue-field-spectrum argument: it allows arbitrary base change, so no flatness of S^circ -> S_0, equality of residue fields, or surjectivity of the entire chart is presumed. The child concludes a point over both u_0 and x, as the residue-field fibre product actually supplies.

Small cases checked: for child 1 a split node can use a trivial splitting field; a nonsplit quadratic node needs a separable extension and is not silently split over the original residue field. In characteristic two an Artin--Schreier splitting extension is allowed; no square-root argument is imposed. A smooth family or empty chosen fibre cannot supply the required nonsmooth x_0. Child 2 allows h=0 and nilpotent smoothing parameters; no domain, regularity, smooth generic fibre, characteristic restriction or global properness is imposed. A rational point is closed even if it is not closed in the total scheme. Child 3 works for non-surjective base change, unequal residue extensions, non-affine bases and nonseparated schemes; a prescribed x rules out an empty relevant pullback. For kappa(u_0) and kappa(x) over kappa(x_0), their field-spectrum product is nonempty even when it is not a single point. Identity base change and identity open immersions recover the original pointed diagram. These checks exposed no false statement needing correction.

I compared each step with its cited statement (C4) and kept all non-elementary uses named (C1). All new notions have definition dependencies; no theorem is asserted solely by citing a definition. `citations.json` contains the exact full statements for all six parent citations. I also checked the dependency sets equal the unions of the step uses and that no child depends on the parent. There are no parent steps above 2000 characters. The only >2000-character handoff block comprises old steps 4--6, now assigned as one explicit algebraization task with a separate complete statement and no proof; it is not hidden in a long parent step.

Mathlib search review: I ran and read LeanFinder, Loogle, grep and LeanSearch for each child, including a second semantic phrasing and supplementary greps. The actual records are assigned to the nodes using their exact logged query strings. I read the Etale source at its flat/unramified equivalence and pullback instances, and PullbackCarrier at `Scheme.Pullback.exists_preimage_pullback` (line 306) and the base-change-surjectivity instances (line 436 onward). These are tools for individual parts of child 3, not a one-line instance of its entire diagram statement. Standard smooth charts apply to smooth points and do not supply nodal singular normal forms. The coprime-polynomial factor-lifting hit does not split a curve singularity or produce this family diagram. Polynomial interpolation's use of the word 'nodal' is unrelated. All services ran successfully; no outage was disguised as an empty search.

Duplicate review: I searched all `dag/nodes` by nodal/split/pointed-pullback terminology and by the relevant Stacks tags, and ran `tools/blueprint_refs.py search` for split node, nodal family, etale diagram, base change chart, 0CBY, 0GDX and point over. No blueprint node states a child. I opened the same-tag candidates and distinguish their statements below. The generic prescribed-residue-field tool is used inside the first child's future proof, not duplicated. The formal equation theorem supplies a completion, whereas the second child concludes an algebraic etale chart. The generic relative approximation theorem requires a specified formal comparison, which the second child must construct. The third child's whole-diagram assertion needs the canonical identifications and point and function compatibility, beyond single-arrow base-change or image formulas.

## Not duplicates

- lem-trf-nodal-family-split-point-neighbourhood vs def-sfb-nodal-branch-scheme: existing defines a graph blowup construction B_f; this child is an existence theorem for a rational split fibre point, and asserts nothing about B_f.
- lem-trf-nodal-family-split-point-neighbourhood vs lem-sfb-dvr-nodal-chart-blowup-calculus: existing computes regularity and blowups of explicit DVR models xy=pi^n; this child supplies a split point over an etale finite-type neighbourhood.
- lem-trf-nodal-family-split-point-neighbourhood vs lem-sfb-nodal-branch-double-cover: existing constructs the canonical etale double cover of the singular subscheme for all fibres; this child selects one split point over a pointed etale base neighbourhood.
- lem-trf-nodal-family-split-point-neighbourhood vs lem-sfb-persistent-node-normalization: existing normalizes persistent generic nodes of projective trait families; this child only splits a prescribed fibre point over an etale finite-type neighbourhood.
- lem-trf-nodal-family-split-point-neighbourhood vs lem-trf-formal-local-structure-nodal-family: existing gives a formal total-space equation once the fibre point is already split; this child produces that split fibre point by a separable etale base extension.
- lem-trf-nodal-family-split-point-neighbourhood vs lem-trf-nodal-etale-chart: existing constructs marked/log-compatible charts under stronger hypotheses and uses the parent; this child only selects a rational split fibre point and does not construct its model chart.
- lem-trf-nodal-family-split-point-neighbourhood vs lem-trf-nodal-family-etale-local-model: parent gives a nodal etale chart for an arbitrary base; this child only supplies a rational split fibre point after a finite-type etale base neighbourhood, without a model chart.
- lem-trf-nodal-family-split-point-neighbourhood vs lem-trf-nodal-generic-component-closure: existing proves flat component closure and finite boundary over a valuation base; this child only splits one fibre point over a finite-type integer base.
- lem-trf-nodal-family-split-point-neighbourhood vs lem-trf-nodal-log-regularity: existing concludes log regularity for proper marked nodal families; this child only selects a split fibre point with no log or marking assumptions.
- lem-trf-nodal-family-split-point-neighbourhood vs lem-trf-ordered-nodal-branch-overlap: existing compares labelled branch ideals generically on overlaps of given valuation-ring charts; this child constructs a split fibre point and has no branch-ideal conclusion.
- lem-trf-nodal-family-split-point-neighbourhood vs lem-trf-valuation-smooth-branches-strict-chart: existing gives strict Zariski charts under smooth-branch valuation hypotheses; this child constructs only a split fibre point over an etale finite-type neighbourhood.
- lem-trf-nodal-family-split-point-neighbourhood vs lem-trf-valuation-symmetric-nodal-blowup: existing constructs a symmetric nodal blowup over a valuation ring; this child selects a rational split fibre point over an etale finite-type neighbourhood.
- lem-trf-pointed-etale-diagram-pullback vs def-sfb-nodal-branch-scheme: existing defines the graph-exceptional branch construction; this child transports any supplied etale diagram, without a singular subscheme or blowup.
- lem-trf-pointed-etale-diagram-pullback vs lem-sfb-dvr-nodal-chart-blowup-calculus: existing computes singularities and blowups of fixed DVR equations; this child transports arbitrary etale diagrams and a point with no DVR assumptions.
- lem-trf-pointed-etale-diagram-pullback vs lem-sfb-nodal-branch-double-cover: existing constructs and compares a canonical branch cover; this child transports arbitrary etale diagrams without any branch cover.
- lem-trf-pointed-etale-diagram-pullback vs lem-sfb-persistent-node-normalization: existing constructs a normalization/conductor pushout over a trait; this child transports arbitrary etale diagrams with no normalization or projectivity.
- lem-trf-pointed-etale-diagram-pullback vs lem-trf-formal-local-structure-nodal-family: existing constructs a formal nodal equation; this child transports an already existing arbitrary algebraic diagram and its specified point.
- lem-trf-pointed-etale-diagram-pullback vs lem-trf-nodal-etale-chart: existing constructs marked/log-compatible nodal charts and uses the parent; this child only transports any existing etale diagram without log or marking data.
- lem-trf-pointed-etale-diagram-pullback vs lem-trf-nodal-family-etale-local-model: parent constructs a nodal model; this child assumes a complete etale diagram and transports it through arbitrary base change and open restrictions, without any nodality hypothesis.
- lem-trf-pointed-etale-diagram-pullback vs lem-trf-nodal-generic-component-closure: existing proves closure and boundary properties of nodal components; this child transports arbitrary etale diagrams without components or valuation assumptions.
- lem-trf-pointed-etale-diagram-pullback vs lem-trf-nodal-log-regularity: existing concludes log regularity for marked nodal families; this child transports any supplied etale diagram without log structures or nodality.
- lem-trf-pointed-etale-diagram-pullback vs lem-trf-ordered-nodal-branch-overlap: existing compares labelled branch ideals on generic overlap points; this child transports an entire arbitrary etale diagram and its marked point.
- lem-trf-pointed-etale-diagram-pullback vs lem-trf-valuation-smooth-branches-strict-chart: existing constructs charts of semistable pairs with smooth branches over valuation rings; this child assumes a chart and transports it to arbitrary base change.
- lem-trf-pointed-etale-diagram-pullback vs lem-trf-valuation-symmetric-nodal-blowup: existing changes a curve by blowing up a vertical ideal; this child makes no modification and transports a supplied etale diagram under base change.
- lem-trf-pointed-etale-diagram-pullback vs lem-weil-pbc-base-change-image: existing gives an underlying-set image formula for one fibre product; this child transports all arrows of an etale diagram and their commutativity and functions through two product identifications and open restrictions.
- lem-trf-pointed-etale-diagram-pullback vs lem-weil-pbc-etale-covering-base-change: existing preserves joint surjectivity of an etale covering family; this child assumes only one chosen chart point and transports a compatible model diagram through arbitrary base change and open restrictions, without a jointly surjective family.
- lem-trf-pointed-etale-diagram-pullback vs lem-weil-pbc-surjective-base-change: existing preserves surjectivity of one arrow under base change; this child handles a compatible three-arrow etale chart, two iterated-product identifications, open restrictions, a specified point pair and pulled-back functions.
- lem-trf-split-node-algebraization-finite-type vs def-sfb-nodal-branch-scheme: existing defines a graph blowup branch construction; this child is an algebraization theorem, with no branch scheme in its input or conclusion.
- lem-trf-split-node-algebraization-finite-type vs lem-sfb-dvr-nodal-chart-blowup-calculus: existing computes properties and blowups of explicit DVR models; this child constructs an etale chart from a split node over a general affine finite-type integer base.
- lem-trf-split-node-algebraization-finite-type vs lem-sfb-nodal-branch-double-cover: existing constructs a canonical branch cover; this child constructs a model chart at one rational split point from its completed fibre equation.
- lem-trf-split-node-algebraization-finite-type vs lem-sfb-persistent-node-normalization: existing constructs a projective trait-family normalization; this child constructs a chart for one split completion over a finite-type integer base.
- lem-trf-split-node-algebraization-finite-type vs lem-trf-completed-local-base-change: existing identifies a completion after base completion; this child constructs an algebraic diagram from a split fibre node.
- lem-trf-split-node-algebraization-finite-type vs lem-trf-fixed-family-etale-span-descent: existing descends an already given etale span through an affine inverse limit; this child starts with a split fibre completion and constructs a new etale diagram.
- lem-trf-split-node-algebraization-finite-type vs lem-trf-formal-local-structure-nodal-family: existing concludes an isomorphism of completed local rings assuming a Noetherian stalk; this child verifies that hypothesis from the finite-type base and concludes an algebraic pointed etale diagram.
- lem-trf-split-node-algebraization-finite-type vs lem-trf-nodal-etale-chart: existing constructs marked/log-compatible charts under stronger hypotheses and uses the parent; this child isolates rational-split algebraization over a finite-type integer base, avoiding a cyclic citation.
- lem-trf-split-node-algebraization-finite-type vs lem-trf-nodal-family-etale-local-model: parent starts with an arbitrary nodal family/base; this child assumes an already rational split fibre point and an affine base finite type over Z, isolating the formal-to-algebraic stage.
- lem-trf-split-node-algebraization-finite-type vs lem-trf-nodal-generic-component-closure: existing proves flat component closure and finite boundary over a valuation base; this child algebraizes one rational split node over an affine finite-type integer base.
- lem-trf-split-node-algebraization-finite-type vs lem-trf-nodal-log-regularity: existing concludes log regularity for proper marked nodal families; this child algebraizes a rational split node with no log or properness assumption.
- lem-trf-split-node-algebraization-finite-type vs lem-trf-ordered-nodal-branch-overlap: existing compares labelled branch ideals on overlaps of given valuation-ring charts; this child constructs a chart from a split completion over a finite-type integer base.
- lem-trf-split-node-algebraization-finite-type vs lem-trf-relative-completion-etale-approximation: existing requires a supplied local sigma and completed-base-linear isomorphism; this child constructs them from a rational split node before applying the approximation theorem.
- lem-trf-split-node-algebraization-finite-type vs lem-trf-valuation-smooth-branches-strict-chart: existing gives strict Zariski charts over finite-rank valuation bases with smooth components; this child uses a rational split completion over a finite-type integer base.
- lem-trf-split-node-algebraization-finite-type vs lem-trf-valuation-symmetric-nodal-blowup: existing constructs a symmetric nodal blowup over a valuation ring; this child algebraizes a split fibre completion over a finite-type integer base.

- lem-trf-nodal-family-split-point-neighbourhood vs lem-trf-nodal-point-finite-separable-splitting: the existing theorem gives a finite separable extension and split point of one curve over a field; the new child realizes that extension over the family base by an affine etale neighbourhood of finite type over Z and verifies flatness/local finite presentation of the base-changed family.

## Proof handoff: original argument preserved without shortening

The following is the returned proof verbatim, including its sources and cited-node lists. It belongs to the future workers of the new statement-only nodes as indicated. These are report handoff notes, not proof steps inside their unsplit node files. Old step 1 remains parent step 1 (its forward step number is updated); old step 7 remains parent step 4 verbatim.

### Original step 1 — Parent step 1

Apply [lem-trf-nodal-family-noetherian-approximation] at $x$. Its hypotheses are exactly flatness, local finite presentation, and the geometric-fibre hypotheses here. It gives affine open neighbourhoods $X^\circ,S^\circ$, a Cartesian identification $X^\circ=X_0\times_{S_0}S^\circ$, and a flat finitely presented $f_0:X_0\to S_0$ between schemes of finite type over $\mathbf Z$, with the same geometric-fibre condition. The image $x_0$ of $x$ is nonsmooth for $f_0$. It is enough to construct the required diagram for $(f_0,x_0)$ and then pull it back, retaining a point over $x$ as in steps 8--9.

Uses: lem-trf-nodal-family-noetherian-approximation.

Source: literature/stacks-project/curves.tex; Tag 0CBY, first proof, first paragraph; Tag 0C5F (descent of the nodal condition).

### Original step 2 — lem-trf-nodal-family-split-point-neighbourhood

Write $s_0=f_0(x_0)$ and $k=\kappa(s_0)$. The fibre $C=(X_0)_{s_0}$ is a finite-type $k$-scheme: on a finite affine presentation cover its rings are $B_i\otimes_{R_i}k$, generated by the images of the finitely many generators of $B_i/R_i$ [def-weil-finite-type-morphism]. For every algebraically closed extension $\Omega/k$, the fibre-product universal property identifies $C_\Omega$ with the geometric fibre of $f_0$ at the composite $\operatorname{Spec}\Omega\to S_0$. By [lem-trf-nodal-family-fitting-singular], the first-Fitting singular locus is the nonsmooth locus and commutes with arbitrary base change; applying it to the fibre over $s_0$ shows that $x_0$ is nonsmooth on $C$. Thus [lem-trf-nodal-point-finite-separable-splitting] applies to $C,x_0$, giving a finite separable extension $K/k$ and a $K$-rational split node $x_K\in C_K$ above $x_0$, whose completed fibre ring is $K[[u,v]]/(uv)$.

Uses: def-weil-finite-type-morphism, lem-trf-nodal-point-finite-separable-splitting, lem-trf-nodal-family-fitting-singular.

Source: literature/stacks-project/curves.tex; Tag 0CBY, first proof, second paragraph; Tags 0CBT--0CBW.

### Original step 3 — lem-trf-nodal-family-split-point-neighbourhood

Apply [lem-weil-pbc-etale-neighbourhood-prescribed-residue-field] to $S_0,s_0$ and $K/k$. It gives an étale pointed map $(V_1,v_1)\to(S_0,s_0)$ with $\kappa(v_1)=K$ over $k$. By the fibre-product universal property, $x_K$ gives a $K$-rational point $x_1$ of $X_1=X_0\times_{S_0}V_1$ above $v_1$, split in that fibre. Shrink $V_1$ to an affine neighbourhood of $v_1$ small enough to lie over an affine chart of $S_0$ on which its étale map has a finite presentation. This is possible by [def-weil-etale-morphism] and [def-sbc-locally-finite-presentation]. A finite presentation adds finitely many algebra generators, so the ring of this $V_1$ is a finitely generated $\mathbf Z$-algebra. The map $f_1:X_1\to V_1$ is flat by [lem-weil-pbc-flat-morphism-base-change] and locally finitely presented by clause (3) of [lem-weil-pbc-qcqs-morphism-permanence].

Uses: lem-weil-pbc-etale-neighbourhood-prescribed-residue-field, def-weil-etale-morphism, def-sbc-locally-finite-presentation, lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-qcqs-morphism-permanence.

Source: literature/stacks-project/curves.tex; Tag 0CBY, first proof, second paragraph and reduction to a finite-type base with split node.

### Original step 4 — lem-trf-split-node-algebraization-finite-type

The finite-type-over-$\mathbf Z$ scheme $V_1$ is Noetherian by [lem-weil-pbc-finite-type-over-noetherian]. Its affine section ring $R_1$ is Noetherian by [pqf-lem-affine-open-locnoeth]. At $v_1$ with prime $\mathfrak p$, the stalk identification $\mathcal O_{\operatorname{Spec}R_1,\mathfrak p}\cong (R_1)_{\mathfrak p}$ in [lem-weil-pbc-spec-residue-field-identification], together with [lem-weil-pbc-localization-noetherian], makes $A=\mathcal O_{V_1,v_1}$ Noetherian. Local finite presentation implies locally finite type by dropping the relations in its finite algebra presentation. We may therefore apply [lem-trf-formal-local-structure-nodal-family] to $f_1,x_1,v_1$. Flatness is step 3 and the split fibre node is $x_K$: under the identification $(X_1)_{v_1}\cong C_K$ of step 3, $x_1$ is $K$-rational, hence closed in that fibre, since in every affine open $\operatorname{Spec}B\ni x_1$ the map $B\to\kappa(x_1)=K$ is a surjective $K$-algebra map, so $x_1$ is a maximal ideal there and has no proper specialization (opens are stable under generization). It gives $\widehat h\in\mathfrak m_A\widehat A$ and a $\widehat A$-algebra isomorphism $\widehat{\mathcal O}_{X_1,x_1}\cong\widehat A[[u,v]]/(uv-\widehat h)$, equivalently the completed local ring of $M_{\widehat h}$ at its origin.

Uses: lem-weil-pbc-finite-type-over-noetherian, pqf-lem-affine-open-locnoeth, lem-weil-pbc-spec-residue-field-identification, lem-weil-pbc-localization-noetherian, lem-trf-formal-local-structure-nodal-family.

Source: literature/stacks-project/curves.tex; Tag 0CBX and Tag 0CBY, first proof, third paragraph.

### Original step 5 — lem-trf-split-node-algebraization-finite-type

Set $T=\operatorname{Spec}\mathbf Z[a]$ and $Y=\operatorname{Spec}\mathbf Z[u,v,a]/(uv-a)$ over $T$. The ring map $\mathbf Z[a]\to\widehat A$, $a\mapsto\widehat h$, gives $\operatorname{Spec}\widehat A\to T$. Let $t$ be the image of its closed point and localize to obtain the local map $\sigma:\mathcal O_{T,t}\to\widehat A$. Form $Y_\sigma=Y\times_T\operatorname{Spec}\widehat A$. On rings, tensoring the displayed presentation replaces $a$ by $\widehat h$, so $Y_\sigma=M_{\widehat h}$. Let $y_\sigma$ be its origin and let $y\in Y$ be its image. The completed-model clause of [lem-trf-formal-local-structure-nodal-family] is exactly the $\widehat A$-algebra isomorphism $\widehat{\mathcal O}_{X_1,x_1}\cong\widehat{\mathcal O}_{Y_\sigma,y_\sigma}$ required for relative approximation.

Uses: lem-trf-formal-local-structure-nodal-family.

Source: literature/stacks-project/curves.tex; Tag 0CBY, first proof, third paragraph: the homomorphism sigma and the formal model Y_sigma.

### Original step 6 — lem-trf-split-node-algebraization-finite-type

Apply [lem-trf-relative-completion-etale-approximation] to $X_1\to V_1$ and $Y\to T$, with $x_1,v_1,y,t,\sigma,y_\sigma$ just specified. Both bases are of finite type over $\mathbf Z$, both structure maps are locally finite type, and the isomorphism of completions is over $\widehat A$, as checked in steps 3--5. It gives an étale pointed map $(V_2,v_2)\to(V_1,v_1)$, a morphism $\tau:V_2\to T$, an étale $(U_0,u_0)\to(X_1,x_1)$, and an étale $V_2$-map $U_0\to Y\times_{T,\tau}V_2$. Put $h_2=\tau^*a\in\Gamma(V_2,\mathcal O_{V_2})$. Thus $Y\times_{T,\tau}V_2=\operatorname{Spec}_{V_2}\mathcal O_{V_2}[u,v]/(uv-h_2)$. This is the algebraic smoothing function supplied by approximation; it need not equal the original formal $\widehat h$.

Uses: lem-trf-relative-completion-etale-approximation.

Source: literature/stacks-project/curves.tex; Tag 0CBY, first proof, final paragraph; More on Morphisms Tag 0GDX (lemma-relative-map-approximation-pre).

### Original step 7 — Parent step 4

The map $X_1\to X_0$ is étale since it is the base change of $V_1\to S_0$, by clause (1) of [lem-weil-pbc-etale-base-change-finite-limits]. Clause (2) of [lem-weil-pbc-etale-composition-cancellation] now gives étaleness of $U_0\to X_1\to X_0$ and of $V_2\to V_1\to S_0$. Both triangles commute by the approximation theorem. We have obtained the required chart for $f_0$ and the chosen point $u_0$ maps to $x_0$.

Uses: lem-weil-pbc-etale-base-change-finite-limits, lem-weil-pbc-etale-composition-cancellation.

Source: literature/stacks-project/curves.tex; Tag 0CBY, assembling the diagram for the finite-type model.

### Original step 8 — lem-trf-pointed-etale-diagram-pullback

Define $V=V_2\times_{S_0}S^\circ$, $U=U_0\times_{X_0}X^\circ$, and pull back $h_2$ to a function $h$ on $V$. Since $X^\circ=X_0\times_{S_0}S^\circ$, associativity of fibre products identifies $U$ with $U_0\times_{S_0}S^\circ$ and gives $U\to V$. Clause (1) of [lem-weil-pbc-etale-base-change-finite-limits] makes $V\to S^\circ$ and $U\to X^\circ$ étale and preserves the étale map to $W=Y\times_TV$. The model square is Cartesian by its definition, and evaluation of its affine presentation gives $W=\operatorname{Spec}_V\mathcal O_V[u,v]/(uv-h)$. The open inclusions $X^\circ\to X$, $S^\circ\to S$ and their composites with these maps are étale by clauses (1)--(2) of [lem-weil-pbc-etale-composition-cancellation].

Uses: lem-weil-pbc-etale-base-change-finite-limits, lem-weil-pbc-etale-composition-cancellation.

Source: literature/stacks-project/curves.tex; Tag 0CBY, first proof: pull the finite-type-model diagram back to the original affine base.

### Original step 9 — lem-trf-pointed-etale-diagram-pullback

It remains to retain a point of $U$ over the originally prescribed $x$, rather than merely one over $x_0$. The field map $\kappa(x_0)\to\kappa(u_0)$ gives a surjective map $\operatorname{Spec}\kappa(u_0)\to\operatorname{Spec}\kappa(x_0)$ because both spectra have one point. Its base change along $\operatorname{Spec}\kappa(x)\to\operatorname{Spec}\kappa(x_0)$ is surjective by [lem-weil-pbc-surjective-base-change], hence has a point. By the residue-point maps and the fibre-product universal property this scheme maps into $U_0\times_{X_0}X^\circ=U$, and that point maps to $x$ in $X$. Together with steps 7--8 this proves every requested map, commutativity, étaleness and the point-existence clause.

Uses: lem-weil-pbc-surjective-base-change.

Source: literature/stacks-project/curves.tex; Tag 0CBY, conclusion after base change; Morphisms Tag 01S1 (surjectivity under base change).

## Unfinished work and validation

The three new nodes are intentionally statement-only and join the parallel queue; their proofs are not claimed complete. The parent split is complete relative to those interfaces. The server-only review_split probe passed before this report was written. Full deliver.py --no-push and push results are recorded below after execution. No compiler, Lean build, Lake command or repository write was used.

Full dry run: `deliver.py O4 lem-trf-nodal-family-etale-local-model --no-push` exited 0 and printed `OK (not pushed)` at commit `5dff3f030f1`, with server preflight passed. The proof has 2712 characters in five steps; three new unsplit nodes, zero new Mathlib leaves. The subsequent push reruns preflight.
