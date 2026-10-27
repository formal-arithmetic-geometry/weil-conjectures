## Worker report

Q86 split lem-sfb-internal-bar-character-roof-cup at stage 1. The mathematical statement is unchanged. There are five proof steps, no new nodes and no Mathlib leaves. Only the sandbox contains writes; no Lean or compiler/Lake/build command was used.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-internal-bar-character-roof-cup.json — existing statement, now split. It is not a Mathlib leaf. The explicit extension lift and the inverse-cancellation/induction arguments use existing nodes, so creating fresh nodes for these calculations would violate the elementary/duplicate rules.
- citations.json — verbatim excerpts from every statement cited by every proof step.
- report.md — this report and signed self-review.
- searches.jsonl — the unaltered search-command log. write_split.py is a sandbox-only reproducibility helper, not a delivered project file.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for character extension, ordered cup, bar resolution, CharacterExtension, CharacterRoof, and InternalBar. The only relevant ordinary-bar hit is RepresentationTheory/GroupCohomology/CupNonvanishing.lean, which concerns ordinary representations of a commutative abstract group over an ordinary ring and proves a nonvanishing assertion, not any clause of this internal-variable-ring roof normalization. Its proof does not provide an attachment for this item. The project's Sheaf definition def-sfb-condensed-unipotent-class is reused through its existing DAG node, rather than restated as a fresh definition.

## WANTED

WANTED: an exact literature reference for the internal condensed-variable-ring bar/derived-adjunction/ordered-cup normalization beneath paragraph (3), for lem-sfb-internal-bar-character-roof-cup. The current blueprint gives the open-direct-image context, not this calculation. This missing exact reference is retained from the imported item. The proof is explicitly agent-written and takes its non-elementary inputs from existing DAG statements; no source was downloaded and no Stacks tag is claimed to assert the complete internal statement.

## Issues checked and corrections

The imported item had no proof. I supplied an explicit equivariant lift rather than assuming projectivity, and separated the cone-boundary sign from the positive-character-class definition. I checked the live roof-adjunction statement, which now specifies rho_f = -delta for the cone arrow -pr. The resulting signs agree with the imported item's x_a = -delta_a and Phi_1(x_a) = -[a], so no statement correction or STATEMENT-DISPUTED is necessary.

The source document and proof-origin document now name literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, rather than working from an obsolete snapshot. The inherited blueprint.from.node is null: tools/blueprint_refs.py ancestor prints “a node created for lem-sfb-internal-bar-character-roof-cup has blueprint.from.node = None”. The inherited via chain is retained. The place and split_report.blueprint now describe the precise normalization calculations served by the proof. No maintainer field or other node is edited.

## Unfinished work

No unfinished obligation in this item's assembly proof. The existing non-elementary input nodes retain their own status and proof obligations; this delivery does not claim they are Lean-closed.

## Blueprint and route

Read dag/chapters/sec-six-functors-basics.json and dag/units/sk-thm-sf-ctf-stability.json and the current latest direct-images proof, paragraph (3). latest resolves to main-20261023-1620, commit 7284bb09daf97437d544c51882b325f9c52cd345 in COMMITS.txt. The paragraph obtains open direct image from the open-coefficient result. The internal bar branch is existing agent-formulated infrastructure below that result. Steps 1–3 give its character normalization; steps 4–5 give its shifted-roof and ordered-cup argument. This neither replaces a unit step nor changes a chapter or unit statement.

Global blueprint_refs searches for “character”, “cone”, “ordered cup”, “unipotent class”, and “inflation graded” were read. Broad character/cone hits concern other geometric characters or cone constructions; the three specific phrases returned no blueprint node. Whole-DAG keyword searches identified the existing internal-bar-character-lifts, internal-bar-roof-adjunction, internal-inflation-graded-cup, condensed-derived-restriction-calculus, condensed-unipotent-class, and augmented-resolution-extension-cone-lift. I opened the relevant existing statements and use their actual assertions. No new node was needed.

## Not duplicates

No new nodes, hence no new/existing node pair to distinguish. In particular the extension-cone comparison and the graded-cup comparison are citations of their existing nodes; the concrete ell calculation, telescoping inverses and induction remain proof steps rather than duplicate nodes. The ordered-cup parent and the explicit-character-lifts sibling are not used, avoiding a circular proof and avoiding an unwanted special choice of L.

## Mathlib searches

Preserved the item's historical searches and appended exactly the five Q86 commands recorded by msearch.py in searches.jsonl: leanfinder with the character-extension/internal-condensed formulation; loogle with the literal query `"Ext", "comp"`; grep with `cupProduct|cup_product|barResolution|δ₁_apply`; leansearch with the character-one-extensions formulation; and a second leanfinder phrasing about arbitrary shifted chain lifts and Yoneda products. Every service answered successfully; no unavailable service is represented as an empty successful search.

The Loogle query returned unrelated Std.ExtDTreeMap comparison lemmas. The semantic queries returned Rep.barResolution.extIso, ordinary groupCohomology cochain/connecting lemmas, LightCondensed.ihomPoints, and generic projective/injective Ext constructors. Read Mathlib/RepresentationTheory/Homological/Resolution.lean:430–443 (ordinary projective bar resolution); GroupCohomology/LongExactSequence.lean:120–185, especially δ₀_apply at line 145; Condensed/Light/InternallyProjective.lean:42–70 (underived internal Hom over an ordinary ring); and CategoryTheory/Abelian/Projective/Ext.lean:1–125 (projective/K-projective Ext construction). These do not state the internal condensed arbitrary-ring derived-roof normalization or its ordered cup identity, nor give it by a one-line specialization. Mathlib has useful generic infrastructure, but the item is not a leaf.

## Review by Q86

I read the current latest blueprint paragraph (3) with the item and the chapter/unit records open. It only supplies the open-coefficient context. I therefore kept proof_origin.by = agent and retained the WANTED reference rather than attributing the bar sign calculation to that paragraph or inventing a Stacks tag. There are no new-node source statements to audit. The old item statement, including coefficient universes, arbitrary profinite G, arbitrary commutative condensed A, arbitrary allowed cochain lifts, canonical cone convention and all degree-zero clauses, is retained exactly.

For step 1 I opened lem-sfb-condensed-derived-restriction-calculus: its statement explicitly says that forgetting the action detects exactness and that equivariant kernels/cokernels are the underlying ones. This proves exactness of the biproduct extension without assuming sectionwise exactness of an arbitrary sheaf sequence. I also opened lem-sfb-condensed-internal-bar-resolution: its statement explicitly defines A[X] by the free-module adjunction and gives alternating deletion. Those are precisely the inputs to ell[g]=(a(g),1). The checks ell[hg]=h ell[g], p ell=e and ell partial_1=(a(g_1)-a(g_0),0) are written out. They are natural on every profinite test object; no assertion that sections of a sheafified free module are a free module is used. Group multiplicativity of a means a(g_0^{-1}g_1)=-a(g_0)+a(g_1), which does not require G to be commutative.

For step 2 I opened the final clause of lem-sfb-internal-bar-roof-adjunction, not just its title or proof. It states that an equivariant lift ell of e through a short exact extension gives the unique f with if=ell partial_1, with rho_f=-delta for exactly the cone convention in the item. All hypotheses were verified in step 1. A map P to A[1] has only its degree -1 component; hence the assumption on eL identifies that entire map with bar f. This uses every allowed L directly and needs neither a projective resolution nor uniqueness up to homotopy of lifts.

For step 3 I read both the adjunction normalization in lem-sfb-condensed-derived-restriction-calculus and the actual definition statement of def-sfb-condensed-unipotent-class. The latter defines [a] by applying derived invariants to the canonical extension boundary after the invariant unit 1 and shifting down by one. This is exactly the formula for Phi_1(delta_a), since the former node normalizes the transpose by the invariant inclusion and uses canonical shifts. Thus the minus sign follows from step 2. I did not infer this identification merely from a degree-one cohomology class or claim an underived Hom complex computes the derived object. Additivity here follows from the formula R(u) composed with the unit and the cited additivity of R.

For step 4 I opened def-weil-abstract-derived-category, whose statement defines Q as the localization at quasi-isomorphisms and says Q commutes with shifts, and the exact augmentation clause of the internal-bar-resolution node. Their statements make every Q(e[q]) invertible. I checked the domains: Q(F_q) goes from Q(P) to Q(P[q]), Q(L_{q+1}[q]) goes from Q(P[q]) to Q(P[q+1]), and Q(e[q]) maps to A[q]. The displayed inserted inverse cancels in that order, producing x_{a_{q+1}}[q] composed with rho_q. This is the elementary inverse/functoriality calculation, not an uncited derived comparison theorem.

For step 5 I opened lem-sfb-internal-inflation-graded-cup. Its statement sends the identity to the unit and gives exactly Phi_p(x) cup Phi_r(y) = t_{p,r} Phi_{p+r}(y[p] composed with x), in the order used here, and declares the signs coefficient/group/arrow independent. I checked q=0 and q=1 separately before the q>=1 induction; the recurrence T_{q+1}=T_q t_{q,1} never silently uses a nonexistent T_0 recursion. The two minus signs at q=2 cancel, giving [a_1] cup [a_2] = t_{1,1} Phi_2(x_{a_2}[1] composed with x_{a_1}). No swap of characters or graded commutativity is used.

Small cases: for trivial G every additive character is zero, ell[g]=(0,1) is equivariant and the extension is split; the augmented map and x_a vanish, consistently with both formulas. If any character is zero, its x_a is zero regardless of L and the iterated roof and corresponding cup vanish for q>0. In characteristic two all displayed minus signs coincide with plus, while the formulas still hold. For A=0 the identity and unit are the zero morphism on the zero object, so q=0 remains valid. As a nonzero check, take finite cyclic G of order 3 and A the constant F_3: ell[g]=(a(g),1) and the differences have exactly the written positive sign. The action/equivariance calculation also works for nonabelian G because a kills commutators. The augmentation exactness is only invoked as a stated input, never promoted to projectivity or Hom-acyclicity.

I checked B–E: the statement introduces its objects and cites its notions; no definition or theorem is newly duplicated; all five search records are genuine command output; each step's cited statement was opened and its relevant words copied verbatim to citations.json; there is no uncited non-elementary comparison, no clause shifted into a fresh node and no circular dependence on the parent. Every proof step is shorter than 2000 characters (945, 637, 931, 825 and 1044 at writing), so no long step hides a separate obligation. The main corrections to the initially empty proof were the explicit equivariant lift, the canonical-boundary-to-adjunction identification, the cancellation formula and the base cases. The required remote dry run is the final mechanical validation before push.
