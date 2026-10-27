## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-etale-local-infinitesimal-lifts-smooth.json: statement, split; statement and statement dependencies unchanged; six explicit steps, all existing nodes; Mathlib verdict no match.
- citations.json: one verbatim statement quotation for every step/node pair.
- searches.jsonl: actual msearch.py output log for the item; five fresh searches, two semantic phrasings, Loogle and Mathlib grep.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, infinitesimal lifting, formal smoothness, and lift sheaves. FormallySmooth.lean defines the global lifting property; it does not prove this implication. EtaleShortExactLocalLift and EtaleInverseImageLiftingTorsor concern lifts of sheaf sections, not lifts of scheme morphisms. No project declaration found with every clause of the item and a finished proof.

## WANTED

None. Every source used is in literature/stacks-project. No SGA source is used.

## Problems found and changes

The item arrived unsplit, with no proof. The statement is true as written, so there is no STATEMENT-DISPUTED correction. There is already an exact duplicate statement in the reviewed lem-per-etale-local-infinitesimal-lifts-smooth (2026-10-19). I checked its statement word for word against the item and reused its six-step proof route and existing support. I did not create another lift-torsor lemma or a node restating the item, and did not edit the duplicate. The maintainer may consolidate these exact duplicate item statements separately; this delivery makes the present item reviewable under its own id.

The blueprint ancestor command returns None because the created.item lineage eventually reaches a Lean module name. The inherited from.node null, place and via are retained. I read the current latest six-functor stability unit and direct-images proof (3). That paragraph now assembles open/proper images, not the entire historical alteration/moduli route recorded in this item's place. The immediate mathematical use survives explicitly in lem-sfb-fppf-stack-algebraicity-bootstrap Step 5. The split_report distinguishes that historical lineage from a current blueprint quotation. No chapter or unit field is changed.

The last paragraph of Stacks 04AM writes Omega_{X/S} in its finite-presentation sentences although the displayed acting module uses Omega_{X/Y}; its hypothesis is that X -> Y is locally finitely presented. The scheme support node correctly uses the relative module Omega_{V/W}. This is a harmless relative-base notation slip in the cited paragraph, not a reason to assume X -> S is locally finitely presented. The supporting node's finite-presentation hypothesis is exactly the one available here.

## Unfinished work

None for the one-level split. Existing supporting nodes remain future DAG work according to their recorded statuses; this delivery does not claim their proofs are complete.

## Not duplicates

No new nodes were created. The exact existing duplicate lem-per-etale-local-infinitesimal-lifts-smooth was found before writing; its supporting lemma lem-per-etale-local-lift-torsor-quasi-coherent is cited rather than recreated. The reviewed algebraic-space generalization lem-sfb-space-infinitesimal-lift-pseudotorsor was also read: it is a broader alternative interface, not another node to create. The scheme-specific interface avoids introducing algebraic spaces into this scheme criterion.

## Searches read

I read all five fresh search results, which are recorded exactly in searches.jsonl and appended to the item's inherited mathlib_searches. Both semantic phrasings return scheme Smooth/IsSmooth, affine chart criteria and etale instances. Loogle returns Algebra.FormallySmooth and its ring-level consequences. LeanSearch additionally returns RingHom.smooth_def and Algebra.FormallySmooth.exists_lift. The Mathlib grep returns formallySmooth_stalkMap_iff and SmoothFiber. I read Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean (the Smooth definition, affine chart criterion and stalk criteria) and Mathlib/RingTheory/Smooth/Basic.lean (exists_lift and iff_comp_surjective). These take global algebra lifts or formal smoothness as input; they do not assert that an etale-locally nonempty scheme lift sheaf has a global section. None is an exact or one-line specialization for the item. The online search index uses older IsSmooth names; the pinned local source has Smooth and deprecated aliases. No unavailable service was recorded as a negative result.

DAG searches included tags 061A, 061C, 03P2, 02H6, 04AM and the words sheaf of lifts / torsor / quasi-coherent. Whole-blueprint searches with blueprint_refs.py for 'formally smooth' and 'infinitesimal' returned the smooth definition and related general blueprint nodes, and no blueprint node stating this precise local-lift criterion. Thus same_as stays [], while the non-blueprint duplicate above is explicitly reported.

## Review by Q144

I read delivery-errors B through E whole and checked the actual statements, not proofs or node titles, for each citation. For the item I read spaces-more-morphisms.tex Tag 04AM (lemma-smooth-formally-smooth), including the pseudotorsor argument (I)--(II), and Tags 061A (lemma-sheaf), 061C (lemma-action-sheaf), 061D (remark-special-case). I also read more-morphisms.tex Tag 02H6 (lemma-smooth-formally-smooth), etale-cohomology.tex Tag 03P2 (theorem-zariski-fpqc-quasi-coherent), and sites-cohomology.tex Tag 03AJ (lemma-torsors-h1). The proof follows the two-step local-nonemptiness/vanishing argument of 04AM: the present hypothesis directly supplies part (I); it does not deduce local lifts from smoothness and then use them to prove smoothness. There are no new nodes needing additional source review.

Step 1 uses lem-per-etale-local-lift-torsor-quasi-coherent. Its statement gives exactly a quasi-coherent module H on T, the etale sheaf L of the compatible scheme lifts, and the natural simply transitive action conditional on a section. All its hypotheses hold: f is locally finitely presented, i is square-zero, and fa0=bi. Importantly H is the direct image to T of Hom over O_{T0}; no unjustified identification of cohomology on T and T0 occurs. The cited lemma asserts no existence of lifts, so it is strictly smaller than the item.

Step 2 uses the general abelian-sheaf clause of def-sc-gm-torsor, not only its G_m clause. The assumed a_j satisfy precisely the equations defining L(T_j). On every further object over T_j, naturality and the orbit bijection of Step 1 give the translation trivialization. The given jointly surjective etale family therefore makes L a torsor. This is an elementary application of that action and definition, not a hidden descent theorem.

Step 3 uses lem-sc-etale-affine-qcoherent with X=T, F=H and q=1. Its statement permits an arbitrary affine scheme and quasi-coherent module; there are no Noetherian, finite rank, curve or coefficient-ring restrictions. T is affine by the test problem, H is quasi-coherent by Step 1, and its associated etale sheaf is exactly H_et, so H1=0.

Step 4 uses lem-sc-torsor-h1, whose statement is for any scheme and any abelian sheaf and explicitly sends zero to the trivial torsor. Hence the torsor has trivial class and is isomorphic to H_et. Pulling the zero section back across that isomorphism gives an element of L(T), which by its defining set means a scheme map a with fa=b and ai=a0. The existence of that section is written out rather than hidden in 'trivial torsor'.

Step 5 uses def-sbc-formally-smooth: the arbitrary test problem fixed in Step 1 is exactly its affine first-order thickening over W, with structure map b and the compatibility fa0=bi. The constructed a gives both required triangles. Step 6 uses def-sbc-smooth-morphisms, whose statement defines smoothness as local finite presentation plus this formal smoothness. Both properties are available, so this last step is elementary and is not an uncited theorem about a differently defined Smooth predicate.

All six step/node pairs have full verbatim statement quotations in citations.json. proof_deps is the union of uses. The three generic tool uses are declared in split_report.tool_uses: the scheme lift action, affine quasi-coherent vanishing, and arbitrary abelian torsor-H1 classification. These are foundational tools, not a use of a perverse or curve theorem to replace the six-functor unit route. Definitions are allowed across units. No proof step exceeds 2000 characters (largest 526), and no step moves the content to a new node.

Small cases checked: if I=0, the prescribed map already is the lift, H=0 and L is a singleton. For V=A^1_W, the action is addition by the square-zero ideal and the argument recovers affine coordinate lifting. For an etale f, the translation module is zero; locally existing lifts are unique and the torsor argument yields their global lift. For empty T, L(T) contains the unique map and the same conclusion holds. The affine hypothesis on T is essential for the H1 argument and is used only where stated. No finite-cover or affine-cover hypothesis on the T_j was inserted. No assertion that the arbitrary quasi-coherent Hom is quasi-coherent without finite presentation was made: the cited support explicitly assumes local finite presentation of f.

The node format retains inherited metadata, statement notions, pointers and blueprint lineage. This delivery writes no Lean, runs no compiler or Lake, and writes only in the designated sandbox. Required dry run and push results are the final delivery checks.
