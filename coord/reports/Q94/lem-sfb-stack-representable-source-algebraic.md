# Stage-1 delivery: lem-sfb-stack-representable-source-algebraic

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-stack-representable-source-algebraic.json: split the item without changing its statement; Mathlib searches found scheme representability and abstract stack definitions, not this theorem.
- dag/nodes/sec-six-functors-basics/lem-sfb-relative-sheaf-fibred-descent.json: one new statement-only lemma, unsplit; no Mathlib match after LeanSearch, two LeanFinder phrasings, Loogle and source grep.
- citations.json: every step/node pair, quoting the cited statement verbatim.
- searches.jsonl: unedited search-command log.

## Attachments

None. Searched WeilConjectures for the blueprint id, algebraic stacks, representable algebraicity and faithful relative-sheaf descent; no finished project declaration states this item. No Lean file was written or compiled.

## WANTED

None. All proof sources used here are in literature/stacks-project.

## Problems checked and corrections

The item statement is correct; no STATEMENT-DISPUTED change is needed. It allows algebraic-space fibres and does not assume the source is a stack. The existing lem-sfb-representable-fibred-category-stack only allows scheme fibres, so applying it would have been C4. Its proof mentions the general relative-sheaf lemma, but its statement does not provide that lemma. The new node states that missing generic descent theorem without any geometric representability hypothesis. It is not a restatement of the item's algebraicity clause.

Stacks 05UM assumes stacks initially; 05UN removes that assumption by 0CKJ. The delivery proves its hypotheses before using 0CKJ, then constructs the diagonal and smooth scheme atlas explicitly. It uses the existing 02YS presheaf-over-space bootstrap instead of extracting the entire smooth-cover algebraicity theorem (which would hide most of the item's work). The finite-presentation clause uses the expressly existential atlas convention of the item, so no independence-of-atlas theorem is smuggled in.

The inherited blueprint ancestor is null: tools/blueprint_refs.py ancestor prints None. I retained that computed value and the supplied via chain, extended by the item for the new node, and specified the exact supporting place. Read literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its direct-images proof. The latter's current (3) is the direct-image stability argument. The inherited place records the deeper alteration/moduli route underneath it; this delivery only supplies that route's representable-source algebraicity input.

## Not duplicates

lem-sfb-relative-sheaf-fibred-descent vs lem-sfb-representable-fibred-category-stack: the existing statement assumes each scheme-test fibre is represented by a scheme; the new lemma assumes only fibrewise faithfulness and sheafness of relative isomorphism classes, with no representability. The existing proof uses 0CKJ but its statement does not state the general theorem needed here. The new statement includes algebraic-space relative fibres through their sheaf property, whereas the existing statement cannot be applied to them.

Whole-DAG tag and concept searches and blueprint searches for 0CKJ, relative sheaf, faithful and representable found no node stating this general descent criterion. No matching node exists in the latest blueprint either. The open-substack algebraicity lemma is only a special case of the item, not a proof input. The general fppf algebraicity bootstrap cannot be used here as a shortcut: its proof depends on the open-stack theorem and hides the diagonal work.

## Review by Q94

I read algebraic.tex Tags 02ZY, 05UN, 05UM, 045G and the smooth-cover algebraicity proof immediately preceding 05UM; stacks.tex Tag 0CKJ including both descent arguments; stacks-morphisms.tex Tags 06Q2 and 06Q3; and bootstrap.tex's definition of representability by spaces and the 02YS statement. The new lemma is exactly the big-etale-site specialization of 0CKJ. Reversing its structural isomorphisms accounts for the orientation chosen in its statement. It contains no proof sketch or postponed data construction.

For step 1 I checked def-sfb-stable-pointed-moduli-groupoids: its explicit triple objects and arrow equation imply that an automorphism with trivial j-image is an automorphism of a relative fibre triple. A discrete algebraic-space representative has only identity automorphisms, so faithfulness follows. The same equivalence gives the presheaf of relative classes, naturally under restrictions. def-trf-algebraic-space explicitly requires an fppf sheaf. def-weil-etale-morphism defines etale as flat and locally finitely presented (with unramifiedness), and def-pc-fppf-site defines fppf covers by precisely these two conditions and joint surjectivity. Thus etale covers are fppf covers directly from the cited definitions. This is elementary; no flatness theorem is being used implicitly.

For step 2, def-sfb-algebraic-moduli-stack supplies etale descent for Y. The new lemma's faithful functors and all relative sheaves have been verified for every test scheme, not just atlas schemes. It therefore supplies both arrow and object descent for X without assuming it initially.

For step 3, def-sfb-algebraic-moduli-stack supplies the target diagonal space B. The triple-to-ba^{-1} formula gives the Isom interpretation directly from def-sfb-stable-pointed-moduli-groupoids. For a scheme H mapping to B, its specified alpha defines two sections of the space A supplied by the item's hypothesis. def-trf-algebraic-space makes the equalizer of these sections a scheme by its representable diagonal. An arrow between the two triples is exactly beta with j(beta)=alpha; there is at most one by step 1. This checks both existence and uniqueness, not only a bijection on geometric points. The equality test is compatible with every restriction. def-trf-scheme-algebraic-space makes the resulting scheme an algebraic space. lem-sfb-presheaf-space-target-bootstrap states exactly that arbitrary presheaf scheme tests over an algebraic-space target suffice, with no initial sheaf hypothesis. I verified its hypotheses with target B and presheaf P, retaining the structural map to T when considering it on S-schemes. There is no implicit extension of a small-site sheaf to the big site. The displayed triple formula then checks the actual diagonal scheme tests for X. All of this is one explicit fibre-product argument, not an unproved comparison lemma.

For step 4, the algebraic-stack definition provides a scheme atlas V of Y, and the item's hypothesis provides the space A after base change by V. lem-sfb-fibred-groupoid-representable-smooth-calculus explicitly permits arbitrary fibred groupoids with no stack or diagonal hypotheses; its base-change, etale-implies-smooth, chart-comparison and composition clauses give exactly the properties used. The chart U exists by the algebraic-space definition. Steps 2 and 3 plus that atlas meet the complete definition of algebraic stack, including the diagonal, not just existence of a cover.

For step 5, the extra hypothesis lets us choose V with locally finitely presented composite to S; no arbitrary prechosen atlas is assumed to have this property. The item's chartwise hypothesis on A -> V applies directly to U -> A. lem-sbc-locally-finite-presentation-composition states composition for the two scheme maps U -> V and V -> S, exactly the objects in use. Its Mathlib status is already recorded in the live DAG. The resulting U -> X is the smooth surjective atlas already constructed, so its structural composite witnesses precisely the requested clause.

I tested the statement and new lemma on empty source and empty base, identity maps, discrete sheaf maps and schemes; no nonemptiness, Noetherian, separation, finite type or DM assumption is needed. A faithful map to the terminal stack illustrates why relative classes must be sheaves: an arbitrary nonsheaf presheaf would otherwise give a counterexample. With the sheaf assumption, the result is effective descent for a discrete sheaf, as expected. A non-scheme algebraic-space source over a scheme illustrates why the older scheme-fibre descent node is insufficient. The atlas construction works for non-separated spaces as well. Each proof step is below 2000 characters. I checked B1-B10 (statement-only new node, introduced objects/definitions, TeX, tag-label sources, actual searches, blueprint and attachment search), C1-C8 (each non-elementary input is a cited statement, no use of another node's proof, no circular or off-route dependency), D1-D5 (the item carries the diagonal and atlas arguments) and E1-E7 (hypotheses, orientations and restriction compatibility).

No statement or unit route changed. No SGA source is used. No new Mathlib leaf is claimed. The presheaf-over-space bootstrap is listed as a generic tool in split_report.tool_uses; it does not replace the unit's geometric route.

## Unfinished work

The new node is deliberately unsplit, as required for a one-level split. Its source proof is 0CKJ: glue image arrows in G and use separatedness of P_y to lift them, then glue image objects in G and their relative classes using sheafness of P_y; faithfulness forces the lifted transition arrows to be the given ones. The new node's future worker can read this proof in stacks.tex. There is no unfinished part of the item's five-step argument.
