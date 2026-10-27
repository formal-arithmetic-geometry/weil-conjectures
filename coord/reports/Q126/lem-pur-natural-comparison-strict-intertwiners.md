## Worker report

Files written: dag/nodes/sec-six-functors/lem-pur-natural-comparison-strict-intertwiners.json (existing statement, split; Mathlib ingredients only), citations.json, report.md. The search tool maintains searches.jsonl.

New nodes: none. New Mathlib leaves: none.

Attachments: none. The whole WeilConjectures source was searched for the exact blueprint id, fixed pairs, strict intertwiners and functorOfNatTrans. The closest project file is WeilConjectures/Mathlib/CategoryTheory/Endofunctor/Algebra.lean: mapOfNatTrans, isIsoStr_mapOfNatTrans_obj and IsoAlgebra.mapOfNatIso provide transport and strictness. They do not state the converse equation for arbitrary structure morphisms or the two requested inverse identities, so they do not attach the complete item.

WANTED: none.

The item had no proof. Its statement is correct as written and has not changed. The blueprint's phrase “precomposing the vertical maps preserves the commutativity of the squares” omitted the calculation; this delivery supplies it in both directions, plus the requested inverse calculations. There is no dispute or change to the chapter or unit route. No Lean was written and no compiler, Lake or build tool was run.

Unfinished: no part of the requested one-level split. Independent maintainer review and later formalization remain project work.

## Sources and searches

Read GOAL.md, the three blueprint levels in SETUP.md, the chapter sec-six-functors record, unit sk-thm-sf-package (in particular orientation clause (5) and its assembly), and the current item's source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-pur-weil-equivariance-scheme-frobenius.proof.md, its complete final sentence. Read the parent node to check that its comparison really uses this abstract naturality argument. This is an agent expansion of the blueprint, recorded as such, with no SGA source used.

The existing node's five older Mathlib searches and candidate were retained. Q126 ran LeanFinder twice, Loogle, LeanSearch and grep via msearch.py; the exact commands' query texts and actual summaries are in searches.jsonl and appended to mathlib_searches. The second LeanFinder process completed during a provider interruption: its saved log was inspected instead of rerunning it. Its hits are NatIso cancellation/naturality formulas. The additional grep in NatIso.lean produced malformed file/line display fields, so its actual query and hit summary were preserved, and the source itself was opened to verify the declarations. Endofunctor/Algebra.lean lines 151–200 gives functorOfNatTrans and equivOfNatIso on unrestricted algebras. NatIso.lean lines 45–145 gives component inverse identities and cancellation. These do not directly state the complete item: the iff and specified strict inverse formulas require the explicit substitutions now written as steps. No ingredient is used as an unrecorded non-elementary theorem: cancellation and invertibility are proved directly from the inverse equations in the item.

Searches across dag/nodes for natural isomorphisms, intertwining, fixed pairs and natural comparisons found the existing two definition nodes, the sibling lem-pur-natural-comparison-functor-transport, and lem-fd-frobenius-fixed-pair-comparison. Read the sibling and Fourier comparison statements: the former concerns transport along an additional functor with compatibility data; the latter concerns coefficient equivalences for a geometric Frobenius and finite-stage compatibility. Neither duplicates this abstract iff with arbitrary structure maps. Whole imported-blueprint searches using tools/blueprint_refs.py for “natural comparison”, “fixed pair”, “intertwining” and “naturally isomorphic endofunctors” found no blueprint node stating this item; same_as remains empty. The ancestor command confirms prop-pur-weil-equivariance-scheme-frobenius.

## Not duplicates

No new nodes. The existing item is not duplicated by the sibling functor-transport or the geometric Fourier fixed-pair comparison, for the differences above.

## Review by Q126

I opened the blueprint proof, the item, and both cited definition statements. The source compares the two pullbacks by kappa and says to precompose the vertical arrows. The item's abstract notation takes those comparison isomorphisms as data; its naturality equation has the correctly typed direction G(h) kappa_M = kappa_N F(h). No geometry, coefficient restriction, Cartesian square, or unmentioned hypothesis is needed here. There are no new-node source statements to check.

Step 1 uses def-nagata-category exactly for associativity. I checked its statement explicitly supplies composition and the associativity equation. The other inputs are hypotheses of the item: substitution of u and naturality. The four-term displayed calculation proves the forward implication for arbitrary phi_M and phi_N; no invertibility of phi or h is used. Both composites have source F(M) and target N, and the lower arrow stays h.

Step 2 uses the same category definition and the inverse of kappa_M supplied by the natural isomorphism hypothesis. It expands the assumed F-equation to an equality after kappa_M, precomposes by kappa_M inverse, and writes the cancellation identity kappa_M kappa_M inverse = id on G(M). I checked that this order of inverse maps is the one needed; it yields maps G(M) to N. There is no hidden cancellation lemma and no use of a cited node's proof.

Step 3 uses associativity and identities from def-nagata-category and inverse equations from the stated invertibility hypotheses. I checked v_M has type M to F(M), that v_M u_M is identity on F(M), and that u_M v_M is identity on M. Both products are displayed separately. The quantified replacement of M by N gives exactly the same equations at N when phi_N is invertible. This is a definition-level inverse calculation, not a new lemma moved out of the item.

Step 4 cites def-weil-endofunctor-fixed-pair-category. I checked its statement requires an isomorphism T(X) to X, defines arrows by precisely the item's left intertwiner equation, and says identities and compositions are those of C. Steps 1–3 supply its only requirements for T=F. The assignment h to h preserves identity and composition literally, so it defines the asserted action on fixed pairs without any extra equivalence claim. All cited uses are quoted verbatim in citations.json, one entry per cited node per step.

Against delivery-errors B–E: no new statement-only node, duplicate, hollow notion, or clause relabelling was introduced. TeX is serialized once. The definitions are actual statements read above, not borrowed proof constructions. No off-route theorem, circular parent citation, or external purity theorem appears. Every calculation is elementary and written out, so the elementary flags are justified even though the item as a whole was previously delegated as a lemma. Each step is below 2000 characters and hides no separate claim. I corrected no statement and removed no original search evidence.

For small cases I checked F=G and kappa the identity (the equations reduce literally to the same equation), the one-object terminal category (all inverse equations are identities), and h an identity or a noninvertible arrow (no inverse of h occurs). Noninvertible phi maps still satisfy the iff, with the inverse claim correctly conditional. The empty category has no M,N and the universally quantified assertion is vacuous. No size/smallness hypothesis is used by a limit construction or category of diagrams.
