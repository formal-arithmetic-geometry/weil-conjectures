## Worker report

Files written: dag/nodes/sec-proper-base-change/lem-weil-pbc-localization-free-resolution.json — statement, split; no Mathlib match for the whole localization resolution. Also citations.json and this report. No new nodes or new Mathlib leaves.

Attachments: none. Searches of WeilConjectures in the read-only slopmaster2 checkout by the blueprint tag, item id, localization, telescope, and free-resolution phrases found no project declaration stating this resolution. The unrelated flat-model free resolution does not state it. The exact upstream master is reference material only.

WANTED: none.

The item has the correct maps and hypotheses of the displayed resolution in Stacks Tag 0997 (algebraization.tex, lemma-hom-from-Af), applied to the slice. It was statement-only; the source asserts the resolution without spelling out its verification. I expanded that verification, keeping the sectionwise power-torsion condition. No statement correction or dispute was necessary. No unfinished portion remains in the split.

Mathlib searches were run through msearch.py and their queries and results appended verbatim by tool and query. The two LeanFinder phrasings found localization exactness and free-sheaf presentation ingredients respectively, not this resolution. Loogle IsLocalization.Away describes localization and its fractions, not the telescope. The first grep had tactic-telescope and unrelated localization-functor hits; the second, restricted to Algebra, found the direct-limit quotient construction and unrelated shift identities. None gives the sheaf resolution in one line. LeanSearch returned Internal Server Error and is recorded as unavailable. Earlier searches on the existing item were retained, not represented as newly run searches.

## Not duplicates

No nodes were created. The whole-DAG 0997 search finds the existing local Hom tower and derived-completeness nodes; these use the resolution but do not state it. Whole-blueprint searches for localization and free resolution found no second blueprint statement of this item (the projective-line graded resolution concerns different objects). The existing general ringed-site sheafification-exact leaf is reused, rather than creating another exact-sheafification node. In particular the similarly named module-presheaf-sheafification-exact node in proper base change is restricted to open sets of a scheme, so it was not used for an arbitrary site; the constant-R presheaf variant was also not used.

## Review by ND

I read algebraization.tex Tag 0997, label lemma-hom-from-Af, including the two displayed maps. Its global section becomes the section f on the ringed slice defined by def-pur-localized-ringed-site. I also read sites-modules.tex Tags 03CY (module sheafification and adjunction) and 03EI (exactness). There are no new nodes whose source requires another review. The source assertion is unchanged, and the proof follows its free-resolution construction rather than replacing the higher unit route.

Step 1 uses the actual statement of def-pur-localized-ringed-site: restricted ring sections at V/U are O(V). The statement of def-weil-presheaf-modules-sheafification supplies semilinear restriction maps and the category of module presheaves. The fraction equivalence relation is written out, so restriction of fractions and both linear maps are checked from formulas, without an uncited localization theorem.

Step 2 is elementary coordinate recursion for injectivity, finite reindexing for QD=0, and the explicit preimage a e_n for every fraction. Invertibility is used only inside R[1/f], never inside R. Step 3 uses the written fraction relation to deduce f^k a=0; it does not wrongly infer a=0. Step 4 writes the finite preimage and checks its last coordinate explicitly. Its sum identity follows by subtracting the two finite sums, and the sectionwise kernel/cokernel universal properties are checked componentwise; no exactness-under-localization theorem is being presumed.

Step 5 cites lem-weil-pbc-ringed-site-module-sheafification-exact, whose opened statement explicitly gives exactness for modules over a ringed site with a varying ring sheaf. Its hypotheses hold on the slice with O_U, not merely on a scheme or with constant coefficients. This is an existing Mathlib leaf in another unit, used as a generic tool; no unit step is replaced. Step 6 uses the adjunction explicitly stated in def-weil-presheaf-modules-sheafification and constructs both directions of the coproduct universal property. It identifies L# by the item's definition. This prevents the false assumption that arbitrary sheaf-coproduct sections have a globally finite support. Every cited statement is copied verbatim in citations.json.

I checked B–E against the completed JSON: self-contained objects and unchanged statement dependencies, exact source tags and labels, actual recorded searches, no new-node relabelling or duplicate, and every non-elementary step covered by its cited statement. Small cases: f=0 gives localization zero and D the identity; f a unit gives the usual augmentation and its difference-kernel; a nilpotent f gives zero localization and the recurrence dies after a power; for R=Z/4 and f=2 the power-torsion factor is indispensable and the constructed preimage still works. The zero ring, zero sequence, support bound N=0, and k=0/M=0 are all covered. No regular-element, flatness, enough-points, or scheme hypothesis was added. The main correction to the initially tempting argument was to retain f^k a=0 and to truncate only after this annihilation, and to identify the coproduct by adjunction rather than by sectionwise equality.


## Second reading by ND

- Item statement: compared hypothesis by hypothesis with algebraization.tex, Tag 0997, label lemma-hom-from-Af, displayed resolution and both maps; PASS. Applying it on the ringed slice introduces exactly the section f restricted from O(U), with no regularity or scheme hypothesis.
- Step 1: read def-pur-localized-ringed-site and def-weil-presheaf-modules-sheafification; checked the fraction equivalence, semilinear restrictions, and finite-support formulas; PASS, elementary.
- Step 2: compared with both maps of 0997; checked coordinate induction, telescoping with the last shifted coordinate included, and the preimage a e_n; PASS, elementary.
- Step 3: checked the fraction relation from step 1 against zero divisors; a/f^N=0 gives only f^k a=0, exactly as used; PASS, elementary.
- Step 4: computed the recurrence and truncation, particularly j=M and M=0; s_M=0 makes the final coordinate equal x_M even when k=0; sectionwise kernel and quotient restrictions give the presheaf universal properties; PASS, elementary.
- Step 5: opened lem-weil-pbc-ringed-site-module-sheafification-exact and compared its exactness clause with sites-modules.tex Tag 03EI, label lemma-sheafification-exact; its arbitrary ringed-site hypotheses hold on the slice; PASS. Also read the pinned Mathlib Presheaf/Sheafification.lean adjunction and finite-limit instances. This existing Mathlib leaf is a generic tool from sk-prop-cd and requires no replacement unit route.
- Step 6: opened the adjunction in def-weil-presheaf-modules-sheafification and sites-modules.tex Tag 03CY, label lemma-sheafification-presheaf-modules; checked both directions of the coproduct correspondence; PASS after spelling out the images of each coordinate inclusion and uniqueness of the resulting maps.
- New nodes: none; B1-B7 and pruning create no obligations. The three proof dependencies were opened, and citations.json contains their actual statements verbatim for each of the four citations; PASS.

Small cases checked independently: the zero ring and empty scheme give zero sheaves; a field with f=0 gives D=identity and L=0, while a nonzero f gives the usual finite-sum relation; nilpotent f and R=Z/4 with f=2 require the retained annihilating power. Bounds N=0, k=0, and M=0 all satisfy the written recurrence. No inference assumes that all sections of a sheaf coproduct have globally finite support.

Independent searches: msearch.py grep on direct sums/exactness/localization and LeanFinder on the cokernel of identity minus successor returned ordinary module direct-limit, cokernel, and coproduct ingredients, not this resolution. Their actual records are in searches.jsonl and their results are appended to the item's mathlib_searches. A read-only search of slopmaster2 by item id, source label/tag, and localization-resolution phrases found no declaration of this statement. Master remains reference material, never proof evidence.

Changes: replaced step 6's compressed map-identification sentence with the explicit formulas D(a e_n)=a e_n-fa e_{n+1}, Q(a e_n)=a/f^n, followed by uniqueness from the coproduct universal property (E5). Recorded independent Mathlib searches. Preserved the correct statement, the other five steps, all dependencies, citations, and the first reader's sections. No new nodes, no new Mathlib leaves, no statement dispute.

Delivery isolation: deliver.py's default clone is the read-only reference checkout. Run the unchanged script with WEIL_CLONE_PREFIX=weil-secondreader-localization, using a separate clone from origin; no git command or write is run in the reference checkout or the live source/launcher.
