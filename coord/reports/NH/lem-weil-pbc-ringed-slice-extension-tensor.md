## Worker report

Files written: dag/nodes/sec-proper-base-change/lem-weil-pbc-ringed-slice-extension-tensor.json (item, split; no exact Mathlib match), citations.json and report.md. Zero new nodes and zero new Mathlib leaves.

Attachments: none. The exact blueprint tag is absent from WeilConjectures in the slopmaster2 checkout. Searches for extensionByZero, lowerShriek and projectionFormula find geometric/derived constant-coefficient operations, not this assertion about modules over an arbitrary varying ring sheaf. Master declarations are reference material only. No Lean was written or compiled.

WANTED: none. Read the local Stacks sites-modules.tex, lemma-j-shriek-and-tensor (0E8I, lines 4050-4089), its cited lemma-internal-hom-restriction (0E8H, lines 3774-3784), and the adjunction construction 03DI and tensor-Hom lemma 03EO. The statement is unchanged and agrees with 0E8I; its naturality is supplied explicitly rather than inferred from an unspecified isomorphism.

The item originally had no proof. The split now spells out restriction of internal Hom, the five Hom bijections, inverse isomorphisms, and parameter naturality. The Stacks proof says only “Yoneda lemma”; the inverse and naturality calculations are included as elementary steps, so no general Yoneda node or restatement of the item was created. The source's definition calculation in 0E8H is likewise an elementary step, not a new node.

Nothing remains unfinished in this one-level split. The existing citations remain their own independently managed DAG items.

## Searches and reuse

Whole-DAG searches for 0E8I, lemma-internal-hom-adjoint-tensor, lemma-internal-hom-restriction, internal Hom, restriction, and extension by zero located lem-pur-site-restriction-module-adjunction-exact and lem-pc-sheaf-modules-tensor-closed. I read their entire statements before citing them. The first identifies exactly the sheafification of the direct-sum presheaf used by this item, and gives natural module Hom bijections. The second states the tensor-Hom bijection natural in all three variables on any site with a commutative ring sheaf. Its tensor symmetry supplies the reversed tensor order in the source's displayed chain.

blueprint_refs.py ancestor returns def-weil-pbc-completed-pullback. Searches for extension by zero tensor and 0E8I found no equal blueprint node; projection formula and tensoring an extension searches find lem-trf-open-tensor and lem-cbc-extension-zero-projection-formula, which concern derived constant finite coefficients on geometric open immersions. They do not state this arbitrary-ringed-site underived result. same_as remains []. Chapter and unit records were read and not changed. The proof serves the ancestor's final Stacks comparison through the existing slice-flatness route; the two off-unit statements are declared generic-tool proposals in split_report.tool_uses for the maintainer to review, not an alternate unit route.

All new Mathlib searches were made with msearch.py and copied from searches.jsonl with their exact query text. Two semantic phrasings return Tilde restriction, presheaf tensor, free-module and LightCondensed declarations; their displayed types concern different objects or only the presheaf tensor. The initial Loogle query reports an unknown tensorHomEquiv identifier, not a successful absence test; a second query using SheafOfModules and the quoted tensor substring ran successfully and returned zero hits. Grep with and without the optional subdirectory returned zero hits. LeanSearch returned Internal Server Error and is recorded unavailable. No hit establishes this projection formula, and no leaf is asserted.

## Review by NH

I checked the unchanged statement against Stacks 0E8I: C is an arbitrary site, O is a commutative ring sheaf, U is an arbitrary object, G is an O_U-module and F is an O-module. There is no smallness, geometric open-immersion, flatness, finiteness, stalk or enough-points hypothesis. The localized site and restriction in def-pur-localized-ringed-site, extension presheaf in def-weil-extension-by-zero-presheaf, module sheafification in def-weil-presheaf-modules-sheafification, and tensor definition in def-pur-sheaf-tensor-product are the actual notions used by the statement. No statement dispute arose.

Step 1 uses the literal relocalization clause of def-pur-localized-ringed-site and the formula defining sheaf Hom in def-pur-sheaf-hom. At V over U both sides are maps on C/V, with identical ring action and restriction. Pre- and postcomposition are checked componentwise; this is the elementary definition proof of 0E8H and does not take a theorem from a definition that lacks it.

Step 2 uses the adjunction clause of lem-pur-site-restriction-module-adjunction-exact for the very same sheafified direct-sum extension. Its naturality covers G and the target H. The tensor-Hom clause and symmetry of lem-pc-sheaf-modules-tensor-closed apply on C/U, which is a site with commutative ring sheaf O_U by the existing localized-ringed-site definition. They supply the needed natural bijection, including naturality in the tensor factor F|U. This avoids the ringed-space-only module-tensor-hom-adjunction node and the A-valued tensor-closed node, neither of whose hypotheses would match.

Step 3 uses the inverse forms of those same two cited bijections. The middle comparison is precisely the one constructed in step 1, not a claim hidden in a cited proof. All three types match: G maps to internal Hom on the slice, extension maps to internal Hom on C, and the final group is Hom(B,H). Naturality of each comparison is retained in the composite E. Steps 4 and 5 use only E and its inverse laws/naturality already established: explicit evaluation at identity produces u and v, their compositions are identities, and the parameter equation a u = u' b yields v' a = b v. Thus naturality in both variables is actually proved, not asserted by the word “transports”.

I reviewed B through E: no new-node shape or duplicate issue, statements and formulas are TeX, every non-elementary external fact is a cited statement, every quote in citations.json is copied verbatim from that statement, and no proof of a cited node is used as an extra hypothesis. The new edges go only to generic adjunction tools and definitions, never to slice-restriction-flat or a node above the item. The unchanged statement is self-contained and the source tag was checked in tags/tags. Small cases tested: F=0 and G=0 give the zero isomorphism; an object V with no map to U has an empty direct sum without requiring any nonemptiness; the one-object identity-site case reduces to the ordinary module tensor identity. No new statements were introduced. No correction to the source or unit route was needed.


## Second reading by NH

Item statement: checked against sites-modules.tex, Tag 0E8I, lemma-j-shriek-and-tensor, and its five definition dependencies; PASS, arbitrary site, commutative ring sheaf, arbitrary slice object and arbitrary two modules, without flatness or geometric hypotheses. The isomorphism is the source equality interpreted canonically; its naturality is proved below.

Step 1: checked against 0E8H, lemma-internal-hom-restriction, and the complete statements of def-pur-sheaf-hom and def-pur-localized-ringed-site; PASS, relocalization identifies every component, restriction and scalar action, and pre/postcomposition establishes the required variance. This is elementary from those definitions.

Step 2: checked the first two comparisons of 0E8I against the full statements of lem-pur-site-restriction-module-adjunction-exact (03DI, lemma-extension-by-zero) and lem-pc-sheaf-modules-tensor-closed (03EO, lemma-internal-hom-adjoint-tensor); PASS, the extension is exactly the same sheafified direct sum, and the localized ring sheaf is commutative, so symmetry followed by the stated closed adjunction has the displayed types.

Step 3: checked the remaining three comparisons of 0E8I against the same two cited statements and the explicit comparison from step 1; PASS, both inverse adjunctions have the displayed domains, codomains and naturality. No construction from a cited proof is being assumed.

Step 4: checked against the Yoneda conclusion of 0E8I by evaluating the displayed natural Hom bijection and its inverse at identities; PASS, E(q)=q u and its inverse sends r to r v, giving u v=id_A and v u=id_B. This uses no additional theorem.

Step 5: checked the parameter square using the variance of each comparison in steps 1-3; PASS, both expressions for E(a) yield a u=u' b. Expanded the final composition calculation explicitly to v' a=v' a u v=v' u' b v=b v.

New nodes: none; B1-B9 and new-node Mathlib leaf checks are vacuous. Whole-DAG tag searches recover this item and the existing restriction/flatness nodes, not a missing premise requiring creation. Independent msearch.py grep for sheaf/projection and extensionByZero/tensor returned only three irrelevant comment lines; independent LeanFinder phrasing via left adjoint/restriction/internal Hom returned pullback-pushforward adjunctions and constant-coefficient closed structures, not this projection formula. Read PullbackContinuous.lean's adjunction declarations: they do not assert this tensor comparison. No Mathlib leaf or Lean attachment is claimed.

Edge cases: on the one-object identity site over a field (including zero modules) this is the identity tensor comparison; an empty site has no U and hence no instances of the assertion; empty direct sums at objects with no map to U cause no failure of either adjunction. No statement dispute or statement change.

Citations: all six records in citations.json equal the entire corresponding current node statement verbatim. Each non-elementary step cites the exact two assertions used; elementary steps 4-5 use the Hom equivalence constructed in earlier steps. Traversing the four new proof dependencies shows none reaches the item, so these edges create no cycle.

Pre-existing dependency issue for the maintainer (not changed in this delivery): the extension-adjunction dependency reaches def-weil-pbc-sites-and-cohomology, then lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction, then lem-weil-pbc-sheaf-algebraic-structures-objects and lem-weil-pbc-sheaf-algebraic-structures-abelian-component, whose dependency edges form an existing cycle. This item does not occur in it. Those independently managed nodes were not edited.

Changes: expanded step 5's inverse-composition calculation and clarified that the nested split_report.tool_uses are proposals, not recorded maintainer exceptions. An initial removal of those proposals failed the dry run's route check; inspected tools/review_split.py lines 97-102, which explicitly permits worker proposals there under the human decision of 2026-10-10 evening, and restored them verbatim. The top-level maintainer field was never written. Kept the statement, all other proof steps, dependencies and citations unchanged.
