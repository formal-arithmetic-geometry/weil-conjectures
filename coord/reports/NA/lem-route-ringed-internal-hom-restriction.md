# Stage-1 report: lem-route-ringed-internal-hom-restriction

## Files written

- dag/nodes/sec-six-functors/lem-route-ringed-internal-hom-restriction.json: statement, split into two assembly steps; no Mathlib match.
- citations.json: five exact statement quotations for all five step/node citations.
- report.md: this report. searches.jsonl is the search command’s unedited record.

0 new nodes, 0 Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures by the item tag, declaration name and restriction/internal-Hom concepts. The live declaration CategoryTheory.ringedInternalHom_restriction is in lean/Sheaf/Algebra/Homology/RingedInternalHomExactRestriction.lean:392 and its proof ends in sorry. The upstream SheafOfModules.overHomObjIso is an ordinary sheaf-Hom comparison, not this derived assertion; the scheme/open restriction comparisons also do not supply the arbitrary-site statement and its complete coherence clause.

## WANTED

None.

## Corrections and scope

The imported item was a PROVISIONAL machine rendering of a signature truncated midway through the equation. I wrote out the full statement, introducing the ringed site, module-derived categories and their universe/existence hypotheses, both restriction functors, both natural isomorphisms, and the exact comparison equation. I read the complete existing Lean signature, through the final equality, and preserved every mathematical clause. The first input to Hom is contravariant: the transport is H(c_L^{-1},c_M), not H(c_L,c_M). This is completion of a provisional transcription, not a change to the mathematical claim; no false statement or STATEMENT-DISPUTED case was found. The machine’s algebraization.tex source was incorrect: the source is sites-cohomology.tex Tag 08JB, lemma-restriction-RHom-to-U.

The item already has a more general existing DAG theorem covering it, lem-weil-pbc-ringed-internal-hom-exact-restriction. Reusing this statement is the split: no new node merely relabels the item or moves its argument. The explicit comparison equation unpacks that theorem’s successive-restriction clause. The broad theorem’s unrelated tensor-currying, exactness and shift clauses are not used. Its current Lean attachment chiefly records the universe-shift interface and is not evidence that this restriction sorry is proved; the delivery remains stage 1.

## Not duplicates

No new node was created. The existing lem-weil-pbc-ringed-internal-hom-exact-restriction includes this restriction/coherence assertion together with further tensor-Hom and exactness assertions, and is cited directly rather than duplicated. The route item was assigned to account for the specific sorried declaration. A dependency walk through all 247 nodes beneath the cited general theorem found no path to this item. Blueprint searches using “internal Hom”, “ringed internal hom restriction” and “restriction-RHom-to-U” found no imported blueprint node stating this same general infrastructure assertion; the route ancestor is prop-sf-dualizable-hom. The latest ancestor proof’s first paragraph uses local Hom-complex computation, which this infrastructure serves through lem-sf-ringed-rhom-derived-complete. The fixed chapter and unit route are unchanged.

## Review by NA

I read the latest blueprint’s prop-sf-dualizable-hom statement and proof and sk-prop-sf-dualizable-biduality unit, the chapter/unit DAG records, the full live Lean signature/docstring, and the full statement and restriction step of lem-weil-pbc-ringed-internal-hom-exact-restriction. I read Stacks sites-cohomology.tex Tag 08JB (lemma-restriction-RHom-to-U, lines 8934–8945), the preceding construction of internal Hom using a K-injective target, and Tag 08FI (lemma-restrict-K-injective-to-open, lines 4314 onward). Stacks’ proof uses that preservation result; the existing theorem already packages it, so this assembly does not silently cite a mere definition for K-injectivity preservation. I also opened the K-injective restriction, well-definedness, Hom-complex and sheaf-Hom node statements to check the underlying source route. There are no new-node sources to audit.

Step 1 cites the general theorem’s actual statement: it explicitly supplies a natural restriction isomorphism compatible with successive restrictions, without boundedness or finiteness. It does not rely on a construction hidden in that theorem’s proof. Applying it again to C/U is legitimate: C/U is small, R_U is a commutative ring sheaf, and the stipulated derived categories for C/V exist in the chosen universe. def-pur-localized-ringed-site explicitly identifies the double slice with C/V and the restricted ring with R_V. The comparison therefore gives s_f on every pair of objects of D(R_U), as the Lean statement requires, not only on objects coming from D(R). This is the only non-elementary application.

Step 2 cites def-pur-localized-ringed-site for its sectionwise identity of successive restriction and def-weil-pbc-ringed-derived-restriction for the exact-functor-induced derived restriction. These definitions identify c_f with the canonical derived overFunctorMap comparison; the actual Mathlib definition overFunctorMap at PushforwardContinuous.lean:83 is sectionwise Iso.refl, which I read. The theorem cited in this step supplies the equality of the two successive restriction paths. Writing those two paths in order gives exactly the displayed formula, with the inverse on the contravariant argument. This is a short unpacking of a cited statement, so it is marked elementary. It does not assume that an arbitrary unnormalized pair of isomorphisms would be compatible. Every node used in either step has a corresponding verbatim quote in citations.json. No proof step exceeds 2000 characters.

I checked B through E of delivery-errors.md: the statement is self-contained with definition dependencies; TeX has single mathematical escapes; the tag/label are correct; there are no invented Mathlib searches or new nodes; every non-elementary input is cited and each cited statement supplies the indicated fact; no source proof is being mined for unstated claims; no cycle or route replacement is introduced. The off-unit general theorem is explicitly declared as a generic tool in split_report.tool_uses, for the maintainer to judge.

Small-case checks: on a one-object site the identity arrow makes all restrictions and c identity, so the equation becomes e=e. For f=id_U the same normalization holds. Zero complexes and the zero ring make both sides the unique zero-object morphism. On a nontrivial site f need not be a monomorphism: the relocalization C/V = (C/U)/(V/U) is still valid, so no open-immersion hypothesis has been smuggled in. Arbitrary unbounded L and M are allowed by the cited theorem. The equation is typed from r_f r_U H(L,M) to H_V(r_VL,r_VM) on both sides.

Mathlib searches were run only via the mandated msearch.py, and all seven returned result lists were read. Two semantic phrasings, two Loogle queries, a general grep and a module-category grep returned ordinary sheaf Hom, module restriction, its composition comparison and generic exact-derived-functor infrastructure; these do not state derived internal-Hom restriction with the equation. I read the relevant Mathlib overFunctorMap definition and sheafHom construction, and upstream ordinary overHomObjIso. The item is not a Mathlib leaf. The inherited machine grep entry remains labelled as such; all appended search entries match searches.jsonl exactly.

## Unfinished work

None in this stage-1 split. No Lean was written or compiled, no agents were started, and all writes are confined to the item sandbox. Independent maintainer review remains the project’s delivery process.
