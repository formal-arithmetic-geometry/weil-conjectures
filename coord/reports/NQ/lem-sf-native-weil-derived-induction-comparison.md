# Stage-1 report: lem-sf-native-weil-derived-induction-comparison

## Files written

- `dag/nodes/sec-six-functors/lem-sf-native-weil-derived-induction-comparison.json`: statement, split into eight proof steps; no Mathlib match for the whole statement. The statement and its four statement dependencies are unchanged.
- `citations.json`: one verbatim quotation for each step/node pair.
- `report.md`: this report. The search log and the sandbox-only writing script are supporting working files, not project changes.

New nodes: **0**. New Mathlib leaves: **0**. All non-elementary input statements already exist. No sibling node, unit, chapter, Lean file, repository or launcher file was written.

## Attachments

None. The exact blueprint-id search and the concept searches in `lean/WeilConjectures` found no declaration proving all clauses. I read the native Category, LowerStar, LowerShriek, OpenImmersion, Adic/Constructible and RightDerivedFunctor/IsoAlgebra sources; their existing generic comparison does not itself prove the free-induction statement on the stated hull. No source declaration containing sorry was treated as finished.

## WANTED

None. The relevant blueprint proof files and Stacks sources are present. The new ordinary-derived assembly is explicitly agent-written, rather than attributed to the blueprint's category of fixed pairs in a derived category.

## Corrections and scope

No statement dispute or target change. The inherited statement is a valid specialization of the existing generic results together with the existing native compact-support coproduct theorem. The original empty proof was filled in. I kept the locally finite coefficient sheaf exactly as defined, allowed covering-member-dependent finite ranks, and retained absence of absolute separatedness. In particular the separated-scheme native open/proper-forgetting node was not substituted for the required general statement.

The blueprint ancestor command returns `None`, consistent with the reviewed sibling `lem-sf-free-derived-weil-resolution`: this chain ends at a maintainer-created seed. I retained `from.node=null` and the precise inherited final exceptional-adjunction place; the current parent records the supplied anchor `lem-a1-local-boundary-duality`. The eight steps realize its derived forgetting/free-induction input without replacing the unit's geometric biduality route. The off-unit lemmas are recorded as generic tool uses in split_report.

I initially tried to quote the word “localizing” from `def-weil-triangulated-subcategory`; reading its full statement showed that it defines only triangulated subcategories. I corrected that citation to its actual triangulated-subcategory clause. Localizing closure and closure under small coproducts are explicitly defined in the item and in the cited free-resolution and compact-support-sums statements. No extra node is needed for that definition. The audit also made the finite-type condition on the compactification's middle scheme explicit using the existing finite-type composition node.

## Unfinished work

None in the requested stage-1 split. Existing unsplit dependencies retain their own obligations. Nothing here claims the underlying Lean proofs have been completed.

## Not duplicates

No new node was created, so there is no new/existing pair to distinguish. Whole-DAG and whole-blueprint searches for Weil induction, induction comparison, fixed pairs, K-injectives and coproducts led to the existing fixed-pair lemmas and `lem-sf-locally-finite-adic-compact-support-sums`, which are reused. The free resolution is not restated as a child of this item.

## Mathlib searches

All six inherited search records were read and retained. I also ran the required msearch command with leanfinder, loogle, grep and leansearch, followed by a second leanfinder phrasing and a grep for the closest search hits. The exact tool/query/result summaries are appended from the genuine `searches.jsonl`; all services answered. I read the returned Mathlib sources: AlgCat/Basic:243 concerns algebra equivalences, Action/Limits:265 concerns preservation for ordinary group-action functors, and Sheaf/Free:184-201 concerns coproducts of the ring unit. None gives a native derived Weil-sheaf comparison, its K-injective normalization, or the orbit-summand formula. Thus none is a whole-item leaf. No unrun search was recorded.

## Review by NQ

I read GOAL.md, the worker/stage rules, the three-level rule, the whole B-E delivery-error checklist, and this node's chapter and unit records. For the mathematical source I read main-20261015 `cor-coef-verdier-weil-equivariance.proof.md` (especially its final exceptional-adjunction sentence), `sk-rem-sf-pf-done/lem-fix-weil-operations.proof.md` (the explicit Frobenius exchange and inverse-square construction), and the integral Brown construction proof used as provenance for the existing native sums node. I also read the source statements of Stacks 079P (`injectives.tex`, theorem-K-injective-embedding-grothendieck), 08BJ (`derived.tex`, lemma-adjoint-preserve-K-injectives), 070Y (lemma-K-injective-defined), 04IE (sites-modules.tex, lemma-localize-ringed-topos), the extension-by-zero exactness lemma there, and 04VG (categories.tex, lemma-properties-left-localization). The native source and these generic sources are used without citing an SGA route. There are no new-node sources to audit.

For step 1, I checked the actual framework definition gives internal modules over the discrete constant Omega algebra with the additional B-action, and wrote out their equivalence with B-module sheaves sectionwise. The ring-sheaf Grothendieck node applies to this B, on the already fixed small site and module universe. The pro-etale isomorphism node supplies reindexing of the site, not a theorem that a nonconstant ring is a constant sheaf: the identity on functions proves the needed coefficient identification. Equivalence-preserves-limits gives exactness and small-sum preservation. Exactness gives the kernel/image cohomology formula. The constructible-pullback node has exactly the same locally finite coefficients and local-rank condition, for arbitrary scheme morphisms. This verifies preservation of C and then of its localizing hull by the written closure argument.

For step 2, I read both the fixed-pair comparison and free-derived-resolution statements. They explicitly supply Grothendieck abelianness, exact conservative forgetting, K-injective preservation, the exact free adjunction and derived small-sum preservation. The functorial-resolution statement applies independently in the two Grothendieck hearts; no bounded-below assumption enters.

For step 3, the weakly-etale-localization statement is used only for the site equivalence. The B restriction equality comes from the framework's functions, so the ringed-slice node really supplies the exact j_! being used. Created kernels and cokernels pass exactness to the fixed-pair lift. The module adjunction is for the actual coefficient map, and I wrote the short Hom universal-property proof of preservation of finite limits. The exact-functor and right-derived-triangulated statements cover both open and proper factors. All hearts have K-injectives by step 2.

For step 4, I opened the common-resolution and normalized-exact-square node statements. They say identity on the shared p_*UJ complex and naturality on homotopy classes, and the latter explicitly supplies a unique natural isomorphism normalized on every K-injective. Their hypotheses r=U_Z, s=U_Y, equality of the ordinary functors on objects and maps, and preservation of K-injectives are satisfied. Exact-derived-natural-iso descends the open identity, so beta has the required normalization, including derived morphisms.

For step 5, I checked the exact-equivalence-square statement says its comparisons commute with both ordinary and derived comparison maps. Its unused left-derived functors may be taken to be zero; the right-derived square is precisely the native Frobenius square. An autoequivalence is conservative and right adjoint to its exact inverse, so the exact-adjoint K-injective theorem applies. The exchange on a K-injective is therefore the ordinary specified exchange. Iteration uses the chosen inverse powers and their cancellation, including negative powers; it does not assume a comparison on fixed pairs of derived objects.

For step 6, the framework supplies the formula p_*(theta) e at the sheaf level. The common-resolution node supplies the actual shared complexes, while the derived-map computation node supplies compatibility with all localized maps and changes of resolution. I wrote the commuting chain equation for the equivariant resolution s. It gives the displayed structure formula under beta by conjugating through the resolution maps. The exact-equivalence-square normalization identifies the exchange used here with that of step 5. This is a computation of the native operations, not an assumption that D(W)=D(A)^P.

For step 7, I checked that exact-derived-adjunction localizes the actual unit and counit, and the free-integer-adjunction statement gives restriction to summand zero and the explicit inverse family. The free-derived-resolution statement gives the n-th counit component and the n+1 shift convention. The Grothendieck-derived-coproduct node says termwise sums, including their coprojections, represent derived sums. The displayed three-term equality then follows by naturality of c_n and the reindexing formula, and computes the very transpose required in the statement. I specifically checked n=0 gives F(iota_0), n=1 shifts zero to one, and n=-1 uses the inverse structure and shifts zero to minus one.

For step 8, I read the complete native compact-support-sums statement: it is on the ordinary derived localizing hull with exactly these locally finite continuous coefficients, for separated finite-type morphisms and with no absolute-separatedness requirement. Base-change nodes verify lft and quasi-compactness of X,Y, separated finite type of f, properness of p and openness of j. Proper p_0 is finite type, and the finite-type-composition node verifies Z_0 and Z are finite type. Only the family (P_X^n A) in L_X is used, so the proof does not demand whole-ambient preservation of coproducts. Universal-property equality of coproduct maps identifies the computed transpose with a composite of two isomorphisms. Derived conservativity from the free-resolution statement then detects the isomorphism in D(W_Y).

I checked every cited statement in full and every quote in citations.json against its literal statement. All non-elementary claims have named cited nodes; the remaining arguments are the explicitly written sectionwise identification, universal-property calculation, closure argument and counit calculation. The statement-only/duplicate/clause tests produce no new nodes. No step exceeds 2000 characters or hides a new lemma behind “standard”, “transport” or “similarly”. Small cases checked: zero A, empty schemes, identity and zero open functors, identity compactification p=j=id (the comparison reduces to the identity on every free summand), P=id with a nontrivial Weil automorphism (the counit is theta^n, so negative n needs the inverse), and complexes unbounded in both directions. The use of K-injectives and termwise Grothendieck sums is valid in the last case. No extra absolute separatedness, uniform local rank, finite coefficient field or constructibility of the infinite free sum was used.

The standalone server review_split check passed before the final source-audit clarification about the finite-type middle scheme. The required complete dry run is run on the final files before delivery.

The first complete dry run requested longer literal citation excerpts for eight entries (the minimum is 40 characters). I expanded those excerpts in citations.json from the already-read node statements; no proof or statement was changed.
