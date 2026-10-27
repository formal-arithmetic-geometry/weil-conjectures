## Worker report

Files written: `dag/nodes/sec-smooth-purity/lem-sf-cbc-coefficient-linear-projection-descent.json` (statement, split into seven steps, no Mathlib match), `citations.json`, and this report. The sandbox also retains the actual search log and a sandbox-only generation script. No repository, launcher, or Lean source was written and no compiler was run.

## New nodes

None. Zero Mathlib leaves were added. The nine proof dependencies already exist in the live DAG.

## Attachments

None. I searched `lean/WeilConjectures/` for the item's blueprint tag, coefficient-linear projection/descent names, and the scalar-extension/projection notions. Existing finite constant-coefficient scheme projection files do not give this arbitrary small ringed-site statement with its supplied eta and kappa. No project declaration stating every clause was found.

## Sources and searches

No WANTED document. Read `sites-cohomology.tex`, Tag 0GL1, label `lemma-j-shriek-and-tensor`; Tag 06YU, `definition-derived-tor` and its preceding construction; Tag 06YS, `lemma-K-flat-resolution`; and Tag 06YY, `lemma-derived-base-change` and its proof. Read the ordinary formula in `sites-modules.tex`, Tag 0E8I, `lemma-j-shriek-and-tensor`, and the direct-sum construction in Tag 03DI, `lemma-extension-by-zero`. The proof is marked agent-written: the supplied-coefficient-linear refinement and representative normalization are not asserted as the verbatim statement of 0GL1.

Read the main-20261015 `fix-lem-exchanges.proof.md`, Steps 1–2, and `lem-cbc-completed-extension-zero-comparison.proof.md`. This item realizes the extension-by-zero coefficient comparison below those steps. It asserts no preservation of countable products and uses no integral completion argument from that latter proof.

Whole-DAG searches by K-flat/resolving/localization titles and statements found the nine existing dependencies; no new statement was needed. Blueprint ancestor lookup returned `fix-lem-exchanges`. Whole-blueprint searches `one-sided tensor normalization`, `projection descent`, and `slice extension` returned no matches; `coefficient-linear` returned `det-sp-tower-classes`, a coefficient-tower classification, not this arbitrary-ring-sheaf projection statement. The broader `derived tensor` results led to reuse of the existing derived tensor infrastructure rather than duplication. `blueprint.same_as` stays empty.

All fresh Mathlib searches used the mandated msearch command, logged in searches.jsonl and appended verbatim in tool/query to mathlib_searches. Both semantic phrasings were read: the first returned Ext linearity and exact derived functor results, the second generic derived-category localization and exact-functor comparisons. Loogle returned `CategoryTheory.Localization.liftNatIso` and its hom/inv lemmas. I read `Mathlib/CategoryTheory/Localization/Predicate.lean`, including fullyFaithfulWhiskeringLeft at line 278 and liftNatIso at line 357, and the derived exact-functor comparison source. These are tools for our localization step, already supplied by existing DAG nodes, not an exact or one-line match to the entire ringed-site assertion. LeanSearch returned ordinary ModuleCat scalar extension/adjunction, sheafification, and unrelated algebra results. The grep of derived/extendScalars/restrictScalars had zero hits. Inherited search records were preserved; no inherited query was represented as freshly executed.

## Problems corrected

The item previously had no proof. Its statement, hypotheses, conclusions, source record, creation record, and blueprint provenance were retained. In particular eta is the GIVEN S-linear natural isomorphism; the proof does not substitute an arbitrary ordinary projection isomorphism. It does not presume that restriction from D(S) to D(R) is faithful. It proves comparison uniqueness by resolving localization instead.

The strict-tower conclusion is conditional as stated: a tower evaluation is identified only when its computation comparisons satisfy the indicated equation. This item does not prove an additional theorem about evaluation commuting with derived functors and does not cite its parent, which would create a cycle.

Nothing mathematical remains unfinished at this one-level split. Existing non-leaf dependencies remain their own items.

## Not duplicates

No new nodes, hence no new/existing pairs with a shared tag. In particular the ringed-open-flat-resolution, site-derived-tensor-descent, and one-sided-tensor-normalization statements are reused, not recreated.

## Review by NZ

I read the statement of each of the nine cited nodes, not just its title or proof. The source comparison above leaves the item's full generality intact: R and S are sheaves of commutative rings on a small site, V is an arbitrary object, and R to S may be nonflat. There is no scheme, constant-coefficient, adic, or boundedness specialization. There are no new statements requiring a separate source review.

Step 1 uses `lem-weil-pbc-site-derived-tensor-descent` specifically for its stated equivalence of the localization of flat-term K-flat homotopy complexes with D(R), applied on the slice. `lem-pur-site-restriction-module-adjunction-exact` states exactness of both slice extension functors, for the actual localized ringed site. `lem-weil-pbc-exact-functor-derived-factorization` supplies natural representative comparisons at EVERY complex. `lem-cbc-ringed-open-flat-resolution` states both K-flat and termwise flat preservation for arbitrary localized ringed sites, so the ambient scalar-extension counit can be used at j!P. `lem-weil-pbc-ringed-topoi-derived-pullback` states its counit is invertible on exactly those complexes and natural in maps. Smallness holds for the slice since its objects and morphisms are formed from the given small site. No open-immersion or quasi-compactness assumption was borrowed from a scheme case.

Step 2 is the sole elementary step. The supplied natural eta, evaluated on each differential, is the chain-map equation. Evaluation on each component of a chain map or homotopy gives naturality and homotopy compatibility, since scalar extension and the exact extension functors are additive. This is two applications of naturality, not a hidden projection-formula lemma.

Step 3 reuses the precise counit and exact-functor natural transformations just checked in Step 1. I checked the orientations: a maps F(QP) to the ambient ordinary tensor; b maps G(QP) to the extended ordinary slice tensor. Thus b inverse, Q(h), a compose in D(S), giving an S-module derived morphism before any forgetful functor is applied. No K-flatness of the changed-coefficient P tensor S_V is needed for b: exact extension computes on every complex.

Step 4 cites the equivalence from site-derived-tensor-descent and the natural-transformation clause of localization-universal-property. The latter explicitly lifts an isomorphism, respects composition, and gives uniqueness, whereas a bare fully faithful Yoneda statement would not suffice. Its inverting hypothesis holds because both restricted functors factor through Q. I wrote the multiplication by inverses of quasi-isomorphism naturality squares to cover localized morphisms; no direct chain comparison between arbitrary resolutions is asserted.

Step 5 uses restriction-derived-products ONLY for exact derived scalar restriction, not product preservation or faithfulness. Exact-functor-derived-factorization computes it termwise; localization-universal-property descends the supplied kappa and its inverse. The one-sided-tensor-normalization statement explicitly allows an arbitrary, possibly nonflat second complex and is natural in homotopy maps of the flat K-flat first factor. These are precisely j!P and P. The ordinary scalar/tensor identification is stated for arbitrary ring sheaves in cbc-extension-tensor-comparison-independent, with the local pure tensor normalization; swapping its tensor factors merely puts the degree-zero scalar in the right-hand position. That is not the constant-ring-only finite-reduction-restrict-tensor node.

Step 6 cites resolving localization and the transformation universal property again, now for the explicitly written x_P and y_P natural isomorphisms. They do not conceal a new general lemma: identifying this scalar restriction with the normalized tensor comparison is a conclusion of the item itself. I checked the type of k at E_V(QP), and the inverse in y_P. Expanding y k U(beta) x inverse cancels k inverse against k, then U(b) against U(b inverse), and U(a) against U(a inverse). The remaining map is Q(kappa h), exactly Q(r_P), between the two ordinary R-complexes. This computation verifies the normalization and explains why no faithfulness of derived scalar restriction is required.

Step 7 uses the same fully faithful descent of transformations on the resolving localization to compare arbitrary natural R-linear transformations. Equality on all flat K-flat representatives suffices; it is not deduced merely from objectwise essential surjectivity. Tower evaluation is used only after the comparison data in the item's hypothesis identify its representative equation. All steps cite the node statements for the facts actually taken; citations.json gives a verbatim excerpt for every uses entry.

For the B1–B10 checks there are no newly created nodes, no new definitions, no purported Mathlib leaf, no duplicate tags, and no unverified attachment. Existing statement dependencies were retained. For C1–C8 I checked the exact contents just listed, avoided the parent dependency, and declared the generic off-unit localization, exact-functor, and tensor tools in split_report.tool_uses, never in maintainer-owned tool_uses. These tools implement the unit's stated extension-by-zero coefficient comparison rather than replacing its route. For D1–D5 the item's steps carry the actual construction and cancellation equation; no new node restates a clause and no omitted-details appeal is left. For E1–E7 I checked coefficient categories and each K-flat hypothesis rather than calling a nonflat scalar sheaf flat.

Small cases checked: the zero complex; S the zero ring sheaf; R=S with the supplied (not necessarily identity) eta; V terminal, where slice extension is the identity up to the specified comparisons; and a nonflat quotient Z to Z/2 on the point site, using the two-term flat complex [Z --2--> Z], where ordinary tensor has the expected extra homology and no exactness of extension of scalars was assumed. Unbounded complexes cause no sum or limit interchange in this proof. Each non-elementary proof step is below 2000 characters, and none hides an additional independent claim requiring a new node.
