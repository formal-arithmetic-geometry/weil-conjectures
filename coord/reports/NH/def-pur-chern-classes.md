# Worker report: def-pur-chern-classes

## Files written

- `dag/nodes/sec-smooth-purity/def-pur-chern-classes.json`: definition, split; no Mathlib match. Seven existing statement dependencies retained; no new nodes.
- `citations.json`: `[]`. This item is a definition with no proof steps, so there are no step citations to quote.
- `report.md`: this report.
- `searches.jsonl`: the four actual NH searches recorded by msearch.py.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for `def-pur-chern-classes`, `chernclass`, `chern_class`, `chern class`, and `chernClasses`, and additionally for Chern/characteristic-class/projective-bundle wording in the geometry and six-functor directories. No declaration defines these finite-coefficient Chern classes. No sorry-bearing upstream master declaration is treated as a completed proof.

## WANTED

None: the cited Stacks source and current blueprint are available locally.

## Corrections and scope

The imported item already had the right mathematical construction and the needed dependencies. Its phrase “basis 1,h,...,h^(r-1)” left the degrees of the coefficients implicit. I wrote the degree-2r, twist-r coefficient map explicitly and defined the classes by the signed inverse coordinates. The statement now explicitly calls F an O_T-module of constant nonnegative rank and specifies ordinary pro-etale cohomology as the full-support case. These clarify the same definition; no statement dispute, extra hypothesis, or new theorem is involved. The old alternating relation and conventions c_0=1, c_i=0 for i>r, including rank zero, are retained.

The original Q80 search records are preserved. The sandbox had no previous node, report, or searches to resume, so the NH log is new. All NH searches were run with the provided msearch command and read: LeanFinder returned topological bundles, differentials, Picard groups, cocycles and continuous cohomology; LeanSearch, a second phrasing of the question, returned free sheaves, local frames, generic Ext/cohomology and Proj structure sheaves. None defines these classes. Loogle's two matches were matcherName declarations; the 12 grep matches were matcherName and Chernoff bounds. No match was promoted to a Mathlib leaf.

## Unfinished work

None for this one-level definition split. Existing dependencies remain responsible for the projective-bundle isomorphism and the other constructions they state. No Lean was written or compiled; no live project or launcher file was changed.

## Review by NH

I read Stacks `weil.tex`, section `section-chern`, Proposition Tag 0FI5 (`proposition-chern-class`), especially the first construction paragraph and `equation-chern-classes`. Its equation is sum_i (-1)^i h^i p^*c_(r-i)=0; reindexing i=r-j and multiplying by (-1)^r gives exactly this item's alternating monic relation. Only that coefficient construction is used here. I do not invoke the proposition's further multiplicativity assertions or silently assume its additional Cartier-divisor axiom. I also read the current main-20261015 ancestor `thm-pur-localized-top-chern.md` and its proof, especially Step 4 (L4), which calls for the ordinary Chern class; the item supplies that definition independently of localized classes or purity. The chapter and unit sk-prop-an were read. This helper is not the unit's key node, so no unit realization fields were changed.

There are no proof steps: the item is a definition and its proof/proof_deps remain empty (B1, C1-C4). I instead checked every statement dependency with its statement open. `def-pur-conventions` supplies A=O_E/varpi_E^n, n>=1, the fixed base field, constant coefficient objects and twists. `def-pur-support-cohomology` explicitly includes the pro-etale kernel-of-restriction construction: taking full support makes the open complement empty and gives ordinary cohomology. `def-amb-finite-locally-free-module` states the Zariski local O_T^r condition used for F. `lem-pur-projective-bundle-tautological-geometry` gives Proj Sym(F), invertible O(1), properness and, for rank one, P(F)=T with O(1)=F. Its quotient convention agrees with Stacks constructions.tex Tag 01OB (`definition-projective-bundle`), which I read along with Tag 01O3 (`lemma-relative-proj-base-change`, including theta on twists) and Tag 01OE (`lemma-projective-space-bundle`). In particular the dual convention would change the normalization, and was not used.

`lem-pur-kummer-additivity` explicitly constructs c_(1,A)(O(1)) in the pro-etale category for the given finite ring, independently of a killing exponent. The projective bundle is a separated finite-type k-scheme: q is proper, hence separated and finite type, and T has those properties. Thus the domain of that Kummer statement is respected. `thm-pur-projective-bundle-formula` is precisely the ordinary pro-etale isomorphism with summands A_T(-j)[-2j] and components the adjoints of powers of that same h, for rank n+1. Apply it with n=r-1. Taking Hom from A_T(-r)[-2r], and using pullback/direct-image adjunction and the invertible twist identifications already specified by the conventions, yields the displayed group map. A finite direct sum gives the finite tuple of coordinates. This uses the existing named isomorphism, not existence of unspecified classes. Finally `def-pur-supported-cup` specifies the product by tensoring the representing morphisms; for both supports equal to the ambient scheme this is the ordinary cup product used in the coefficient map. No property of a supported Euler class or higher-rank purity enters. Since these are statement dependencies of a definition, no off-unit proof tool is being substituted for the unit route.

I checked the degrees explicitly: a_j lies in H^{2(r-j)}(T,A(r-j)), so q^*a_j cup h^j lies in H^{2r}(P,A(r)), and c_i=(-1)^{i+1}a_(r-i) has degree 2i and twist i. Substitution into the relation cancels every a_j with its negative. For r=1, q is an isomorphism and O(1) corresponds to F, so c_1 equals the existing Kummer class. For r=2 the formula gives c_1=a_1 and c_2=-a_0, so h^2-c_1h+c_2=0 has the intended signs. In characteristic 2 the same cancellation works. For r=0 the inverse map is never invoked; c_0=1 and all positive classes are zero. For empty T every group is zero and the unique degree-zero unit equals zero, consistently. Nothing assumes A is a field or flat over Z/ell^N, so ramified E and n>1 remain covered. Singular T and nonsplit vector bundles are allowed by the precise projective-bundle theorem being used.

For B2-B9 and C5/D1-D2 I searched the whole DAG for Tag 0FI5, Chern-class wording and the item id, and searched every imported blueprint with `blueprint_refs.py search 'Chern'`, `'ordinary Chern'` and `'projective-bundle relation'`. The seven broad Chern hits concern trace/Thom constructions or the localized class, not this ordinary graded definition. In particular `lem-pur-chern-flag-formula` is a theorem about these already-defined classes and is not used to define them, preventing a circular splitting-principle dependency. No new nodes were created, so there is no duplicate-pair distinction to make. The blueprint ancestry and the original created fields are preserved; from.place now identifies Step 4 (L4) and the precise Stacks relation. The item remains one definition, with no proof hidden in an unsplit child and no statement longer than a proof step (there are no proof steps to audit under the 2000-character rule). No source on the forbidden SGA route was used.
