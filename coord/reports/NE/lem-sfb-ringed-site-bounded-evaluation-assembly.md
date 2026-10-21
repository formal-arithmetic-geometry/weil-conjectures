# Stage-1 delivery: lem-sfb-ringed-site-bounded-evaluation-assembly

Group NE; 2026-10-21. Direct delivery, with worker self-review and independent maintainer review.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-site-bounded-evaluation-assembly.json`: statement node, now split into eight steps; no exact Mathlib match.
- `citations.json`: fifteen literal quotations covering every node cited by every proof step.
- `report.md`: this report.

No new DAG nodes and no new Mathlib leaves. The search command also wrote `searches.jsonl`; `search-closed-dual.txt` retains the full second semantic-search response. `write_split.py` is sandbox-only preparation code.

## Attachments

None. The exact blueprint tag has no declaration in `lean/WeilConjectures/`. Concept and name searches found `AlgebraicGeometry.boundedOrdinaryEvaluation_degree`, in `lean/WeilConjectures/AlgebraicGeometry/BoundedOrdinaryEvaluationAssembly.lean:58`. I read its whole theorem and proof. It assumes a scheme, an open, and an already supplied chain map satisfying the prescribed block equation; its conclusion is only degreewise invertibility. Our item is on any small ringed site and additionally constructs the chain map, proves its differential formula, specifies both finite-support identifications, and constructs the inverse chain map. It is not an attachment. The more abstract termwise dual construction in `WeilConjectures/Algebra/Homology/Monoidal/Dual.lean` also does not state our internal-sheaf-Hom comparison or its specified identifications.

## WANTED

None. The needed Stacks source files and current blueprint are available locally.

## Problems found and changes

The imported item had a complete, correct statement but no proof. I retained that statement and every inherited source/search/provenance field. Its proof now gives actual reindexing maps and inverse maps, an explicit finite-product-as-coproduct verification, a sheafification-compatible construction on pure tensors, the two nonzero Hom differential components, and the inverse chain-map equation. It uses the existing `lem-sfb-ringed-site-bounded-dual-components` instead of duplicating that calculation or adding another evaluation lemma.

The inherited blueprint location described a “second paragraph, final sentence,” but the current `det-thm-sf-ctf-stability-internal-hom` source has the relevant second isomorphism in a displayed formula and no proof paragraph. I made `blueprint.from.place` name that precise display. `tools/blueprint_refs.py ancestor` returns `None`: the pre-existing `created.item` ancestry ends at a Lean module name. I preserved its null `from.node` and inherited via list, explaining the broken ancestry rather than inventing an ancestor. The mathematical association is the ordinary calculation underlying the displayed coefficient-duality isomorphism. This is a subordinate node, not the unit's key theorem; I changed no unit or chapter record.

No STATEMENT-DISPUTED issue and no source error was found. No extra hypothesis was inserted. The ordinary calculation here is the finite-support part of Stacks 08JJ; K-flatness in Stacks is used to represent a derived tensor, which this ordinary-complex item does not assert.

## Not duplicates

No new node was created. The existing scheme-only `lem-pc-bounded-ordinary-evaluation-assembly`, `lem-pc-ordinary-evaluation-source-biproduct`, and `lem-pc-ordinary-evaluation-target-biproduct` were read and not applied to a general ringed site. They have a scheme/open hypothesis; the first also takes the chain map as data. The sibling `lem-sfb-ringed-site-bounded-dual-components` is cited for its actual projection, support and differential clauses. I did not create ringed-site copies of any finite-biproduct or matrix identity: the short arguments are proof steps.

Whole-DAG searches used Stacks tag 08JJ and finite-support/evaluation/biproduct terms. Whole-blueprint searches included `ordinary evaluation`, `finite biproduct`, `tensor dual`, `bounded complex`, and `tensor-Hom`. No blueprint node states the entire item in another form, so `same_as` remains `[]`.

## Mathlib searches

I retained the four inherited searches and read their results, then ran five searches through the required `msearch.py NE lem-sfb-ringed-site-bounded-evaluation-assembly` command: LeanFinder for the bounded ringed-site evaluation statement, Loogle with `CochainComplex, CategoryTheory.MonoidalClosed`, grep with `homComplex.*[Ee]val|[Ee]val.*homComplex|tensor.*[Hh]om.*[Ii]so`, LeanSearch for bounded module-sheaf tensor-dual/internal-Hom assembly, and a second LeanFinder phrasing using closed symmetric monoidal categories and dualizable terms. Their exact query strings and actual result summaries are in the item and command log. All five services succeeded.

I read the relevant module contractions in Mathlib `LinearAlgebra/Contraction.lean`, the external cochain definition in `Algebra/Homology/HomotopyCategory/HomComplex.lean`, and the tensor-unit construction in `Algebra/Homology/Monoidal.lean`. The returned module-level equivalences are not sheaf-internal Hom complex equivalences; the latter HomComplex consists of external families of category morphisms. The unitors, rigid hom-set equivalences, Cartesian closed sheaves, and evaluation-corepresentability results do not give the map or finite-support identifications asserted here. Thus no exact match or one-line specialization finishes this item. No searches are invented or recorded as unavailable when they actually succeeded.

## Review by NE

I read the complete proof of Stacks Tag 08JJ, `lemma-dual-perfect-complex`, in `literature/stacks-project/sites-cohomology.tex`, especially its last three displays, and the construction and differential in Tag 0A8X, `section-hom-complexes`. I also read the current blueprint file `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-internal-hom.md`, the unit record, and the chapter record. The split follows the ordinary bounded-complex calculation used by the existing ringed-site perfect-duality route. It does not invoke any prohibited SGA route. There are no new nodes whose sources need a separate audit.

For step 1, I opened `lem-sfb-ringed-site-bounded-dual-components.json` and read its statement, not its proof. It explicitly supplies the projection isomorphism, the reversed support, and the sign $(-1)^{q+1}$ in the dual differential under the hypotheses we actually have: an arbitrary bounded complex on a small ringed site with commutative coefficient sheaf. There is no projectivity or exactness hypothesis to discharge. Its additional bidual claim is not used. The citation copies the display and following support clause verbatim. I checked transitively that this node does not depend on our item.

Step 2 uses exactly the direct sum and tensor differential specified in `def-pc-tensor-complex-sheaves`; I read that whole statement. It uses the sheafification definition in `def-pur-sheaf-tensor-product` and the explicitly stated unique factorization in `def-weil-presheaf-modules-sheafification` to discard zero tensor factors. The two maps on coproduct summands are written and both composites are checked there. This is a finite reindexing, not a tensor-distribution theorem or a hidden boundedness hypothesis on $F$.

In step 3, the statement of `def-pur-hom-complex` actually gives the product over all integers, computed sectionwise. The statement of `def-pur-sheaf-hom` gives maps on each slice, so a zero source gives a zero Hom factor. The statement of `def-weil-sheaf-of-modules-category` asserts the category is abelian under our smallness convention. The finite product/coproduct argument explicitly builds $u_i$ and its extension of any family $g_i$, and verifies both identities by projections; it needs no uncited preservation or exactness theorem. I checked that the tensor complex's already cited existence of all direct sums covers our integer indexing and that our finite set is in the prescribed universe.

Step 4 uses the read tensor, sheaf-Hom, Hom-complex, sheafification, and total-complex statements. It defines a map on every object of the slice, including restriction of $y$, rather than treating a global section of a sheaf tensor as necessarily a pure tensor. Balancing and linearity produce a map on the presheaf tensor, and the cited sheafification universal property extends it to the sheaf tensor. Thus the formula is a morphism of sheaves and has exactly the component asserted in the item. Each of those uses has its own verbatim citation entry.

In step 5 I substituted the dual differential already obtained in step 1 into the exact tensor differential quoted from `def-pc-tensor-complex-sheaves`. For $n=p+q$, the target differential quoted from `def-pur-hom-complex` has contributions at $r=-q$ and $r=-q-1$ only. The latter has coefficient $-(-1)^n=(-1)^{p+q+1}$, which agrees with $(-1)^p(-1)^{q+1}$ on the source. The target degree at both components is $r+n+1$, as required. Equality on the presheaf generators suffices by the explicitly cited uniqueness of sheafification, not by an unsupported assertion that all sheaf sections are tensors.

Step 6 reads the block equation directly from our constructed map and the actual maps in steps 2 and 3. It does not infer that any two abstractly isomorphic objects have the same comparison morphism. Step 7 uses precisely the assumption with $M=F^{n+i}$, builds the inverse finite diagonal map, and checks both products. Step 8 multiplies the chain-map identity by those two-sided inverses in the stated order. These are short matrix and composition calculations, so no separate lemma or Mathlib leaf was created for them. Steps 6–8 use only earlier steps and the hypotheses and have no uncited non-elementary premise.

I tested zero $E$, the zero coefficient ring, empty support ($a>b$, forcing every $E^i=0$), singleton support, and targets $F$ unbounded in both directions. Empty products and sums are zero sheaves, so the construction includes the empty case. With $E$ concentrated in degree $i$, the map reduces to the assumed comparison in degree $n+i$. For an explicit sign check, take $E^0=E^1=R$ with differential $1$ and a degree-$-1$ dual element $\phi$: $d_D\phi=\phi d_E$, and at $p=0$ the second Hom component is positive, as the formula predicts; at $p=1$ it is negative on both sides. No step uses finite freeness, flatness, a stalk functor, a scheme structure, or a bound on $F$.

Against delivery-errors B–E: statements and hypotheses were preserved; no new definitions, circular dependencies, clause-restating nodes, unrun searches, or extra source claims were introduced. Every quoted node exists and is unmerged; every cited statement was read and the quoted part supplies what the step takes. The union of the step uses is exactly `proof_deps`. All eight steps are under 2000 characters, and I checked them for an inline hidden lemma regardless of that length. The one non-elementary input, the dual-components calculation, is explicitly a cited existing node. The other steps write out the routine universal-property, bilinearity, finite-matrix, and sign calculations.

## Unfinished work

None in the requested one-level split. The reused sibling dual-components node remains an independently assigned unsplit DAG item. No Lean was written and no compiler, Lake, local preflight, or local DAG/review checker was run. Required validation and delivery are performed by the remote delivery command.
