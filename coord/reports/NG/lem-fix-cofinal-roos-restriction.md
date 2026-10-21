# Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-fix-cofinal-roos-restriction.json`: statement, split; nine explicit proof steps; no Mathlib match for the complete comparison.
- `citations.json`: 18 entries, one verbatim statement excerpt for every node used by every proof step.
- `report.md`: this report and signed self-review.
- `searches.jsonl`: six searches recorded by the prescribed msearch command, retained without alteration.

There are 0 new nodes and 0 new Mathlib leaves. The existing Mathlib leaf `lem-weil-pbc-homotopic-maps-equal-cohomology` is reused.

## Attachments

None. Searching `lean/WeilConjectures/` for the exact blueprint tag, Roos, cofinal/subsequence language and the relevant Roos modules found no project declaration stating all clauses. The existing Roos comparison maps/homotopies/retract modules concern maps of towers at the same indices; the arithmetic restriction node concerns the more specialized arithmetic reindexing and its derived normalization. Neither is an attachment for this item.

## WANTED

None. All sources used were available locally.

## Corrections and scope

The item's mathematical statement and hypotheses are unchanged. There is no statement dispute. The previous proof was empty. The proof now constructs an actual right inverse of the specified selection/block map and an explicit degree-minus-one homotopy for the other composite, instead of inferring that an unspecified comparison of triangulated cones is invertible.

Let m_n=phi(n), and let nu(i) be the first selected index with i <= m_n. Extend selected source coordinates by E(z)_i=t_(i,m_n)z_n and insert selected target coordinates by J(w)_(m_n)=w_n, with zero elsewhere. Then aE=bJ=1 and delta E=J delta'. For h(y)_i=sum_(j=i)^(m_n-1)t_(i,j)y_j, telescoping gives h delta=1-Ea and delta h=1-Jb. Thus S=(J,E) satisfies CS=1 and 1-SC=DK+KD for K(y,z)=(0,-hy) in the prescribed shifted-cone convention. This finite-block elimination is the argument promised by the item's source metadata.

All original metadata, statement dependencies, blueprint ancestry, and prior Mathlib searches are retained. Six newly executed searches were appended to the existing records; their literal query texts and raw result summaries come from the msearch log. No unit or chapter record is changed: the item is a subordinate tool in the scalar-completion associator, not the unit's key statement. The current ancestor source was read at `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-pf-reduction/lem-fix-operation-reduction.proof.md`, paragraph 3: the comparison serves the transport of specified tensor/adjunction maps to field stages, as the inherited ancestry requests.

## Unfinished work

None in the one-level split. No new lemma has been left to another worker. Server dry run and push are performed after this report is written; their command output determines delivery status.

## Not duplicates

No new nodes were created. I searched the whole DAG for Roos, cofinal subsequences, finite-block formulas and Tag 0941, and the whole imported blueprint with `blueprint_refs.py search 'Roos'` and `search 'cofinal'`. None of those blueprint statements states this full arbitrary-subsequence strict comparison. The nearby `lem-pur-compact-support-roos-cofinality` only treats arithmetic subsequences over a constant coefficient ring and also contains a scalar-tensor clause. `lem-sp-strict-tower-arithmetic-restriction` treats arithmetic subsequences with derived products without assuming product exactness; it does not state the arbitrary strictly increasing map law in the item. Neither is duplicated by a new node, and neither is used as a black box for the argument.

## Review by NG

I read the worker contract, the stage-1 rules, the three-level restrictions of SETUP, GOAL, the item's chapter and unit, and both copies of delivery-errors sections B through E. I checked the item against Stacks Tag 0941 (`sites-cohomology.tex`, `lemma-derived-limit-is-ok`), which supplies the tower product/cone setting, and read Tag 0H9K (`more-algebra.tex`, `lemma-pro-isomorphism-iso-Rlim`) in full for its actual selection map, finite-block target map, composition calculation and finite-block elimination. The latter is the mathematical source of the explicit refinement. I read Tag 0116 (`homology.tex`, `lemma-map-cohomology-homotopy-cochain`) and the reused Mathlib leaf's complete statement, as well as Mathlib `Homotopy.lean:894-904`. The source proof of 0116 is omitted, so the split cites the existing independently stated Mathlib result, rather than treating the omitted proof as an argument. There are no new-node sources to audit. No SGA source is used.

For step 1, I opened `def-weil-sheaf-of-modules-category`, `def-weil-inverse-system`, and `def-weil-strict-roos-model`. They respectively supply the abelian module-sheaf category, the strict transition maps and their composites, and exactly the signed coordinates D(y,z)=(-dy-delta z,dz). Each displayed product map has only finitely many inputs in each output coordinate; the product universal property therefore gives an actual morphism of sheaves. This avoids using sectionwise surjectivity or selecting lifts of sheaf sections.

For step 2, the inverse-system statement defines the composite transitions, and the Roos definition gives the differential used in the calculation. I cancelled all intermediate terms in the finite sum and checked that the last transition ends at m_(n+1), rather than m_(n+1)-1. The resulting square is b delta=delta' a with the order required by the item's cone map. Its two diagonal entries are b on the shifted product and a on the unshifted product.

For step 3, the same two cited statements supply all the objects and coordinates. Unboundedness gives nu(i) for every i, including i<m_1; strict increase gives uniqueness of a selected index and the identity nu(m_n)=n. The transition law gives delta E=J delta' by separate selected and nonselected cases. The finite interval [m_n,m_(n+1)) contains exactly one selected coordinate, so bJ=1 even for irregular gaps. Thus CS=1 is a strict equality, not a derived-category assertion.

For step 4, I reread the inverse-system definition and checked both telescoping identities directly. The nonselected-coordinate case applies also before m_1. At a selected index m_n, h is zero but the next h-coordinate contributes minus the rest of the block; this gives y_(m_n)-(by)_n, with the correct negative sign. The displayed notation z_n^sel is defined there as z_(m_n), so E acts on a selected sequence, not on the original ith coordinate. No convergence claim or infinite sum occurs.

For step 5, I reopened the Roos definition and substituted K(y,z)=(0,-hy) into the signed differential. The terms -dh y+hdy cancel because every transition is a chain map. This leaves precisely (1-Jb)y and (1-Ea)z, hence 1-SC, with source and target degrees k and k-1 as required. The inverse construction and this contraction are written as the item's argument: no new node repeats any clause of the item.

For step 6, the module-sheaf definition states abelianness for the assumed small site. Part (b) of `lem-weil-pbc-homotopic-maps-equal-cohomology` explicitly states equality on every cohomology object for homotopic maps of integer-indexed complexes. I specialize its auxiliary additive functor to the identity and apply it to step 5. It has no boundedness, injectivity or exact-product hypothesis. Together with CS=1 this makes H^k(S) and H^k(C) inverse maps. The derived-category definition explicitly defines quasi-isomorphism by these isomorphisms. Countable product exactness remains an assumption of the item, although the stronger chain-homotopy calculation does not use it.

For step 7, the inverse-system definition states strict naturality for adjacent transitions and componentwise composition; induction on the finite transition string gives the equality for t_(i,j). The product selection equation and each summand of the block equation then commute with f, and the Roos statement gives the diagonal induced maps. Thus the proof checks the actual naturality square at chain level.

For step 8, I checked the composition order is phi after psi. The tower statement gives the transition composite used in each double-sum summand, while the Roos statement supplies diagonal maps whose compositions are componentwise. The nested blocks [m_j,m_(j+1)) partition [m_(psi(n)),m_(psi(n+1))) with no missing endpoints. For identity restriction every block has length one and its transition is the identity, giving identity on both cone coordinates.

For step 9, the Roos statement explicitly defines augmentation by (0,(gamma_n)_n), exactly the clause quoted in citations.json. The comparison takes this to (0,(q_(phi(n)))_n). The cited derived-category definition describes localization at quasi-isomorphisms; it transports the already proved equations and inverts the map proved quasi-isomorphic in step 6. It is not being cited for cofinality or a uniqueness theorem for cones.

As a separate finite sanity check, I evaluated 294 scalar-coordinate identities for the block square and the two h identities, with identity, arithmetic, and irregular selected sequences, including m_1>1, and zero, identity, and nontrivial signed transition scalars. They all passed. I also checked the zero tower, a constant identity tower, one-step blocks and strict compatible augmentations directly from the formulas. These are checks of the formulas, not substitutes for the coordinatewise proof in the item. No Lean or build tool was run.

Every proof dependency is the union of step uses; every cited statement was opened and each citations.json excerpt was checked as an exact substring. All steps are below 2000 characters. Steps 3-5 are a single explicit finite-block deformation retraction for these maps, not a hidden general comparison lemma. The only non-elementary result invoked without proof is the existing homotopy/cohomology Mathlib leaf. All other cited nodes define the objects, maps or quasi-isomorphisms used. No new elementary, duplicate, clause-restatement or unsearched node is introduced, and no target statement is weakened.
