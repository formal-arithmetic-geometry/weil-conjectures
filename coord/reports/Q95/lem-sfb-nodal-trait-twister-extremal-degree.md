# Q95 stage-1 delivery: lem-sfb-nodal-trait-twister-extremal-degree

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-nodal-trait-twister-extremal-degree.json`: split statement, six proof steps, no Mathlib match. Mathematical statement unchanged; added its invertible-module definition citation and dependency.
- `citations.json`: verbatim portions of cited node statements, one entry for each step/citation pair.
- `report.md`: this report. Search outputs, the actual `searches.jsonl`, and `prepare.py` are sandbox working records.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched `lean/WeilConjectures/` for the item tag and for twisters, vertical divisors, generic triviality, and extremal nodal degree language. No declaration stating all the clauses was found. Mathlib is not an attachment source.

## Literature wanted

WANTED: local archival copy of Ian Morrison, *GIT Constructions of Moduli Spaces of Stable Curves and Maps*, arXiv:0810.2340, Section 3.3, Proposition 10, printed p.16, for the item's historical source. I read the primary PDF online at https://arxiv.org/pdf/0810.2340. All actual black boxes in this split are existing DAG statements checked against the locally available Stacks source. The generalized proof is explicitly agent-written; it does not assert that Morrison proves the arbitrary-total-space formulation as written.

## What required repair

The item had no proof. Its source points to an extremal component-coefficient argument, but the item deliberately allows singular total spaces, nodes which persist generically, and arbitrary thickness. Treating individual components as Cartier divisors would impose an unjustified hypothesis. Instead I use semicontinuity to obtain a nonzero section on the special fibre and use its component support. This proves exactly the existing assertion and preserves the boundary-zero numerical argument needed by the parent. No statement dispute or weakening is needed.

The blueprint ancestor command prints `None`: the existing creation chain has no imported ancestor. I retained the existing `blueprint.from.node = null`, its full place and via chain, and the searched empty `same_as` field. The assigned chapter and unit are unchanged. This auxiliary input is below the unit-level proof, not a replacement of the constructible direct-image route. Generic tools from other units are explicitly declared in `split_report.tool_uses`.

## Not duplicates

No new nodes are proposed. In particular:

- Reuse `lem-sfb-proper-flat-sheaf-euler-local-constancy` for Euler constancy, rather than create a degree-specialization node.
- `lem-pd-degree-locally-constant` is restricted to base changes of a fixed smooth geometrically integral curve, so it cannot be used for the varying nodal family here.
- Reuse `lem-trf-nodal-normalization-adjunction` only for its stated normalization and branch clauses; no adjunction theorem is being inferred from a definition.
- Reuse the general component formula, birational degree invariance, section positivity, smooth-curve local-ring theorem, and the existing rational-point/effective-divisor formulas. The small ideal-factorization and sum arguments are proof steps, not new nodes.

I searched the whole DAG by statement concepts and the whole blueprint with `blueprint_refs.py search` for twister, nonzero section, degree/local constancy, Euler characteristic and coherent cohomology. I ran the required Mathlib searches through `msearch.py`, including two different semantic phrasings. The returned Weierstrass, polynomial, residue-field, zero-cycle and zero-locus results do not state the item. All five search outputs were read and appended with their actual queries and results, preserving the original searches already in the item.

## Review by Q95

I read the worker brief, stage-1 contract, the three levels in SETUP, GOAL, the assigned chapter and unit, and delivery-errors B--E (both historical copies). For the historical item I read Morrison Section 3.3, Proposition 10, printed p.16. For the actual argument I read Stacks `perfect.tex`, Tags 0B9T (`lemma-chi-locally-constant-geometric`) and 0BDN (`lemma-jump-loci-geometric`), `coherent.tex` Tag 02KH (`lemma-flat-base-change-cohomology`), `varieties.tex` Tags 0AYR, 0AYW, 0AYU, 0AYY and 0B40, and `curves.tex` Tag 0C4D (`lemma-nodal`). There are no new statement-only nodes needing independent source checks.

In Step 1, `lem-pc-projective-proper` says projective morphisms are proper. `lem-pc-projective-base-change` explicitly gives projectivity of arbitrary base changes, which verifies properness of the residue and geometric fibres; I checked its Stacks source Tag 01WF (`lemma-H-projective-base-change`). The local-freeness clause of `def-sc-invertible-module` makes T finitely presented and R-flat because f is flat. The Euler-constancy node explicitly assumes a proper finitely presented family and a relatively flat finitely presented module, and explicitly gives arbitrary base change of its Euler function. Those hypotheses hold for both T and the structure sheaf. Its conclusions give equality of their geometric special-fibre Euler characteristics, and the actual degree definition gives degree zero. I checked that the locally constant functions really agree on both trait points; no connectedness theorem about a different base is used.

In Step 2, the semicontinuity node actually states upper semicontinuity of the residue-fibre H^0 dimension. A closed upper level set containing the generic point contains the closed point. Nonemptiness of the generic fibre is essential for its constant section 1 to be nonzero. The flat-base-change node explicitly states the H^i tensor formula for qcqs f and flat g; it applies to the field extension k to Omega after passing to X_s. A nonzero vector remains nonzero under this extension. This is not a claim that arbitrary special-fibre cohomology commutes with base change from R.

In Step 3, the degree-component node explicitly lists integral proper components and the multiplicity-weighted degree formula. Reducedness makes the generic local rings fields and the multiplicities one. The normalization-adjunction node explicitly says that the normalized proper components are smooth proper connected curves, that normalization is an isomorphism away from component self-nodes, and that nodes have two branch preimages. Its hypotheses only concern the geometric nodal curve over the algebraically closed field, all of which hold here. Birational degree invariance applies to the integral component and its normalization, not to the reducible total curve as if it were integral. The reduced-ring nilradical argument proves that at least one normalized component section is nonzero.

In Step 4, the section-positivity node explicitly gives nonnegative degree for a nonzero section on an integral proper curve and strict positivity if that section has a zero. Applied to every normalization, it implies that a nonzero-on-every-component section with total degree zero has no zeros. A zero at a node would pull back to a zero on its branches; a zero at a smooth point also has a normalization preimage. Hence the section is a unit in every local trivialization and trivializes L. In particular this argument excludes a nontrivial multidegree-zero gluing class; zero multidegree alone was never identified with triviality.

Step 5 is elementary from the preceding branch description and connectedness: Y and its complementary union W cannot be disjoint, each boundary node has one branch on each side, and restriction of a section zero on W has zero residue value at the node. I wrote the reasoning rather than introducing a duplicate graph-cut lemma. A component meeting W in several nodes contributes several distinct points; a self-node contributes no boundary count. The intersection consists of finitely many nodes on the proper finite-type curve.

In Step 6, the local-ring node states the DVR property at every closed point of a smooth connected curve. The relevant branch points have residue field Omega, and their point ideals therefore give effective Cartier divisors on the normalizations, not on X. Membership of the coefficient of sigma_i in these point ideals supplies a nonzero section of the negative boundary twist. Positivity applies to that new section. The degree-base-change node's actual statement, not just its title, includes both the effective-divisor tensor formula and the degree of a sum of rational Cartier points, which give the lower bound r_i. Summation counts each boundary node exactly once.

I tested an irreducible fibre (including self-nodes): only the trivial branch can occur. I tested two components with one boundary node, where degrees (1,-1) realize equality on the positive component, and multiple boundary nodes, where the number of distinct vanishing points gives the full multiplicity of the cut. Empty B_i is allowed and contributes zero. The empty fibre and disconnected fibre are excluded by the item's hypotheses; no proof step assumes the generic fibre is smooth, that total X is regular, that any component of X_s is Cartier in X, or that R is excellent. Persistent nodes and smoothing thickness affect none of the steps, since all local point-divisor arguments take place on smooth normalized geometric components.

C1/C4 were checked by opening every cited node's statement and recording substantive verbatim portions in citations.json. I also checked that none of the cited dependencies has a path back to this item. All six steps are under 2000 characters; no long step hides an additional lemma. The new argument uses existing general results and elementary deductions rather than moving a clause of the item into a new node. No Lean, compiler, Lake, repository file or launcher file was written or run.

## Unfinished work

None in the authorized stage-1 scope. Existing cited nodes keep their own independent proof obligations. The first server dry run passed at 829aef4e9f4. I then made the fibre-projectivity citation explicit and rerun the required dry run before direct delivery.
