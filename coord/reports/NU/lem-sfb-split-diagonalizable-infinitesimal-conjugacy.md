# NU — lem-sfb-split-diagonalizable-infinitesimal-conjugacy

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-split-diagonalizable-infinitesimal-conjugacy.json`: existing statement node, now split into four steps; no Mathlib match.
- `citations.json`: verbatim statement quotations for all nine step/node citation pairs.
- `report.md`: this report.

No new nodes and no Mathlib leaves. The sandbox initially contained only dispatcher brief markers, so there was no earlier proof or report to replace. The live item was unsplit with no proof. The statement, statement dependencies, source, original searches, provenance, and blueprint ancestry were retained. Four newly executed searches were appended from `searches.jsonl`.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact node identifier and for diagonalizable/infinitesimal-conjugacy terminology; no project declaration states the item. No compiler or Lake command was run.

## Wanted literature

WANTED: Brian Conrad, *Reductive group schemes* (2014), Appendix B.2, Proposition B.2.5, Corollary B.2.6 and Remark B.2.4, printed pp.285–287, locally as `literature/conrad-reductive-group-schemes.pdf`, for this item. Read online at https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf using the PDF text. No local literature or repository file was written.

## What changed and why

The item had a source reference but no argument. The existing split-torus conjugacy proof suggested the direct coefficient contraction, which works unchanged for the basis of an arbitrary group algebra. I wrote out that extension for the actual character group M, preserving every hypothesis and the homomorphism-level conclusion. The explicit contraction is agent-written and `proof_origin.by` records that fact. There is no claim that a reference alone proves a step.

Conrad's supplied-lifts argument is the source context: it treats the difference cocycle and the conjugation action; his vanishing remark explains why diagonalizable groups have no obstruction in degree one. The delivered proof uses the existing congruence-module theorems and computes the contraction directly instead of introducing a new cohomology node. No forbidden source is used.

The four steps use N for the kernel module, keeping M for the character group. The decisive calculation takes the coefficient indexed by the identity element 0 of M in the second variable. It is a coefficient in a free group-algebra basis, not evaluation at points over a field. Thus torsion and nonreduced diagonalizable groups cause no extra hypothesis.

Nothing was found wrong in the imported statement. No statement dispute or change to its meaning is made. The work is complete subject to the required dry run and delivery.

## Searches and reuse

The DAG was searched for square-zero Lie kernels, flat scalar extension, regular cocycles and diagonalizable conjugacy. I read the existing statements of `lem-sfb-group-space-square-zero-kernel-module`, `lem-sfb-smooth-group-congruence-flat-scalar-extension`, `lem-sfb-split-torus-infinitesimal-conjugacy`, `lem-sfb-square-zero-hom-regular-defect`, `lem-sfb-diagonalizable-regular-two-cocycle`, and `lem-sfb-smooth-diagonal-additive-crossed-vanishing`. The first two provide precisely the general-purpose inputs. The torus conjugacy theorem requires a free character lattice; the smooth-diagonal theorem assumes an algebraically closed field and smooth source. Neither is silently applied to torsion characters over general rings. The two-cocycle theorem concerns degree two and is unnecessary here.

`tools/blueprint_refs.py ancestor` returned None; searches of the whole imported blueprint for `cocycle`, `diagonalizable` and `infinitesimal conjugacy` found no equivalent imported statement. The existing from.place and via chain are retained, and same_as is empty. Read the latest blueprint's direct-images proof (3), its unit and chapter records, and the three-level restrictions in SETUP.md. This is the existing supporting centralizer prerequisite below that route, with no route replacement.

Executed all four permitted Mathlib search kinds with msearch.py and read the hits. LeanFinder returned formal-smooth algebra-extension lift constructions; LeanSearch returned abstract group cohomology and HomComplex cocycles; Loogle and the AlgebraicGeometry grep had zero hits. The live item also retained its earlier, different semantic phrasing. None of these algebra-map or abstract-group results is an exact theorem about regular homomorphisms of ring group schemes or a one-line specialization to this statement. Actual results and query strings are recorded without inventing searches; all services answered in this run.

## Not duplicates

No nodes were created. All reusable input statements were cited in place.

## Review by NU

I read Conrad Appendix B.2 at the online source places above for the item's deformation context. For the module inputs I opened their full DAG statements and their proof sources: Stacks `spaces-more-morphisms.tex`, Tags 0618 and 04D0, labels `lemma-difference-derivation` and `lemma-action-by-derivations`. No new node requires a new source review. The explicit finite-sum calculations below are agent arguments, recorded as such.

Step 1 uses the kernel-module theorem for its additive module structure, the ring-diagonalizable definition for the basis and Hopf operations, and the flat-scalar-extension theorem for its actual isomorphisms and naturality. I verified that G is smooth affine of finite presentation exactly as that theorem requires and that J is the given square-zero ideal. C and C_2 are free over A even when M has torsion. Their flatness is proved by the direct-sum tensor calculation; no smoothness of H or assumption that the thickening splits is used. The finite-coefficient module identification is explicitly constructed from the cited tensor universal property. This step is marked non-elementary because the congruence-module theorems are substantive inputs.

Step 2 uses the coproduct in the diagonalizable definition and the substitution naturality in the scalar-extension statement. The maps for x, y, xy are written explicitly on basis vectors. Equality of the two given reductions places the difference in the reduction kernel over C. Expanding the two group homomorphism identities gives the displayed product and then its additive cocycle identity. This step is elementary relative to those precise inputs; it does not cite a mere definition for an unproved cohomology assertion.

Step 3 uses both clauses of the scalar-extension statement: conjugation is linear, and naturality identifies the conjugation of each extended coefficient with its extension. This justifies taking the y-identity coefficient through the action. I checked each coefficient: the left side contributes p, the constant first term contributes c(x), and the action term contributes rho_x(p). The sign is therefore c(x)=p-rho_x(p), the sign required by Int(u) f_1=f_2. This is a direct finite-sum calculation, with no auxiliary claim hidden in it.

Step 4 uses the normalization at A and additive law of the same scalar-extension statement, and the affine-spectrum definition to interpret the universal point. The kernel difference p-rho_x(p) represents u f_1(x) u^{-1} f_1(x)^{-1}; cancellation gives the desired equation. The universal C-point is the identity morphism of Spec C, so this proves equality of scheme morphisms, not merely equality of geometric points. Subsequent evaluation is pullback along the algebra map specifying any test point. Membership in N gives the required identity reduction without a lifting theorem.

I checked small cases J=0 (N=0 and u=1), M=0 (the source is the trivial group and both homomorphisms are its identity section), and the zero ring (all points and modules are trivial). I also checked the critical example M=Z/p over a ring of characteristic p: the group algebra may be nonreduced, but its basis is still indexed by M and the y^0 projection still makes the calculation valid. No division by p, point-density argument, injectivity, connectedness, noetherian hypothesis or finite generation of J enters. The argument also allows f_1 to be trivial and G commutative.

Against delivery-errors B–E: no new statement-only nodes, relabelled clauses or duplicates were introduced; the existing statement is self-contained and its notions remain cited; sources are identified by their precise places; all nine citation pairs have verbatim quotes verified against the live statements in citations.json. I checked the input statements, not their proof internals, for every use (C4), and the only non-elementary theorem invocations are the explicitly cited kernel/module inputs (C1). All are in the same unit; the other two notions used in proof steps are Mathlib leaves. None depends on this item. Every proof step is shorter than 2000 characters and is a single construction or calculation. The two substantive kernel inputs are already separate existing nodes; their content was not hidden in elementary text. No global DAG or review script was run locally.
