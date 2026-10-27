# Stage-1 delivery: lem-sfb-split-charzero-weyl-character-identity

## Files written

All paths below are in this item's sandbox; no repository or launcher file was written, and no Lean file or compiler was used.

- `dag/nodes/sec-six-functors-basics/lem-sfb-split-charzero-weyl-character-identity.json`: item, statement, split into eight steps; not a Mathlib match. The statement is unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-split-semisimple-geometric-root-comparison.json`: new statement-only node, unsplit, no Mathlib match; geometric scalar extension of the actual group, root datum and prescribed positive Borel.
- `dag/nodes/sec-six-functors-basics/lem-sfb-split-simple-absolute-irreducibility.json`: new statement-only node, unsplit, no Mathlib match; absolute simplicity for split semisimple rational representations.
- `citations.json`: one verbatim statement quotation for every step/node pair. Whole statements are quoted so the reader can inspect all hypotheses as well as each conclusion.
- `searches.jsonl` and `search-results.json`: executed search log and full returned hits, respectively. Supporting sandbox script: `write_split.py`.

## Attachments

None. Searches for the blueprint id, Weyl character/alternant/highest-weight terms, absolute simplicity and geometric root comparison in `lean/WeilConjectures/` found no declaration stating this item or either new statement. Finite abstract-group FDRep characters and abstract root-pairing declarations are different objects and give no attachment.

## WANTED

None for this split. Milne's local PDF supplies the item and both new statements. The existing Euler-characteristic input has its own recorded Nielsen/Iversen obligations; I reused its statement and did not claim those sources were locally available or reproved them here.

## Errors and corrections

Milne's printed Theorem 22.52 is false without the characteristic-zero restriction; its appended errata explicitly supply that restriction. The item already makes it, so there is no statement dispute or statement change here. The line-bundle convention also matters: for positive roots in Lie(B), H^0(M_mu) has highest weight -w0(mu), not mu. The proof takes mu=-w0(lambda), constructs the matrix-coefficient map explicitly, and converts the existing negative-rho Euler identity by reindexing alternants. It never cancels the alternant or evaluates a quotient at the identity.

The inherited `blueprint.from.node` is null: `blueprint_refs.py ancestor` reports None because the upstream created-item chain is broken. I retained this computed ancestry and the detailed existing place and via chain, added explicit places for the new nodes, and recorded the anomaly in split_report. The current blueprint is `literature/blueprint/latest` -> `main-20261024`; its ctf-stability unit and direct-images proof (3) were read, together with the stored chapter/unit records. This is the numerical supporting route already inherited by this item, not a replacement of a unit step. The item is not the key unit node, so no unit record is changed.

The only off-unit generic tool is `lem-pc-fpqc-descent`, declared in split_report.tool_uses. It supplies full faithfulness for descent of multiplication of character lines. The representation unit has no replacement for this generic module-descent fact.

## Unfinished work

The two new lemmas are intentionally statement-only stage-1 obligations. The item's proof is complete relative to the cited statements; no Lean proof is claimed. No mathematical part of the item is left unstated or omitted.

## Not duplicates

lem-sfb-split-semisimple-geometric-root-comparison vs lem-sfb-split-positive-root-borel: the latter starts with an already pinned split realization over a ring. The new node starts with the actual unpinned rational group and proves its geometric simple connectedness and actual root/cocharacter comparison, so that the algebraically closed-field inputs apply.

lem-sfb-split-semisimple-geometric-root-comparison vs lem-sfb-relative-tangent-weight-base-change: the latter compares tangents and weights for a smooth group with an external split torus action, without geometric simple connectedness, maximality, normalized coroot identification or a Borel for the chosen positive system. It does not state the new comparison of reductive root data.

lem-sfb-split-semisimple-geometric-root-comparison vs lem-sfb-split-flag-rational-fixed-scheme: the latter assumes a split Borel pair and a flag quotient, and compares their fixed flags and Weyl points; it supplies neither geometric simple connectedness nor root-coroot comparison for the unpinned input group.

lem-sfb-split-semisimple-geometric-root-comparison vs lem-sfb-multiplicative-character-antiduality: the latter concerns groups of multiplicative type, hence covers torus characters but not geometric simple connectedness, coroots or positive Borels of the semisimple group.

lem-sfb-split-simple-absolute-irreducibility vs lem-sfb-simple-module-dual-highest-weight: the latter starts over an algebraically closed field and classifies highest lines and duals. It cannot justify that the original simple rational representation stays simple on extending Q to its algebraic closure.

Whole-DAG searches included exact ids, titles/concepts, 22.4, 22.50, 22.52, absolute simplicity, scalar extension, highest weights, root data, and existing Weyl/flag inputs. Whole-blueprint `blueprint_refs.py search` queries included Weyl, Weyl character, highest weight/highest, Casimir, alternant, root datum, simple representation, scalar extension, simply connected and absolute. No blueprint node states either new lemma or this item. No Stacks tag is attached to the new statements: these are split semisimple-group representation results sourced by Milne theorem numbers, not Stacks statements.

## Review by Q35

I read Milne 22a (printed pp.463--471), 22d--22e (pp.479--481), and the appended p.480 erratum for the item. For geometric root comparison I read 21.11--21.12 (pp.428--430), 21.29--21.35 (pp.433--435) and 23.56--23.59 (pp.501--502): these identify the field-independent actual split root datum, simple connectedness with the weight lattice, and the Borel associated with the chosen chamber. For absolute simplicity I read 22.2--22.4 (pp.463--464) and 4.19(b) (pp.90--91), including the distinction between an invariant rational subspace and absolute simplicity. Neither new statement is a character identity or any clause of the item relabelled: both are general scalar-extension tools, while the steps carry the character calculation.

Step 1 uses the finite weight decomposition, geometric root comparison, absolute-simplicity and algebraic-closure existence statements. Their hypotheses are a split maximal torus, a simple finite-dimensional rational representation, and characteristic zero, all present. The equality of multiplicities after scalar extension is written out with a weight basis, and the root-vector annihilation extends through the natural dual-number tangent comparison. It does not assert that an arbitrary representation over Q is absolutely simple.

Step 2 reads the Borel-pair statement only for semisimple implies reductive; the rho-section statement for rho being an actual character; the reflection-realization and rho-orbit statements for the geometric Weyl group and longest element; and the differentiation-Hom statement for U-equivariance of F -> V_F. U is smooth, connected, affine and finite type by the geometric comparison and its definition, and F has characteristic zero. Thus Lie(U) annihilation really implies group-scheme invariance. The simple-module highest-line statement then identifies the given lambda; it is not used to infer absolute simplicity.

Step 3 uses the dual-highest-weight statement to get ell of weight -w0(lambda), and the primitive cyclic weight bound for all weights of the simple dual. I corrected a draft that used the coroot-base statement: its moreover clause does not explicitly tie the sign of a coroot to the sign of its root. The delivered proof instead applies the exact cyclic weight statement to the nonzero normalizer translate n_delta ell. The displayed all-algebras formula gives its reflected weight, and independence of the simple roots then proves the desired inequality. This is Milne 22.15--22.17, and verifies dominance without extracting more than a cited statement says.

Step 4 uses the actual homogeneous-section function equation, including inversion and left-translation convention. I checked j(x)(gb)=mu(b)j(x)(g), j(sx)(g)=j(x)(s^-1 g), and nonzeroness by evaluation at 1. The Euler statement supplies finite-dimensional sections, complete reducibility applies only in characteristic zero, and the induced primitive-line statement supplies one-dimensional U-invariants. Each simple summand has a nonzero highest line by the cited simple-module statement, so there can be exactly one summand. Injectivity and surjectivity follow from ordinary invariant-subspace simplicity. This is the explicit elementary matrix-coefficient argument from those cited statements, not an unproved appeal to Borel--Weil.

Step 5 uses the homogeneous quotient's actual character descent data and full faithfulness of fpqc module descent. I corrected a draft phrasing about local trivializations to use the faithfully flat B-torsor and its descent data directly, without assuming that the torsor is Zariski trivial. Multiplication of characters is exactly the compatibility equation, so this is an elementary application of the cited equivalence, not a new node.

Step 6 uses the rho simple-coroot values, strict-dominant ampleness, canonical-character isomorphism and Kodaira statements. I verified algebraic closedness, characteristic zero, smoothness, projectivity, geometric integrality, pure dimension and ampleness explicitly. The mu+2rho inequalities are strict even when lambda lies on chamber walls. I deliberately use the characteristic-zero Kodaira assembly recorded in Milne 22.51; the general Kempf node's positive-characteristic dimension route is not used.

Step 7 applies the exact polynomial Euler identity q_mu A(-rho)=A(-mu-rho), with the same line bundle, lattice, determinants and integer weight multiplicities. Steps 4 and 6 identify its Euler sum with the original q. The finite-sum reindexing gives both determinant factors and cancels only the unit sign. In particular no character is reduced modulo a field characteristic and no zero denominator is evaluated.

Step 8 separately checks empty roots: the regular-cocharacter Borel statement explicitly gives S=T_F in that case, and lattice rank zero makes the split torus trivial. Simplicity gives dimension one directly. Reducible root systems require no factorwise choice in any step. I also checked lambda=0, rank-one SL2 with lambda=m (q=e^m+e^(m-2)+...+e^-m), and products of two rank-one systems: multiplication by e-e^-1 telescopes to the alternant, and the two determinant signs in step 7 agree.

For B--E: both new files introduce their own objects, have definition dependencies, ordinary TeX, precise local source locations, empty proof/proof_deps and unsplit status. I ran all four prescribed search kinds for the item and each new node, with independent natural-language phrasings, and read the actual hits. FDRep.simple_iff_end_is_rank_one assumes an algebraically closed field and a finite abstract group; RootPairing.BaseChange handles abstract pairings and even lists extension of scalars as TODO. Neither is an algebraic-group-scheme match. All results and exact query strings are retained, with no invented searches or unavailable service recorded as absence. Every proof citation was checked against the statement, and citations.json copies it verbatim. I checked the transitive closures of the reused geometric Euler, canonical, ample, Kodaira, simple-module, complete-reducibility, primitive-line and differentiation inputs for a path back to this item; none contains it. All non-elementary facts used are cited statements; tensor and finite-sum manipulations are written as elementary arguments. No proof step exceeds 2000 characters, no new node merely restates the item, and no source prohibition is used.
