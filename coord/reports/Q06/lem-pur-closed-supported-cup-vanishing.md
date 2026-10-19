# Stage-1 delivery: lem-pur-closed-supported-cup-vanishing

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-closed-supported-cup-vanishing.json: existing statement, split into ten proof steps; Mathlib searches found no match.
- citations.json: one verbatim statement passage for every citation of every proof step.
- report.md: this report.

There are no new nodes and no Mathlib leaves. Search logs and local writing scripts are retained in the item sandbox only.

## Attachments

None. I searched the read-only slopmaster2 WeilConjectures tree for the exact blueprint tag, supported cup, support/cup combinations, and restriction/zero. The declarations in EtaleCohomology/Purity/Smooth/KummerClass.lean construct cup products (mostly in even degrees), and SixFunctors/Etale/Derived/Supports.lean constructs supported operations; none states the requested zero action for arbitrary a,b,t,s. The existing closed-immersion derived full-faithfulness instances are general tools, not the item's theorem. No attachment to an upstream master sorry is claimed.

## WANTED

None. All sources needed for this split are available locally.

## Corrections and scope

The statement is unchanged and is mathematically sound. The imported proof was empty. The source correctly describes Tags 0G75--0G77 as a ringed-space model, not a theorem already about small pro-etale sites. I did not apply a ringed-space theorem to a site. I supplied the finite ordinary module-sheaf proof using the current supported tensor-morphism definition and existing closed-image results.

The blueprint ancestor remains thm-pur-localized-top-chern with via lem-pur-chern-flag-formula. I read the main-20261015 localized-top-Chern statement and proof, especially Step 4 (L4), and the current supported-cup and supported-Hom blueprint nodes. This auxiliary calculation serves the ordinary cohomology axiom needed for the flag/Chern formula. It does not attempt to resolve the separate local-class gluing or flag argument of the ancestor. The unit sk-prop-an is not its key statement, so I did not change its realized fields. No chapter/unit route is replaced. No SGA source is used.

## Mathlib and duplicate searches

For the item I ran msearch.py with LeanFinder, Loogle, grep, and LeanSearch and read their returned hits. Two natural-language phrasings (the inherited records plus the new direct zero-action queries) and support/cup regular expressions do not find this operation in Mathlib. The returned declarations about vanishing structure-sheaf sections on basic opens, terms of a cochain complex, and topological compact support do not state supported etale/pro-etale cup annihilation. Loogle's cup/support query and the direct grep had no hits.

I also explored a possible closed-tensor-restriction lemma, with both semantic services, Loogle, and two greps. The hits only provide general module adjunctions, pro-etale site definitions, and unrelated monoidal closed structures. I did not create that node: the shifted-sheaf calculation below follows in a few lines from existing closed-image and exact-adjunction statements. This avoids creating an elementary consequence as a node.

I searched the whole DAG for i_*i^*, supported Hom, closed direct image, the closed/projection/tensor keywords, and the relevant Stacks tags. I ran blueprint_refs.py ancestor for the item and whole-blueprint searches for support cup, closed tensor, support restriction, closed constant, restriction tensor, annihilate support, zero cup, and projection formula. No blueprint node states this item. Existing closed-site, essential-image, normalized Hom, tensor, and comparison nodes are reused. Since there are no new nodes, there are no new-versus-existing duplicate pairs to distinguish.

## Review by Q06

I read the item against Stacks cohomology.tex, Tags 0G75 (remark-support-cup-product), 0G76 (remark-support-cup-product-global), and 0G77 (lemma-support-cup-product). Tag 0G76 visibly begins with restriction to the support; Tag 0G77 leaves the compatibility proof omitted. I checked the pro-etale replacement against proetale.tex, Tags 09AA (lemma-closed-immersion), 09BM (lemma-closed-immersion-complement-retrocompact-exact), and 09AH (lemma-ses-associated-to-open), and the actual statements of every cited DAG node. I also read the relevant tensor-pullback passages of sites-modules.tex (03EL) and sites-cohomology.tex (07A4), and the exact-functor and adjunction passages of derived.tex (015F and the proof of 08BJ). No new node needs a source review.

Step 1 uses lem-weil-pbc-finite-type-over-noetherian for the actual finite-type structure morphism to Spec k. A field is Noetherian directly from its two ideals. The cited open-subscheme node says every open subscheme of a Noetherian scheme is quasi-compact; applying it to U intersected with each affine open proves j is quasi-compact by the cited finite-type-morphism definition. I read the 01T6 statement and the 01OZ/04ZA consequences. This checks the quasi-compact-complement hypothesis rather than assuming it of an arbitrary closed immersion.

Step 2 uses exactly the Hom isomorphism in lem-pur-supported-hom; A(t) and A(s) are degree-zero sheaves, so its bounded-below hypothesis holds. I read the current def-pur-supported-cup statement, including its explicit multiplication map, flatness argument, and signed shift comparison. For supports X and Z its coefficient multiplication is the left unitor. Thus the displayed morphism represents the actual supported product, not an arbitrarily chosen pairing.

Step 3 uses the explicit evaluation normalization stated by lem-pur-supported-hom-adjunction-transpose. Its formula evaluates a morphism on q(1). Composing with the constant restriction q therefore gives the inclusion of supported sections into all sections. Doing this on the same injective resolution proves the forgetting map is precomposition with q. I checked the locally Noetherian hypothesis using Step 1. I did not take forgetting compatibility from the statement of supported-cup-functoriality, which does not itself state that square.

Step 4 reads lem-pur-supported-hom-pullback in its full-support case; its statement explicitly includes the pro-etale version for etale-pulled-back inputs. To meet that condition, I use lem-amb-finite-tate-site-descent for nonnegative twists and lem-asd-etale-finite-twist-pullback for their etale rank-one lines. For negative twists I wrote the basis/dual evaluation argument, using the exact comparison inverse image of lem-sf-comparison-pullback-exact and the general ringed-topos tensor comparison. These two nodes were added during self-review so that exact monoidal comparison was not implicit. The conclusion is the actual equality between restriction of the cohomology class and inverse image of its representing morphism; no exceptional functor appears.

Step 5 uses def-pur-supported-cup for an assertion it actually proves in its statement: S=i_*A_Z is flat. It is not a citation of a definition of flatness to justify tensor exactness. Tensor with this degree-zero K-flat object computes the derived tensor, so F[a] tensor S is H[a] for the sheaf H=F tensor S. The ringed closed-adjunction node explicitly states j^*i_*=0. The ordinary inverse-image tensor-comparison node then gives j^*H=0. The closed-essential-image node explicitly states that the actual unit H -> i_*i^*H is an isomorphism. Its coefficient-identification hypothesis is supplied by the finite constant exact-pullback node. I checked that these are ordinary constant module sheaves, with no condensed/completed coefficient substitution.

Step 6 uses the derived closed adjunction of lem-sf-ringed-closed-kernel-adjoint and exact constant pullback. The exactness of i_* is part of the former node's statement. The termwise-adjunction node states its unit and counit on complexes; the exact-functor factorization node states that every complex computes the derived functor and provides shift compatibility. I wrote how the unit and adjunction identities descend through localization. For the particular target H[a] this unit is eta_H[a], hence invertible. This is not a test of derived morphisms on cohomology sheaves, which would be invalid.

Step 7 uses the ambient finite-level natural isomorphism from lem-pur-derived-pullback-tensor-iso; its statement permits arbitrary derived inputs. The shifted tensor-morphism calculus explicitly states additivity and pullback compatibility, so tensoring the zero restricted class with the identity is zero. Step 8 is just the written naturality equation eta_T m = i_*(i^*m) eta_S and cancellation of an isomorphism. It creates no new universal comparison assertion.

Step 9 writes the bifunctorial factorization of alpha tensor beta using lem-weil-derived-tensor-functorial and the actual cup definition. The zero first factor from Step 8 proves the supported assertion. Step 10 writes the naturality equation for the left unitor and uses the Step 3 formula for forgetting. The two paths are literally the same composite after tensor bifunctoriality, with the same signed shift and twist multiplication maps. This supplies the omitted 0G77 calculation rather than asserting it is clear.

I checked the small cases Z empty (S=0 and all supported groups vanish), Z=X (S=A and the hypothesis is alpha=0), a=0 or b=0 (the same unit formulas work), and negative t or s (duals of the finite rank-one Tate line). The proof never divides by a coefficient or by 2, so n=1, ramified coefficients, and ell=2 cause no extra restriction. Singular or nonreduced X and Z enter only through the closed-site facts; no purity, smoothness, regularity, Cartier, finite-Tor constructibility, or exceptional base-change isomorphism has been assumed.

All ten steps are below 2000 characters. I checked B--E: no new unsplit node contains a proof, no clause is moved to a new node, all non-elementary inputs have actual statement citations, no cited proof is used as a black box in place of a statement, and the final tensor/unit identities are written explicitly. citations.json contains verbatim passages checked against the current node statements. Generic off-unit uses are declared in split_report.tool_uses for maintainer review; no maintainer-owned tool_uses field was edited.

## Not duplicates

No new nodes.

## Unfinished work

None in this one-level split. The existing cited nodes retain their own statuses; this delivery makes no claim that their Lean proofs or descendants are closed. Required server dry run and delivery results are recorded by the delivery tool.
