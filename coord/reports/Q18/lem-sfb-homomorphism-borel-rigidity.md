# Worker report: lem-sfb-homomorphism-borel-rigidity

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-homomorphism-borel-rigidity.json`: statement, now split in five steps. No Mathlib match. The inherited statement and its hypotheses are retained; literal doubled TeX backslashes were normalized.
- No new nodes and no new Mathlib leaves. `citations.json` records every proof-step citation, with the entire cited statement as an exact quote. The sandbox also contains the source extraction, logged searches and the local writing script; these are research aids, not delivery node files.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag, Borel subgroup names and flag-variety terminology; there is no project declaration giving this item. No Lean was written, and no compiler or Lake command was run.

## WANTED

None. The proof source is available locally as `literature/milne-algebraic-groups_iAG2017.pdf`.

## Findings and changes

Read Milne Proposition 17.21, printed p.358, specifically its R=k argument. Its standing group varieties in section 17b are affine, smooth connected algebraic groups over an algebraically closed field; no reductivity, surjectivity or kernel restriction is imposed. The item says exactly this case, including equality of scheme morphisms. Its existing proof was empty.

The proof follows Milne: form delta(a)=u(a)v(a)^{-1}, descend its right-B invariance, use completeness of A/B and affineness of D, and evaluate at the identity. Read the quotient factorization Proposition 5.21, pp.104, torsor calculations Propositions 5.24--5.25 and Corollary 5.27, pp.104--105, Theorem 17.9, p.354, and Appendix A.75(f),(g), p.583. The codomain G in one printed occurrence of delta-bar in Proposition 17.21 is visibly G'; our map has codomain D throughout. No statement correction or dispute is required.

I did not infer scheme-level constancy just from a one-point topological image. Instead I used the existing proper reduced global-sections node (Stacks 0BUG) and the affine adjunction (01I1) to obtain equality of morphisms. This also avoids claiming that equal F-point maps alone suffice on arbitrary nonreduced test algebras.

The current blueprint is `literature/blueprint/latest` (main-20261024); I read its unit `_section.md` and direct-images proof (3), retaining the item's supporting route and full inherited `blueprint.from.place`/`via`. The inherited chain ends at an item with no literal blueprint ancestor, and `python3 tools/blueprint_refs.py ancestor lem-sfb-homomorphism-borel-rigidity` reports None. Whole-blueprint searches `Borel`, `homomorphism Borel`, and `quotient Borel` found no node stating this rigidity result. The Borel hits in the imported blueprint are Borel--Moore terminology, not algebraic-group Borels.

Searched the whole DAG by Borel subgroup, quotient, complete variety, global functions, affine adjunction and fpqc representable descent. Opened the actual statements of all twelve proof dependencies. General-borel-flag-variety states a proper smooth flag scheme with transitive rational action and exact scheme stabilizers, but does not itself state that its quotient map is an fpqc epimorphism. Homogeneous-orbit-quotient-geometry supplies exactly that comparison and its kernel-pair formula after identifying the orbit with the flag scheme. These statements are used separately, without borrowing either node's proof.

The Mathlib searches were made with the required msearch.py command and are in searches.jsonl. LeanFinder queried homomorphisms agreeing on a Borel; LeanSearch used the distinct maximal-connected-solvable phrasing; Loogle searched "Borel"; grep searched `Borel|flag.variety|hom_ext` in AlgebraicGeometry. Read the returned `AlgebraicGeometry.ext_of_isAffine`, Mathlib/AlgebraicGeometry/AffineScheme.lean:154--156: its hypothesis is equality on global sections, not equality on a Borel subgroup. Read `LieAlgebra.Basis.borelUpper` and `borelLower`, Algebra/Lie/Basis/Basic.lean:147--156: these are Lie submodules, not subgroup schemes. The other hits concern abstract solvable groups or general extensionality. None is a match or a one-line specialization. Parent search records are preserved, and only actually executed new queries are appended.

## Unfinished work

None in the one-level split. The existing dependencies retain their own stage states; their proofs are not asserted to be completed by this delivery.

## Not duplicates

No new nodes. Existing general flag geometry, quotient geometry, fpqc descent, proper reduced global sections and the affine adjunction are reused, rather than introducing special cases of them.

## Review by Q18

I checked B--E against the node and the local sources, including the distinction between a cited statement and its proof. This is the direct-delivery worker's review authorized by the brief; the maintainer's independent review is still required.

Step 1 uses `lem-sfb-general-borel-flag-variety` for a nonempty smooth connected proper separated finite-type X, a rational point x and stabilizer B, and transitivity on X(F). Its statement gives each of these. `lem-sfb-smooth-group-orbit-geometry` gives the reduced orbit as a locally closed subscheme. `lem-weil-pbc-closed-point-residue-field-base` and `lem-sc-lft-over-field-jacobson-space` respectively say that every closed point is rational and that closed points lying in any closed subset are dense in that subset. Hence all closed points lie in the orbit, its closure is X, it is open, and a nonempty closed complement is impossible. This is the explicit short argument, not an uncited orbit-surjectivity assertion. `sbc-lem-smooth-geometrically-reduced` applied to X over Spec F ensures X is reduced, so the reduced full-open orbit agrees as a scheme. I checked finite type, algebraic closedness and smoothness at their uses. I did not assume the group reductive.

Step 2 applies `lem-sfb-homogeneous-orbit-quotient-geometry` with G=A and H=B, to the action on this separated finite-type X. Its statement gives the quotient-orbit isomorphism, faithful flatness and the exact kernel-pair isomorphism (a,b) |-> (a,ab), including nonreduced subgroup schemes/test rings. `lemma-nagata-finite-type-to-separated-target` clause (b) applies because A/F is finite type and X/F is separated; it gives quasi-compactness of q. The singleton covering condition is then checked directly from `def-weil-pbc-fpqc-covering`: preimages of affine opens are quasi-compact, finite affine covers have images covering those opens, and q is flat and surjective. This checks the actual hypothesis of descent rather than silently declaring a faithfully flat map fpqc.

Step 3 uses `def-sc-group-scheme` for the morphisms of multiplication, inverse, and the homomorphism identities. The displayed multiplication orders are important: (v(a)v(b))^{-1}=v(b)^{-1}v(a)^{-1}; no commutativity of D is assumed. The equality u|B=v|B holds as morphisms, so the calculation holds as an identity on A times B over every algebra. `lem-weil-pbc-fpqc-representable-descent` states exactly that compatible morphisms on an fpqc covering glue uniquely. The kernel-pair formula from step 2 verifies compatibility, and applying its uniqueness to maps to Spec F verifies that the descended map is over F. I read Stacks descent.tex, label lemma-fpqc-universal-effective-epimorphisms (023Q), which states this sheaf condition.

Step 4 uses `lem-weil-pbc-proper-reduced-algclosed-global-sections-product`, whose statement identifies the *structural* F-algebra map from the finite product indexed by connected components. X is nonempty and connected, so this product has one factor; X is proper and reduced by step 1. I read varieties.tex, label lemma-proper-geometrically-reduced-global-sections (0BUG), especially clauses (1)--(3). For a proper reduced connected scheme over an algebraically closed field these yield exactly F. `lem-a1-locally-ringed-space-affine-adjunction` states a natural bijection between maps into Spec C and ring maps C into global sections. I read schemes.tex, label lemma-morphism-into-affine (01I1). Its naturality identifies the descended morphism with d composed with the structural map, because their global-section maps agree. The F-algebra structures ensure d is an F-point. No further geometric connectedness hypothesis is added.

Step 5 cites only the definition of group schemes and is elementary: evaluating the *constant morphism* at e_A makes its value e_D, and multiplying the difference identity on the right by v gives u=v. These are identities of scheme morphisms; the final all-algebras formulation is their functor-of-points expression, including nilpotent algebras.

All proof steps are shorter than 2000 characters (1011, 828, 826, 878, 568 at writing). The orbit comparison is the routine consequence of the five cited statements written out in step 1; the descent and global-functions arguments have their non-elementary inputs cited. There is no unmentioned comparison lemma or subclaim left inside a long step. I checked dependency reach for the flag, quotient, global-functions and affine-adjunction inputs and found no path back to this item. Off-unit citations are recorded as generic tools in split_report.tool_uses; no unit route is replaced.

For small cases, if A is solvable then B=A and X is a point; the same proof becomes immediate restriction equality. The trivial group and zero-dimensional smooth connected affine group give the same case. For SL2, X is the usual P1, so the proper/affine argument has its expected content. Positive characteristic is allowed throughout; no differential-injectivity or separability of u or v is used. D can be noncommutative, as the displayed ordered cancellation confirms. The properness and reducedness checks explain why replacing X by an arbitrary nonproper or nonreduced scheme would not justify the constancy step. There are no new statements requiring separate small-case tests and no new source requests.
