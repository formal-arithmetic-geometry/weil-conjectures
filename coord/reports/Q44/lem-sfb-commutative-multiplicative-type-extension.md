# Stage-1 delivery: lem-sfb-commutative-multiplicative-type-extension

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-commutative-multiplicative-type-extension.json`: item split, original statement retained; three assembly steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-multiplicative-additive-vanishing-criterion.json`: new statement, unsplit, no Mathlib match after both mathematical and Hopf-algebra phrasings.
- `dag/nodes/sec-six-functors-basics/lem-sfb-faithfully-flat-group-quotient-universal.json`: new statement, unsplit, no Mathlib match after two phrasings.
- `citations.json`: four verbatim quotations, covering every step/node pair.
- `searches.jsonl`: actual search-command log, retained unchanged.

## Attachments

None. Searched the item blueprint tag and diagonalizable/multiplicative-type concepts in `lean/WeilConjectures/`; there is no matching declaration. Source-library mentions of diagonalization are unrelated linear algebra.

## WANTED

None. Both new statements and the item's argument have the obtained Milne source.

## Findings and source correction

The imported statement is correct and unchanged. Its empty proof becomes the Hom-to-additive-group argument in Milne, Corollary 12.22, printed p.239. Milne's final sentence says criterion (12.18c), although the displayed theorem labels the no-additive-homomorphisms condition (b); the proof uses Theorem 12.18(a),(b),(d), not an unproved implication from commutativity alone. This is a label correction, not a change of theorem or route. No SGA source is used.

I read the current chapter and unit records and the latest blueprint direct-image proof at `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3). This item is a supporting algebraic-group lemma far below the recorded alteration/moduli prerequisite; neither chapter nor unit route is changed. `blueprint.from.node` remains null exactly as the ancestor command reports, with the full inherited supporting chain retained and extended for each child. The item is not a unit key node, so no unit record is edited.

## Not duplicates

lem-sfb-multiplicative-additive-vanishing-criterion vs lem-sfb-multiplicative-character-antiduality: character antiduality classifies groups already known to have multiplicative type; it does not detect that property from the vanishing of all maps to the additive group.

lem-sfb-multiplicative-additive-vanishing-criterion vs lem-sfb-diagonalizable-group-geometric-criteria: that node computes smoothness and connectedness of specified group algebras, and contains no additive-Hom criterion.

lem-sfb-multiplicative-additive-vanishing-criterion vs lem-sfb-unipotent-to-multiplicative-trivial: the latter has a unipotent source and multiplicative target, the opposite direction to the additive-Hom criterion here.

lem-sfb-faithfully-flat-group-quotient-universal vs lem-weil-pbc-fpqc-representable-descent: the existing statement descends a compatible morphism along a covering; the new statement starts with coordinate faithful flatness and trivial restriction to a scheme-theoretic group kernel, and asserts the unique descended group homomorphism. The missing kernel-pair invariance, quotient condition and group-law compatibility are substantive inputs to its future split. It is Milne's separate Theorem 5.13, not a new node for the item's conclusion.

lem-sfb-faithfully-flat-group-quotient-universal vs lem-a1-fppf-kernel-pair-quotient-descent: that node requires a finite locally free surjection and a specified kernel-pair equivalence relation and constructs a sheaf quotient. The new statement assumes only a faithfully flat coordinate map of finite-type affine groups, allows nonfinite kernels and descends homomorphisms annihilating that kernel.

Whole-DAG searches covered Milne 12.18, 5.13 and 5.43, multiplicative type, diagonalizable/diagonalisable, primitive/coetale and faithfully-flat quotient/descent wording. Whole-blueprint searches included multiplicative type, diagonalis, diagonalizable, additive group scheme, quotient homomorphism, faithfully flat quotient and primitive. No blueprint node states either new lemma. Existing general descent nodes are recorded above rather than silently duplicated. No Stacks-tag duplicate pair arises: these new sources are Milne theorems, not new Stacks citations.

## Review by Q44

I checked the argument against Milne Corollary 12.22 (p.239), and read Theorem 12.18 and its entire proof on pp.237–238 for the criterion child. Its conditions apply to affine finite-type group schemes without smoothness: the proof uses finite subcoalgebras of the coordinate Hopf algebra, finite local Artinian dual algebras, a dual-number quotient producing a nonzero primitive element if such a factor is not a field, and the group-like basis when all factors are fields. Algebraic closedness makes the separable closure in condition (d) equal to the given field. The finite-type diagonalizable convention gives a finitely generated character group, matching the item's exact D(M) convention. This is a genuine detection lemma, independent of extensions, rather than a restatement of a clause of the item.

For the quotient child I read Milne Theorem 5.13 (p.101), its functorial proof, Definition 5.5 and Proposition 5.7 (p.99), and Proposition 5.43 (p.107), which supply the quotient-map interpretation of the stipulated faithful flatness. The source descends from cosets in all algebra-valued points, not just geometric points. The new statement keeps the equality on the scheme-theoretic kernel and the coordinate faithful-flat hypothesis, so it does not accidentally assume surjectivity on points over every algebra. The original source proof extends the coset-functor map uniquely and checks the descended group law. This input applies to any affine finite-type group target and uses no commutativity hypothesis, which makes it independent of the multiplicative-type extension conclusion.

In step 1, the criterion's forward implication is used with G=N and G=Q; both have precisely the specified group-algebra presentations. In step 2, the restriction of an arbitrary u:E→Ga to N is zero by step 1, so the quotient lemma gives a group homomorphism v:Q→Ga with u=vq. I opened def-sc-gm-ga and checked that it defines Ga as Spec k[y] with its additive comultiplication, hence the affine finite-type target required by the quotient lemma. Step 1 then kills v, proving u=0. Step 3 uses the reverse implication of exactly the same criterion with G=E: the statement assumes commutativity, and step 2 supplies its other hypothesis. Every uses entry is represented by a verbatim statement excerpt in citations.json. There is no use of a definition node as a theorem, no suppressed flatness-to-exactness argument, and no unproved descent hidden in the assembly.

I tested the statements on the trivial group D(0), on q=id, and on q:E→1: the conclusions reduce correctly. In characteristic p, μ_p and μ_(p²) are allowed diagonalizable nonreduced groups, so the sequence with p-power map does not force a smoothness assumption. By contrast α_p maps nontrivially to Ga by its defining closed immersion; the criterion therefore correctly excludes it. Dropping commutativity would admit the monomial-matrix counterexample from Milne Example 12.10, so I kept that hypothesis exactly. No new node is elementary or an extension clause: the two inputs concern detection and descent. All three item steps are below 2000 characters, and no new node contains proof steps or a proof sketch in its statement.

Mathlib's returned Scheme.Hom.liftQuotient is factorization into a closed subscheme, not descent through q. QuotientGroup.kerLift only handles abstract groups, and Flat.epi_of_flat_of_surjective provides uniqueness but not the factorization existence or kernel compatibility. Hopf group-like element results do not assert spanning or the additive-Hom detection theorem. Accordingly both children remain unsplit, with actual successful queries and their hit summaries recorded. No compiler, Lake or Lean-writing tool was run, and all writes are inside this sandbox.

## Unfinished work

No part of the item's split is left unfinished. The two new statements are intentionally unsplit, as required for a one-level stage-1 split. They await later workers.
