# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-additive-subgroup-commutative-extensions-witt.json: item split in six steps; statement and hypotheses retained verbatim; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-symmetric-polynomial-cocycle-normal-form.json: new statement-only lemma, unsplit; no Mathlib match. This is Milne Lemma 15.26's polynomial existence assertion, independent of group-scheme extensions and without a perfection hypothesis.
- citations.json: one verbatim statement quote for each node used in each item step.

## Attachments

None. Searched lean/WeilConjectures by the blueprint tag and by Witt, commutative extension, symmetric cocycle, polynomial cocycle, and Hochschild-related notions; the Witt hits are isocrystal-independent Hall--Witt Lie identities and unrelated Artin--Schreier--Witt comments. No project declaration states the item or the new lemma. Also checked the relevant GroupScheme, RingTheory and RepresentationTheory source and Sheaf algebraic geometry source. No Lean file was written and no compiler was run.

## Literature

No WANTED documents: all assertions delivered are sourced to literature/milne-algebraic-groups_iAG2017.pdf. Read Proposition 15.27 on printed pp.316-317, Lemma 15.26 on p.316, Proposition 15.10 and Corollary 15.11 on pp.308-309, and the explanation of additive torsors preceding the extension computation on p.314. The two previously existing supporting nodes give the torsor-section statement from Example 2.72 and the monic additive subgroup polynomial from Exercise 14-3(a). The new node cites Milne 15.26 itself, not the Demazure--Gabriel or Lazard references which Milne mentions but whose contents I have not read. No SGA source is used.

## What needed checking

The imported statement is correct with its perfect-field hypothesis; no STATEMENT-DISPUTED correction is needed. The source's one-line bounded-degree lifting assertion needs an actual proof, especially when Q is nonreduced. Step 3 supplies it by observing that the cocycle defect has degree less than n in each of three variables, so it equals its own monic remainder. The step does not lift identities merely from geometric points.

Milne's inference from an arbitrary linear combination of Frobenius powers of the Witt cocycle to one pullback also needs care: postcomposition on the kernel does not preserve the identity on the given kernel. Steps 4 and 5 instead choose p-th roots b_i of the coefficients a_i, form h(T)=sum b_i T^(p^i), and calculate the second-coordinate correction B(T) by adding the vectors (b_i T^(p^i),0) in W_2. Step 6 uses the resulting explicit coboundary to produce an isomorphism which really induces the identity on both ends. No hypothesis is dropped or added.

## Searches and duplicate audit

The item's existing Mathlib searches were read and retained: their hits are abstract group extensions, Witt-vector constructions, isocrystals and cotangent modules, which do not give the group-scheme extension classification. Before creating the new node I searched all DAG statements and source places for 15.26, symmetric cocycles, polynomial cocycles and extensions, and searched the project Lean source. The whole-blueprint search command found no match for Witt, symmetric cocycle, polynomial cocycle, Lazard or additive subgroup; the newest blueprint text was also searched directly. Blueprint searches for monic led to the existing monic quotient support, which is reused.

Six actual msearch.py calls for the new polynomial lemma are recorded in searches.jsonl and exactly copied as queries into its mathlib_searches. Both semantic phrasings return Witt polynomial/coordinate identities, not a theorem classifying all symmetric polynomial cocycles. The Loogle search for WittVector and cocycle returns no hit. The first grep returns no hit; the second returns only the comment at Mathlib/RingTheory/Flat/EquationalCriterion.lean:44 about the unrelated theorem on flat modules. No unavailable service was treated as an absence result.

## Not duplicates

lem-sfb-symmetric-polynomial-cocycle-normal-form vs lem-sfb-additive-subgroup-commutative-extensions-witt: the new node is a polynomial identity on the full additive line over any field of prime characteristic; it neither mentions nor classifies group-scheme extensions or constructs a Witt pullback. The item additionally proves the torsor reduction, restriction-surjectivity for every closed subgroup, conversion of the polynomial class to a single pullback over a perfect field, and the normalized isomorphism of extensions.

lem-sfb-symmetric-polynomial-cocycle-normal-form vs lem-sfb-length-two-witt-extension-verschiebung: that node constructs the Witt group and computes Verschiebung; it does not state any normal form for arbitrary cocycles.

lem-sfb-symmetric-polynomial-cocycle-normal-form vs lem-sfb-disjoint-symmetric-two-cocycle-integration: the latter concerns multiplicative functions on disjoint subsets of a finite set, not polynomial additive cocycles in prime characteristic. Its potential assertion does not imply this normal form.

## Review by Q72

I read the item against Milne Proposition 15.27 and the new node against Lemma 15.26, with the definitions of symmetric cohomology on pp.308-309 open. The new statement writes the normalized cocycle equation and the coboundary out, defines the integral polynomial before reduction, introduces every object, and cites the existing field and polynomial-ring definitions. It is left statement-only. The existence part follows exactly from Milne's normal form; no uniqueness claim beyond what is needed has been added.

For step 1 I opened def-sc-group-scheme, def-pc-fibre-product and lem-sfb-additive-affine-torsor-section. The last statement explicitly allows any affine base, has no smoothness or reducedness condition, and supplies the section for the action isomorphism which the step proves using the scheme-theoretic kernel. Faithful flatness and finite presentation are hypotheses of the item, not consequences inferred from finite type. I wrote the inverse to the translation map and the inverse to the chosen trivialization, so no torsor classification theorem is hidden here.

For step 2 the cited group-scheme definition supplies the group law and commutativity, while def-weil-affine-spectrum gives the contravariant algebra-map correspondence and def-weil-pbc-mv-polynomial-ring gives evaluation and uniqueness. The three cocycle conditions are obtained directly from the actual group law. The coordinate algebra of a product follows from the described polynomial quotient's universal property; there is no use of smooth points or an unstated cohomological comparison.

For step 3 I read the exact statements of lem-sfb-additive-subgroup-polynomial-quotient and lem-weil-pbc-monic-quotient-free. The first supplies the positive-degree monic defining polynomial and its zero constant term for a proper closed subgroup, and the second supplies the monic remainder basis over every commutative coefficient ring, as needed successively in three variables. I checked each substitution in the defect: in F(X+Y,Z) both new exponents are at most the old X exponent, and in F(X,Y+Z) both are at most the old Y exponent. Thus no degree reaches n, which is exactly why vanishing in the quotient proves the polynomial identity. This is not a new general lifting lemma.

For step 4 the new node supplies exactly F=sum a_i c_p^(p^i)+delta b with b(0)=0. Perfectness is used only to choose the finitely many roots b_i^p=a_i; the additive polynomial h then defines the group homomorphism by the cited affine/polynomial definitions and def-sc-gm-ga. I did not assume the original cocycle itself was already a Witt pullback.

For step 5 I opened the complete statement of lem-sfb-length-two-witt-extension-verschiebung: it supplies precisely the displayed commutative polynomial group law, zero, injection j and projection tau. This step uses its group-law clause, not its Verschiebung clause. Regrouping a finite sum in a commutative group is elementary. Homogeneity and the fact that c_p's coefficients lie in the prime field give the stated equality for each pair of summands. I checked the sign: c_p(h(X),h(Y)) equals sum a_i c_p(X,Y)^(p^i) minus delta B, so the correction in F is delta(b+B).

For step 6 the fibre-product statement supplies its actual points/universal property; the affine-spectrum statement makes the displayed coordinate formulas into morphisms; and the Witt node supplies the kernel and quotient coordinates. I checked both composites, the homomorphism equation and the restriction at x=0. The correction is t+u(x), with inverse v-u(x), so both the original kernel and quotient are fixed. The second projection then gives both requested equations. These are direct calculations, not a new extension-equivalence theorem.

I checked small cases: Q=0 has P=T, n=1, so the normalized representative is zero and E is its kernel; Q=Ga uses the polynomial lemma without any finite quotient. For alpha_p and alpha_(p^r), the quotient/remainder argument works in nilpotent coordinate rings unchanged. Disconnected finite additive subgroups likewise use the same polynomial identities. For p=2 the Witt cocycle is XY; adding two terms introduces the expected cross-term coboundary B, which confirms why the B correction is necessary. A split extension admits a homomorphic section giving F=0 and all coefficients zero, hence h=0. No test relies on algebraic closure. Every step has a definite elementary flag, every non-elementary input appears in uses, and proof_deps is precisely their union. Each step has fewer than 2000 characters; no sublemma was hidden by compressing a long argument. All cited statement quotes in citations.json are literal full statements read from the current node files. Definitions and the Mathlib monic-quotient leaf are permissible generic tools; the remaining support is in the item's own unit.

The latest blueprint proof is literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3). It gives the ambient compactification/direct-image route, not this much deeper algebraic-group lemma. I retained the inherited complete support chain and the null ancestor returned by blueprint_refs.py ancestor, and filled the new node's exact supporting place in Milne. No chapter or unit route was changed.

## Unfinished work

None for this one-level split. The new polynomial lemma is deliberately unsplit and is a subsequent stage-1 item. Required dry run and delivery results follow below.
