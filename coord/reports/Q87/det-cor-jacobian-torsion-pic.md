# det-cor-jacobian-torsion-pic — Q87

## Files written

- `dag/nodes/sec-picard-framework/det-cor-jacobian-torsion-pic.json`: statement, split into five proof steps using four existing nodes; statement unchanged. No new nodes and no Mathlib leaves created.
- `citations.json`: a verbatim statement excerpt for each step/node use.

The sandbox was empty apart from dispatcher markers when this continuation began. No delivery process was active. Searches performed in this continuation are preserved in `searches.jsonl` and recorded exactly in the item's `mathlib_searches`.

## Attachments

`AlgebraicGeometry.surjective_npow_points` belongs to existing `lem-sc-isogeny-surjective`, `WeilConjectures/AlgebraicGeometry/AbelianVariety/Isogeny.lean:390`. This attachment is already reflected in that node's closed slopmaster2 audit. The actual source statement applies to every positive n, without a characteristic restriction.

`AlgebraicGeometry.Scheme.exists_mulEquiv_prod_ker_picDegreeHom`, `WeilConjectures/AlgebraicGeometry/Curve/Picard.lean:383`, states the degree-compatible decomposition of existing `lem-sc-pic-proper-decomposition`. Its source proof contains no sorry; this is an attachment candidate for that existing node, not a claim that its entire transitive proof has been independently certified here. No other node was edited.

The project searches for the item's exact blueprint tag and for Jacobian/Picard torsion, quotients and degree found no project declaration giving every clause of this item. In particular the above two results are ingredients, not an attachment for the whole item. Upstream master is not used as evidence of completed proofs.

## WANTED

None. The item and unit proofs and the existing dependency statements are available locally. The proof origin remains agent-written because the blueprint proof is agent-written and the diagram chase is expanded here.

## Corrections and route

The imported statement is correct and is retained verbatim. In particular the item deliberately asserts the Picard conclusions for all positive n, not just n invertible in k. No STATEMENT-DISPUTED is needed.

The imported proof had an unjudged step (`elementary: null`), omitted real dependencies from the `uses` arrays and from `proof_deps`, and referred to nonexistent current DAG ids `sk-prop-av-mult-surjective`, `sk-prop-av-isogeny`, `sk-prop-av-divisible` and `sk-cor-picard-degree`. I did not recreate these labels. Existing `lem-sc-isogeny-surjective` is exactly the general divisibility fact, in the unit `sk-prop-av-divisible` that our unit already cites. Existing `lem-sc-pic-proper-decomposition` states the required exact degree sequence for exactly our hypotheses. Its use as a generic tool is declared in `split_report.tool_uses`, since the absent `sk-cor-picard-degree` label supplies no current node. I use only the degree sequence, not the extra choice of its splitting.

This realizes unit `sk-cor-jacobian-torsion`, step 4: divisibility on geometric points and the kernel/cokernel calculation for multiplication by n in the degree sequence. The proof uses the existing divisible-points lemma as the black box the unit expressly names. Its finite-fibre argument is already below that lemma. The snake-lemma conclusion is written out as its elementary element chase, so no new general snake-lemma node is needed. Chapter and unit records are unchanged: this item is the detailed Picard clause, not the unit's entire key statement.

## Mathlib searches and duplicate checks

Ran LeanFinder twice with different mathematical phrasings, LeanSearch, Loogle twice, and Mathlib grep twice using the required msearch command. All actual queries/results are preserved. The first Loogle pattern failed because `Picard` is unknown; this is explicitly recorded as a query error, not as evidence of absence. The second substring search returned unrelated metaprogramming names. LeanFinder/LeanSearch returned Weierstrass Jacobian coordinates, elliptic point/class-group constructions or function-field class numbers. I read `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Basic.lean`, especially its explanation of Jacobian coordinates and its abbreviation at line 111: these are elliptic Weierstrass coordinates, not a theorem about the Picard group of every smooth proper curve. The grep hits do not establish our theorem either. Thus the item is not a Mathlib leaf.

Searched the whole DAG by statement concepts and the whole imported blueprint with `blueprint_refs.py search` for Jacobian, divisibility and the degree sequence, and checked the item's blueprint ancestor. Found and reused the existing general lemmas. The nearby `lem-sc-pic-proper-ntorsion` assumes n prime to the characteristic and gives the finite torsion structure; it does not state this item's arbitrary-positive-n assertion. The other detailed Jacobian torsion nodes address the étale kernel, base extension and group structure. No other blueprint node states all clauses of this item, so `same_as` is empty.

## Not duplicates

No new nodes. In particular no fresh divisibility, degree-sequence, torsion-identification or quotient lemma was introduced.

## Review by Q87

I read `dag/chapters/sec-picard-framework.json`, `dag/units/sk-cor-jacobian-torsion.json`, the current `main-20261015` item statement and `.proof.md`, and the source for the general divisible-points proposition. I also read the older blueprint source for `lem-sc-pic-proper-decomposition` and its actual Lean statement and proof. I checked delivery-errors B through E against the node and sources. There are no new nodes needing source, search, self-containedness or statement-only checks; existing source/checklist data were not silently rewritten.

Step 1: `sk-thm-picard-main` explicitly says that J is an abelian variety and identifies its k-points with Pic^0(C). `lem-sc-pic-proper-decomposition` explicitly displays the exact degree sequence and surjectivity. Both assume exactly an algebraically closed field and a proper smooth connected curve. Their combination supplies the displayed sequence, including its kernel, not merely representability. I read both complete statements; the citations quote the relevant main-theorem sentence and the exact degree sequence.

Step 2: `lem-sc-isogeny-surjective` says that [n] on A(k) is surjective for an abelian variety over an algebraically closed field and every n >= 1. Step 1 supplies the abelian variety. No étaleness, finite reduced kernel or invertibility is assumed. The source Lean statement agrees and makes the characteristic-independent quantifier explicit. This proves divisibility rather than inferring it from scheme-theoretic surjectivity alone.

Step 3: `sk-def-av-mult-n` gives precisely the fibre-product/kernel definition, so evaluating its universal property on Spec k gives points killed by n. The degree-sequence node supplies a homomorphism with zero-degree kernel. The integer calculation n deg(L) = 0 implies deg(L) = 0 because n is positive; the inclusion then preserves the same n-torsion equation. This is an elementary three-line kernel chase, not an uncited classification or representability theorem. The Picard/Jacobian identification was established in step 1 and is not a new identification asserted here.

Step 4: the same degree-sequence node states surjectivity to Z. The formula deg(L+nM) = deg(L)+n deg(M) proves quotient well-definedness, and a lift of an integer representative proves surjectivity. There is no need to cite a general quotient-exactness result for these two elementary checks.

Step 5: I checked both integrality conditions used in the chase: degree zero modulo n means an actual equality deg(L)=nm with m an integer, and surjectivity of degree supplies M of degree m even when m is negative. Thus L-nM is in the degree-zero kernel. Step 2 provides B in J(k) with nB=L-nM. The explicit equation L=n(M+B) proves the quotient kernel is zero. Bijectivity gives a group isomorphism, with additivity of the inverse justified by injectivity. The isomorphism is the degree map asked for, not an unspecified abstract decomposition.

Small cases: n=1 gives zero torsion and zero quotients on both sides. For genus zero, J(k)=0 and degree identifies the whole Picard group with Z, producing exactly the stated torsion and quotient. In characteristic p with p dividing n, no prime-to-p torsion formula has entered; the general divisible-points lemma still applies. The positivity hypothesis matters in the integer torsion step; n=0 is excluded throughout. These checks found no needed statement correction.

I checked that every uses entry is an existing, unmerged node and that proof_deps is their exact union. All quotations in citations.json are literal substrings of the cited current statements. Every step has a source and a Boolean elementary flag; none exceeds 2000 characters or hides an auxiliary geometric lemma. The substantial inputs are the cited Jacobian theorem, divisible-points lemma and degree sequence. No new axiom, Lean file, compiler, Lake invocation or live-project write is involved.

## Unfinished work

None in this one-level split. The cited nodes retain their own independent statuses and are not modified by this delivery.
