## Files written

- dag/nodes/sec-trace-formula/lem-trf-flat-pullback-associated-points.json: statement, split into six proof steps; no Mathlib match.
- No new nodes or Mathlib leaves. citations.json contains verbatim statements for all 13 step citations. searches.jsonl records the six searches made in this sandbox.

## Attachments

None. Searches of /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact blueprint tag, associated points/primes, associatedPoints, and assassin found no project declaration for this formula. The existing ring-theoretic DAG node has a landed Lean record, but is reused as a dependency, not offered as an attachment for this geometric statement.

## WANTED

None. All mathematical sources needed are present locally.

## Audit of the imported item

The statement is correct and unchanged: it is the specialization F=O_Y of Stacks Tag 05DB, divisors.tex, lemma-bourbaki. The empty proof is replaced. In particular, arbitrary quasi-coherent G and possibly non-Noetherian Y are preserved. I did not use lem-trf-associated-primes-fibre-bound, which requires both rings Noetherian and finite modules, or lem-trf-flat-tensor-weakass-fibre, which assumes finite presentation and uses weak association. Neither covers this item.

The source refers to algebraic 05C2. Creating a node for that entire formula would be unnecessary: the existing 0312 node supplies the algebraic union formula, and its needed passage from prime quotients to the closed fibre is written out here for the maximal ideal. This is a local calculation, not a new restatement of the geometric item.

Blueprint ancestor: lem-trf-local-term-locality, through the existing relative-assassin chain in blueprint.from. The unit sk-i-curve-zero and chapter sec-trace-formula are unchanged. Searches with tools/blueprint_refs.py for associated, associated points, Bourbaki, and 05DB found no blueprint statement of this item. Searches across the whole DAG by the tags and associated-prime/tensor/localization concepts located all reused nodes. No fresh id is needed. Generic off-unit tools are declared in split_report.tool_uses: pullback stalks, fibre stalk quotient, and Bourbaki 0312. These support the existing route through 05DB and 05DC; they do not replace a unit step.

## Unfinished work

None in the stage-1 split. No Lean was written or compiled, no build or Lake command was run, and all authored files are in the designated sandbox.

## Review by N8

I read divisors.tex Tag 05DB (lemma-bourbaki), including its proof setting A=O_{S,s}, B=O_{X,x}, M=G_s, N=F_x, and algebra.tex Tags 0312 (lemma-bourbaki), 05C1 (lemma-post-bourbaki), 05C2 (lemma-bourbaki-fibres), and 05E0 (remark-bourbaki). For the fibre identification I read algebra.tex Tag 0H9M (remark-local-ring-fibre); the cited scheme-level node gives exactly the compatible quotient map, sourced to Schemes 0HA1. The special case F=O_Y satisfies relative flatness because h is flat. The tensor unit identification removes F, so this is precisely the original statement.

Step 1 cites the definition of flat morphism, which explicitly states that the stalk map is local and B is A-flat. The locally Noetherian definition supplies a Noetherian affine neighbourhood. The affine-stalk localization statement, clause (c), identifies A with the prime localization, and the localization-Noetherian statement proves A Noetherian. This is the only ring to which a Noetherian hypothesis is applied. I opened these four statements and checked that no affine assumption on all of Y or Z is inferred.

Step 2 uses the pullback-stalk node's displayed isomorphism for any module, not just finite or quasi-coherent modules. The relative-assassin definition defines ordinary associated points by exact annihilators in the stalk. The scheme-fibre-stalk-quotient node explicitly gives O_{Y_z,y_z}=B/m_A B by the actual projection stalk map, for arbitrary scheme morphisms. This avoids an uncited localization or coefficient comparison. The quotient of a local ring by an ideal contained in its maximal ideal is local with the indicated maximal ideal: elements outside that ideal's image are units, and the image ideal is proper.

Step 3 uses only the statement of the existing general Bourbaki 0312 node. It assumes R Noetherian, N R-flat, M arbitrary, and S arbitrary; take R=A, S=N=B. It yields the displayed union over Ass_A(M) with terms Ass_B(B/pB). It does not itself identify p as m_A, so step 4 supplies that argument explicitly.

Step 4 cites flat-tensor-exact for injectivity of the tensor of multiplication by a on A/p, and tensor-over-quotient-ring clause (1) for the identification with B/pB. I checked those statements have no finite-generation or Noetherian restriction. Their tensor quotient map sends r-bar tensor b to phi(r)b, so it intertwines the multiplication maps as claimed. A nonzero witness with annihilator m_B cannot be killed by an injective multiplication. Locality puts phi(m_A) in m_B and thus forces p=m_A. This works even when B is non-Noetherian; no localization theorem for associated primes or finite-module prime avoidance is hidden in the step.

Step 5 is elementary from the surjection B to C: the annihilator of the same element pulls back, and inverse image is injective on quotient-ring ideals. The only cited node is the definition of associated points, whose statement says exactly how this algebraic condition defines fibre association. Step 6 combines both directions separately and uses that definition for z and the scheme-fibre definition's stated homeomorphism onto h^{-1}(z) to identify the union as a subset of Y. It does not assume a fibre point exists over an unrelated z.

I checked C1 and C4 for every citation against the opened statements; citations.json copies their complete statements verbatim. No step uses the proof of a cited node. I checked the dependency closure of each proof dependency has no path back to the item. All six steps are under 1,000 characters, so no long step hides another lemma. B1–B9 and D1–D5 introduce no new-node obligations here: nothing is relabelled, no proof clause is moved to a fresh node, and the statement dependencies still define the notions used.

Small cases checked: G=0 gives no annihilator equal to a proper prime on either side; Y empty gives two empty subsets; h=id reduces to the same associated-point condition since the fibre at a point is its residue field; and Z=Spec(k) with G nonzero allows an arbitrary non-Noetherian Y and arbitrary-dimensional G. In the latter case m_A=0 and step 3 reduces directly to association of O_Y; no finite-dimensional basis or finiteness claim is needed. Non-surjective flat maps cause no problem: the union contributes no point outside each actual fibre. I found no statement dispute. The substantive repair is exposing the prime-contraction argument in step 4 instead of silently replacing the prime in Bourbaki's formula by the base maximal ideal.

Mathlib searches were actually run through msearch.py in two phrasings. I read the returned types and checked AssociatedPrime/Localization.lean, especially the declarations at lines 80 and 118: they require a localization and do not handle arbitrary flat pullback. Morphisms/Flat.lean lines 81 and 102 supply base-change stability and flat stalk maps, not the associated-point formula. The grep searches of AlgebraicGeometry for association and of RingTheory for association with Flat/Tensor were empty. All queries and actual hit summaries are retained; there were no unavailable services and no recorded searches invented for this report.
