# Q24: lem-sfb-dg-shifted-character-dual-hom

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-dg-shifted-character-dual-hom.json: existing statement node, now split into six elementary calculations; not a Mathlib leaf.
- citations.json: empty list, because all six proof steps use only the definitions stated explicitly in the item and earlier calculations of this proof, and cite no DAG nodes.
- report.md: this report. searches.jsonl contains the unmodified output records written by msearch.py.

There are 0 new nodes and 0 Mathlib leaves. The statement, statement dependencies, inherited blueprint provenance and prior Q05 searches are retained. The sandbox was empty except for dispatcher markers when this resumed turn started; there was no interrupted deliver.py process to repeat.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, character-dual terminology, DG algebra/module terminology and coinduction. No declaration states either complete identification for arbitrary right DG modules. The ordinary-module and sheaf coinduction declarations do not cover DG modules.

## WANTED

None. The source is available locally.

## Corrections and route

Stacks dga.tex, Tag 09K4 (lemma-hom-into-shift-dual-free), states both identifications but its proof says only that they follow from the preceding discussion. I supplied the missing explicit evaluation inverse and the differential/homotopy signs rather than cite an unstated adjunction. The imported statement is correct, including the unchanged action on a shifted right DG module, and is not modified. No statement dispute was found.

I read the three-level rules in SETUP.md, the chapter and unit records, and the current blueprint latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. The unit record still reflects an older snapshot and chapter assignment, but this item's inherited source-level role is unchanged: Tag 09K4 supplies the character-dual layers used by Tag 09KS, along the inherited direct-image prerequisite chain. No change to a unit or chapter is proposed. blueprint_refs.py ancestor reports no imported blueprint ancestor; that inherited null is preserved. Searches across the imported blueprint for 'character dual', 'dual free' and '09K4' returned no matches. The DAG tag search finds this item, its ancestors and the good-character embedding construction, rather than another node stating this item's two identifications.

The six new logged searches were read, including a second semantic phrasing. CharacterModule.homEquiv (Mathlib/Algebra/Module/CharacterModule.lean:145-147, with commutative-ring assumptions read at lines 35-42) is an ordinary module tensor/character adjunction. CochainComplex.HomComplex.CohomologyClass.homAddEquiv (Mathlib/Algebra/Homology/HomotopyCategory/HomComplexCohomology.lean:170-173) handles ordinary complexes, without the DG-algebra coinduced target identification. Neither is a one-line specialization giving the item. Loogle's HomComplex/dual query and the DG-specific source grep found no hits. All searches added to the node are copied from searches.jsonl with their original tool/query/results; the existing creator's searches remain intact.

## Not duplicates

No new nodes were created. No duplicate pairs require justification.

## Review by Q24

I checked the full statement against both displays of Stacks Tag 09K4 and read the surrounding graded and DG character-dual conventions in dga.tex. I also read the statement of def-weil-size-convention, the sole statement dependency. It fixes the ambient universes, and is not used for an algebraic assertion in any proof step. All other notions are explicitly defined in the item. No new node needs an additional source.

Step 1 checks the objects' consistency directly: the unit Leibniz identity gives d_A(1)=0; two dual differentials compose to zero; expanding d_A(ab) gives exactly the right DG-module Leibniz rule with the stipulated action. The shift sign agrees with the shifted degree of an element. No injectivity, dual exactness, or cohomology comparison theorem is used.

Step 2 writes both directions of the degreewise correspondence for arbitrary t, including the precise degree of a, m and ma. The equalities (mc)a=m(ca) and phi(ma)=phi(m)a prove right linearity and both inverse identities. This is a two-line uncurrying calculation, not a new coinduction lemma. It is performed for all homogeneous degrees and extended additively.

Step 3 expands the chain defect. I checked the cancellation coefficients (-1)^(p+t) and -(-1)^(t+p), and the identity E_(t+1)(delta phi)=(-1)^k d_D E_t(phi). The latter uses (-1)^(k+t+1) in the degree k+t dual differential, and d_A(1)=0 eliminates the target differential term. It does not assert that the unmodified evaluation is a chain map when k is odd.

Step 4 uses precisely the t=0 calculation and the injectivity of the explicit E_1 to identify the chain-map condition with the cycle condition, including the converse. Step 5 uses precisely t=-1. For a prescribed boundary d_D(mu), the homotopy is F_(-1)((-1)^k mu); its chain defect has the required evaluation, so injectivity of E_0 proves the full map equality. Thus both directions of the homotopy/boundary identification are proved, and the quotient maps are explicitly inverse and additive. These are direct calculations from the definitions of the two quotient groups.

Step 6 checks naturality on elements and checks separately that precomposition preserves chain defects and boundaries. The map u has both required properties: degree-zero A-linearity for the inverse formula and the chain-map identity for descent to cycles/quotients. This proves both naturality clauses for every DG module, without boundedness or finiteness assumptions.

For C1/C4, every step has uses=[] because each is an explicit calculation from inline definitions and earlier steps, not an invocation of a non-elementary fact. Consequently there are no cited-node statements to overread, and citations.json is correctly empty. In particular the proof does not invoke injectivity of Q/Z, the tensor-Hom adjunction, or a Hom-complex cohomology theorem. I did not turn those calculations into redundant nodes or move a clause of the item to a new node (D1/D2).

I checked small cases: M=0 gives two zero groups; A=Z in degree zero gives ordinary characters of a complex; a one-term M checks the shift index -k; the two-term identity-differential complex checks cycles and boundaries for k=0, k=1 and k=-1, with the sign (-1)^k in the homotopy formula. The associativity check retains the order acb and thus does not assume A commutative. The formulas apply to negative degrees as parity identities and contain no infinite sums. No step exceeds 2000 characters and no separate hidden comparison lemma is being used.

The checklist in delivery-errors.md B--E is satisfied: no new-node form or duplicate issue, all definitions needed for the argument are present inline, no citation substitutes for an argument, both implications and signs are written, and the source's omitted argument is supplied. All statements and hypotheses are preserved. No Lean was written or compiled; all writes are in this item's sandbox.

## Unfinished work

None in the stage-1 split. Independent maintainer review remains part of the delivery process.
