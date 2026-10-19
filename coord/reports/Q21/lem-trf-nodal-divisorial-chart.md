1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-nodal-divisorial-chart.json` — split statement, no Mathlib match; the original statement and its statement dependency are unchanged. Six explicit elementary calculations replace the empty proof.
- `citations.json` — the two node citations, one in step 1 and one in step 3, with verbatim excerpts from `def-trf-fs-log-blowup`.
- `searches.jsonl` — actual mandated Mathlib search evidence; retained the imported search records and appended the queries executed for this item.

No new DAG nodes and no Mathlib leaves. Uncommitted supporting-node drafts were removed after self-review: the normal-form and algebra calculations can be written explicitly in short steps, so separate nodes would add needless queue work. The abandoned-draft searches are retained as evidence, not claimed as finished nodes.

2. Attachments: none. Searches of `WeilConjectures/` in the read-only slopmaster2 checkout for the exact blueprint tag and the nodal/divisorial monoid notions found no exact project declaration. The upstream-master checkout is reference material only and was not used to claim completion.

3. WANTED: none.

4. The imported statement agrees with the cocartesian square and cartesian monoid-ring square of ILO Exposé VI, Proposition 1.9, printed p. 71. There is no statement dispute and no statement change. The source calls Q fs and gives the group calculation without the elementary details supplied here. The proof is accordingly labelled agent-written, with its exact documentary anchor. The item inherits historical ancestry through `lem-trf-nodal-log-regularity` and `lem-trf-nodal-pair-projective-resolution` to `lem-trf-local-term-locality`. The current ancestor/unit follows contracting correspondences, whereas this supporting node was created for the older nearby-duality input. I retained the existing unit/chapter/ancestry and stated that historical place explicitly; no unit or chapter route was changed.

5. Nothing is left unfinished in this split. All work is stage 1: no Lean file was written and no compiler, Lake or build command was run.

## Not duplicates

No new nodes are delivered. Whole-DAG and blueprint searches for nodal divisorial charts, the cocartesian monoid square, fine saturated monoid pushouts, monoid rings, and cokernel Z produced no equivalent blueprint statement for the item. Related existing log-regularity and chart nodes use this item rather than state its algebraic assertion.

## Review by Q21

I read the chapter and unit records, the target and its neighbouring nodal-log-regularity/etale-chart nodes, the full statement of `def-trf-fs-log-blowup`, and ILO Exposé VI §§1.1–1.9, especially the two squares on printed p. 71. The exact relation is u+v=e+a, with e the invertible generator of Z; the epsilon factor is therefore retained. The proof follows this construction and writes out what the source asserts. No SGA source is used.

Step 1 uses only the integrality clause of the cited fs definition and the item's explicitly defined monoid congruence. The map to H=Z⊕Z⊕P^gp has u↦(1,0,0), v↦(-1,1,a), (n,p)↦(0,n,p); the relation has equal images. Replacing k paired generators by k(e+a), for k=min(x,y), gives the written normal representative. Step 2 uses that calculation alone: the two branch coordinates, the integer coordinate and the P-coordinate of the reduced representative are uniquely recovered from H, so the map is injective and its image criterion is exact. This is a calculation about this Q, not a new lemma hidden behind a phrase such as “standard normal form.”

Step 3 cites the same definition for group completion and the three fs conditions. I checked the proposed inverse on every generator, including v=e+a−u, so the ambient group really is Q^gp. The generators e and −e supply the whole integer factor, finite generators of P give finiteness, and the equality (rm)_−=r m_− holds for every r>0. Thus the saturation argument applies in P^gp exactly as required. Step 4 calculates both inverse maps of the cokernel explicitly. It uses no external group-isomorphism theorem; subtracting (0,t,b) verifies the quotient map directly.

Steps 5 and 6 cite no theorem: they construct the two algebra maps explicitly. I checked that the monoid congruence is respected, that additive extension multiplies correctly on monomials, and that balancing over Z[R] gives the tensor map. In the reverse direction the polynomial relation is killed because 1⊗[u+v]=1⊗[g(1,a)]=epsilon alpha(a)⊗[0]. The two composites fix the stated algebra generators, hence all polynomials and finite sums of tensor monomials. These are routine uses of the definitions of monoid ring, polynomial quotient and tensor product, with all formulas provided; no preservation-of-pushouts theorem is imported implicitly.

I tested P={0} (so uv=e and the resulting Q is a group), a=0 with arbitrary P, P=N with a=d including d>1, P a finite abelian group (allowed fs torsion in its units), and arbitrary coefficient rings including the zero ring and alpha(a)=0. None needs sharpness, torsion-freeness, a≠0, a domain assumption or a non-zero-divisor condition. The cokernel is always the independent u-coordinate Z; saturation is inherited from P by the exact integer image criterion.

I checked delivery-errors B–E point by point. There are no new statements requiring independent hypotheses/definition dependencies, no clause-restatement children, no duplicate/tag conflicts, no off-unit proof citations, and no changes to target meaning. Each use of a cited node was checked against its statement, and every citation has a literal excerpt in citations.json. All six proof steps are below 2000 characters (627, 580, 823, 436, 789, 780). Mathlib searches were actually run and logged, with two phrasings and source inspection of the candidates. `Monoid.PushoutI` is the generic noncommutative monoid/group construction; its group normal-word theorem does not prove this commutative fs assertion. `MonoidAlgebra.instIsPushout`/`instIsPushout'` at `Mathlib/RingTheory/TensorProduct/MonoidAlgebra.lean:122,128` change a coefficient-ring pushout with a fixed monoid, rather than calculate this monoid relation. `IsAffineMonoid` requires torsion-freeness and is not the fs notion here; `AddSubmonoid.NSMulSaturated` is a definition, not this nodal result. The explicit proof therefore remains necessary.
