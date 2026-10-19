## Files written

- `dag/nodes/sec-smooth-purity/lem-fin-projective-curve-betti-cardinalities.json`: existing statement, split into nine steps; no Mathlib match for the family theorem.
- `citations.json`: all 23 step/node pairs, each with a verbatim statement quote.
- No new nodes and no new Mathlib leaves. All lemmas needed by the proof already exist.

## Attachments

None for this item. The source search found no declaration with its blueprint tag or the complete family statement. `AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_zero` in `WeilConjectures/AlgebraicGeometry/Curve/Estimate.lean:62` covers only connected degree zero; the degree-one and degree-two theorems in that file have `sorry`. Neither those theorems nor declarations in the read-only upstream master prove the family cardinalities and constructibility.

## Wanted sources

None. The item's master blueprint, Stacks source, and the original coherent-rank blueprint lemma are available locally. There is no slopmaster2 blueprint file for this item at the corresponding path; no different statement or proof was found there.

## What was wrong and corrected

The statement is unchanged and no statement dispute was found. The original proof cited `def-sbc-smooth-morphisms` as if its statement implied flatness; its current definition does not state this theorem. Step 5 now cites the existing Mathlib leaf `lem-pc-smooth-flat` and the flat-morphism definition. It also checks coherence of the structure module and Noetherianity of X before applying the coherent-rank lemma.

The original argument used finite clopen decomposition and cohomology assembly without naming their supporting statements. Steps 1-2 now cite the existing permanence and curve-decomposition lemmas. Step 3 explicitly builds coherent cohomology assembly using an injective resolution and its restrictions, rather than creating a new component-sum lemma. Step 8 cites the existing finite-coproduct étale cohomology theorem and constant-sheaf pullback. Step 7 supplies primitive-root existence, so the erroneous reading of a trivialization for an arbitrary root cannot enter this proof. The connected-curve theorem already includes the vanishing above degree two, so the separate cohomological-dimension citation is unnecessary.

The coherent-rank argument is retained; constructibility is not deduced from étale smooth base change or étale direct-image constructibility, either of which could be circular in the surrounding route. The chapter and unit records were read and left untouched. This item is not their key statement. Its nine steps realize the two original proof paragraphs, including the coherent rank route and connected-curve calculation.

## Mathlib and duplicate searches

The exact searches are in `searches.jsonl` and `mathlib_searches`. LeanFinder was run on both the family-cardinality statement and a second phrasing about the connected curve ranks; hits are class numbers and algebraic smoothness/cotangent ranks, not these étale cohomology assertions. Loogle on `AlgebraicGeometry.Smooth, AlgebraicGeometry.IsProper` returned no hits. The Mathlib grep for `betti|etale.*cohomology|cohomology.*etale` in `AlgebraicGeometry` returned none. LeanSearch returned HTTP Internal Server Error and is recorded as unavailable, not as absence.

The whole blueprint searches `Betti cardinalities`, `projective curve family`, and `cohomology cardinalities` found only this item or no match; `same_as` is empty. DAG statement searches found the existing curve/point decomposition, ringed-space restriction of injective resolutions, clopen étale assembly, flatness, coherence, and permanence statements. No node was created, so there are no new/existing tag pairs to distinguish. In particular a new node for a disconnected curve calculation or for coherent disjoint-union cohomology would be unnecessary.

## Unfinished work

None in the one-level split. The cited unsplit or imported lemmas remain existing DAG work; their statements suffice for this proof. No Lean files were written, no compiler or Lake command was run, and this worker does not push.

## Review by NZ

I read the master item and the `sec-smooth-purity` chapter and `sk-prop-sf-cbc` unit. I read Stacks `etale-cohomology.tex` Tag 0A5B (`lemma-constant-smooth-statements`) for the component reduction and Tag 03RQ (`lemma-cohomology-smooth-projective-curve`) for the group ranks; `cohomology.tex` Tags 01DZ and 01E1 for module cohomology and injective restriction; `coherent.tex` Tag 01XZ for coherence; and `morphisms.tex` Tags 01T6 and 01VF for the Noetherian and flatness hypotheses. The genus definition is the one in `curves.tex` Tag 0BY7. I read the complete existing statement of each of the 23 citations (repeated uses included), and copied those statements verbatim into the citation evidence. No new node requires an additional source review.

In step 1 the projective-proper statement applies to the original f, and `lem-pc-proper-base-change` actually has both the proper and smooth clauses for arbitrary base changes. The proper definition supplies separatedness and finite type; the curve definition allows the empty and disconnected case. This avoids applying a connected-curve theorem prematurely or assuming the base is of finite type over a field.

In step 2 `lem-sbc-smooth-curve-points-decomposition` supplies the finite decomposition over the algebraically closed geometric residue field and says its coprojections are both open and closed immersions. The pure-dimension-one assumption rules out its point summands. The closed-immersion-proper statement explicitly includes the assertion that a closed subscheme of a proper scheme is proper. Thus all remaining summands meet the connected proper curve hypotheses; no claim about a finite union is taken from a definition alone.

In step 3 the enough-injectives lemma supplies an actual resolution. The restriction lemma supplies an injective resolution on each open component, not just an arbitrary resolution or a sections bijection. Degreewise sheaf gluing on a disjoint cover is written out, as are the coordinatewise kernels and images. This is why the finite product computes coherent cohomology, and why the resulting identifications are k-linear. The cohomology definition cited is for ringed-space modules, not an unrelated étale-only definition.

In step 4 the last clause of `lem-sc-global-functions` expressly includes proper smooth connected curves; it does not require a separately unproved integrality statement in this application. `def-sc-genus` defines the genus as the coherent H1 dimension, which is precisely the value used here. Finite-dimensional direct sums are counted by concatenating bases. The argument allows distinct genera on different components.

In step 5 the Noetherian lemma requires finite type of f and Noetherian S, both verified. The coherent criterion requires locally Noetherian X and a quasi-coherent finite-type module; on each affine chart the structure module is the free module A of rank one. Smooth-flat is a theorem citation. Its stalkwise interpretation proves base-flatness of this particular module, which is what the rank lemma asks for.

In step 6 the rank lemma states constructibility on geometric fibres with coherent cohomology and accepts a projective morphism over a Noetherian base, with no connectedness assumption. Its coefficients are exactly the base change of O_X. All its hypotheses have been checked in step 5. The coherent h0 and h1 identifications from step 4 give c and the sum of genera. I used only this lemma's statement, not a perfect complex concealed inside its proof.

In step 7 the chosen prime is a unit in every geometric residue field, and the primitive-root lemma states existence under this exact hypothesis. `thm-sc-proper-cohomology` gives all four degree cases under a primitive-root trivialization for smooth proper connected one-dimensional curves. Its genus notion agrees with step 4. No arbitrary root is assumed primitive, and no trivializations must be chosen coherently in the family because only cardinalities are asserted.

In step 8 the constant-pullback lemma gives the same constant abelian coefficients on each component, and the clopen assembly statement gives Hq as the finite product in every degree. These are the exact assertions taken from the two nodes. The remaining cardinal calculation counts independent coordinates; zero groups and empty products each have one element. Step 9 uses Boolean closure from the constructible-subset statement and explicitly intersects finite partitions; exponentiating a constant on each piece preserves that partition.

Small cases checked: the empty fibre has c=g=0 and all cohomology groups zero, of cardinality one; a single projective line has c=1 and g=0, giving cardinalities ell, 1, ell; two projective lines give ell^2, 1, ell^2; a projective line disjoint from a genus-one curve gives ell^2 in degrees 0, 1, 2. Characteristic zero and positive characteristic different from ell satisfy the same invertibility argument. Characteristic ell is excluded by the explicit hypothesis. These checks expose why zero-dimensional point components cannot be admitted. No hidden equigenus, connectedness, surjectivity of f, or finite-type base hypothesis was added.

Generic statements from other units are declared in `split_report.tool_uses`, with their purpose. They fill local gaps of the original two paragraphs and do not substitute another route for the unit. I checked B-E: there are no new-node schema, duplicate, source-tag, Mathlib-leaf, or clause-restatement issues; the cited statements give exactly the assertions used; the few-line finite-product and partition arguments are written out; and the original statement and its coefficient category are preserved.

## Second reading by NZ

- Item statement: checked against the blueprint node and the source family statement; the Noetherian base, smooth projective morphism, pure one-dimensional geometric fibres, invertible prime, all three degree cases, and constructibility clause agree. Empty fibres and disconnected fibres remain allowed.
- Step 1: checked against Stacks Tags 01WC, 01W4, and 01VB and the cited proper-morphism and curve-definition nodes; properness and smoothness base change to the geometric fibre, and the curve hypotheses are all present.
- Step 2: checked against Tag 0A5B's component reduction and the cited decomposition and closed-immersion statements; point summands are excluded by purity, while the remaining clopen connected components are proper. The empty index case is covered.
- Step 3: checked against Tags 01DI and 01E1 and the ringed-space cohomology definition; the chosen injective resolution restricts to each component, sections and differentials decompose coordinatewise, and finite products give the stated direct-sum cohomology. The empty product is handled.
- Step 4: checked against Tag 0BY7 and the global-functions node; each proper smooth connected component contributes one degree-zero dimension and its genus in degree one, with dimensions summed over finitely many components.
- Step 5: checked against Tags 01T6, 01XZ, and 01VF plus the flatness definition; finite type over a Noetherian base makes X locally Noetherian, the structure sheaf is quasi-coherent of finite type and hence coherent, and smoothness supplies flatness.
- Step 6: checked against the complete statement of `lem-fin-projective-flat-coherent-ranks`; its projective, Noetherian-base, coherent, and base-flat hypotheses are established before use, and it yields constructibility of exactly the h0 and h1 functions used.
- Step 7: checked against Tag 03RQ and the primitive-root node; invertibility of the prime gives the required primitive root, every component satisfies smooth proper connected one-dimensional hypotheses, and the theorem supplies the three groups and vanishing above degree two.
- Step 8: checked against Tag 0A5B and the constant-pullback and finite-coproduct assembly statements; restriction preserves the constant coefficient sheaf, component groups assemble by finite product, and the cardinal arithmetic also covers zero groups and empty products.
- Step 9: checked against Tag 005H and the constructible-subset definition; finite common refinement is valid and exponentiation of the resulting locally constant integer functions gives the asserted constructible cardinality functions.
- New nodes: none. Therefore B1--B7, duplicate-node searches, and new-node Mathlib-search requirements are vacuous; all cited dependencies are existing nodes or declared generic tools.

Changes made: expanded step 3 to construct the injective resolution by successive cokernels, because the enough-injectives node states embeddings rather than an already chosen resolution; wrote the quotient map from component cycles to component cohomology and identified its kernel to justify the product calculation. Ran an independent LeanFinder query in different vocabulary; its eight hits concern other cohomology theories or class numbers, and no match was found. The new query is recorded in searches.jsonl and mathlib_searches. The statement, dependencies, and verbatim citation quotes are unchanged. No source error or statement dispute was found. I also checked the empty scheme, a point, one projective line, two projective lines, and a mixed genus-zero/genus-one disjoint union; the empty and one-dimensional cases satisfy the formula, while a point is correctly excluded by purity (it would have H2 = 0 rather than cardinality ell).
