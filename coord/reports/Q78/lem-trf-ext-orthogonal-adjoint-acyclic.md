# Q78: lem-trf-ext-orthogonal-adjoint-acyclic

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-ext-orthogonal-adjoint-acyclic.json`: statement, split; not a Mathlib leaf. Three proof steps, reusing an existing reviewed Hom-acyclicity lemma. Statement and statement dependencies unchanged.
- `citations.json`: four step/node entries, each quote checked against the current node statement.
- `searches.jsonl`: actual msearch log, five searches for the item; results read before recording them. Earlier search records in the item are retained.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean, unit, chapter, source-repository, launcher, or coordination files written. No compiler, Lake, or local DAG/preflight check run.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id, Ext orthogonality, adjoint/acyclic combinations and related Hom/injective declarations. The hits on exact adjunctions and K-injectives do not give this statement: L is not assumed exact and TJ need not be injective. There is no exact finished project declaration to attach.

## WANTED

None. All source material used is present locally.

## Errors and corrections

The item is true as written; no statement dispute or correction. Its proof was empty. The main potential delivery error would have been creating another Hom-acyclicity lemma: `lem-trf-acyclic-coproduct-ext-orthogonal-hom` already states exactly that input, including small coproducts with repetitions and the signs of the Hom differential. I reused it instead of creating dimension-shifting or spectral-sequence nodes.

The supplied chapter/unit ancestry is retained: this is a generic homological input to the lower-shriek construction in the existing local-term-locality dependency branch, not a replacement of the smooth-curve unit's argument. This item is not the unit's key node, so no realized fields are written. No SGA source is used.

## Unfinished work

None in the authorized one-level split. The downstream reviewed Hom-acyclicity node remains an existing dependency, not a new item created here. Delivery is subject to the required remote dry run and direct push.

## Not duplicates

No new node pairs: no nodes were created. Whole-DAG searches for Ext/coproducts, acyclic Hom, dimension shifting and injective detection found the existing `lem-trf-acyclic-coproduct-ext-orthogonal-hom`, whose complete statement and reviewed proof I read. It is strictly the input with a fixed F and no adjunction or target abelian category. The current item adds the adjunction and the enough-injectives test; its conclusion is therefore not merely that input again. Existing 07AC nodes for derived lower shriek and derived colimits are applications/parents, not replacements for this abstract adjunction statement. Blueprint searches `Ext orthogonal`, `adjoint acyclic`, and `Hom injective` found no blueprint statement to replace the item. `injective acyclic` found only the PBC IA definition/equivalence units, which impose geometric base-change settings absent here. The ancestor command confirmed `lem-trf-local-term-locality`.

## Review by Q78

I read Stacks `sites-cohomology.tex`, Tag 07AC (`lemma-existence-derived-lower-shriek`), especially the proof of condition (2), from the acyclic bounded-above complex through the Hom adjunction, the warning that the right-adjoint image of an injective need not be injective, and the Ext spectral sequence. The existing Hom lemma isolates the last part using Tag 07AA (`example-hom-complex-into-sheaf`); I read its entire statement and eight-step proof, including its first-quadrant reindexing, degree-zero edge, signs and reviewed resolution-independence repair. For the injective test I read `homology.tex`, Tags 0135 and 0138 (`definition-injective`, `definition-enough-injectives`). These definitions provide exactly extension along a monomorphism and embedding each object into an injective. No new nodes need source review.

Step 1 uses only `lem-trf-acyclic-coproduct-ext-orthogonal-hom`. I checked its statement clause by clause: the site is small in the same module universe; R is the stated S; F is the sheaf TJ; every positive Ext from E_i to this F vanishes by hypothesis; P is bounded above and acyclic; and the terms are small coproducts with repetitions. The conclusion gives the whole Hom complex, in every integer degree, with exactly the sign and index in this item. Its statement, not an incidental construction in its proof, supplies everything taken here. No injectivity of TJ is inferred.

Step 2 uses the preadditivity clause of `def-sp-abelian`. The assumed additive T and the adjunction unit give the additive bijection f -> T(f) eta. The written naturality equality for each a:X->Y verifies precomposition compatibility. Applying that equality to each differential and using additivity for the sign proves a cochain-complex isomorphism, rather than merely unrelated degreewise group isomorphisms. Both directions are supplied by the adjunction bijections; the direction printed in the statement is the inverse of alpha. This is an elementary expansion of the given adjunction, not an uncited derived-adjunction theorem.

Step 3 uses `def-sp-abelian` for kernels and cokernels and `def-sp-enough-injectives` for both the monomorphism H -> J and extension across H -> Q. I opened both statements and copied their defining clauses verbatim into citations.json. With Q=coker(d^{r-1}), ker(Q -> C^{r+1}) is the usual cohomology object; this is the elementary quotient description, not a sheafwise sections argument. An extension v:Q->J yields the cocycle vq. Acyclicity of Hom(C,J) makes it a boundary, and cancellation of the epimorphism q gives v=g bar-d, so its restriction to H vanishes. Thus the original monomorphism H->J is zero and H is zero. This explicitly proves the injective-detection assertion from definitions in a short kernel/cokernel argument; a separate node for it would be elementary. Step 2 applies to this J because it was proved for every injective J. Additivity of L, rather than exactness of L, makes its termwise image a complex.

I checked B1-B10: no new unsplit statements, no hidden proof in a new statement, sources use the correct tags/labels, unchanged self-contained objects and universes, no invented Mathlib match, preserved blueprint ancestry, and no false attachment. I checked C1-C8: every non-elementary input is a cited statement (step 1), the two elementary steps give their actual arguments and definition dependencies, quotations are exact, and the only non-Mathlib statement dependency used in the proof belongs to this same unit. There is no off-unit tool-use request. I checked D1-D5: no relabelled clause, no one-node relocation, no definition-only imitation of the spectral-sequence argument, and no circular dependence. I checked E1-E7: hypotheses, objects, signs and all comparison formulas agree; there is no statement correction to conceal. The largest proof step is 1005 characters, so no non-elementary step crosses the 2000-character review threshold.

Small cases: an empty family forces every term to be zero; repeated summands and infinite small sums are explicitly included by the reused lemma. The two-term identity complex remains exact under any additive L and satisfies the claimed Hom adjunction in both nonzero degrees. Every r, including degrees above the upper bound and negative r, is covered by the cokernel proof; the boundary sign is a unit and is absorbed into g. A zero target category gives zero complexes throughout. To check why an illicit exactness assumption would be wrong, take sheaves on a point, S=Z, L=(-) tensor_Z F_2, T the forgetful functor, and the exact complex Z --2--> Z -> F_2. Its image is not acyclic. The item's hypothesis correctly excludes the family containing F_2, because for the injective F_2-vector space J=F_2, Ext_Z^1(F_2,TJ)=F_2. Conversely the free family E=Z has vanishing positive Ext against TJ even though TJ itself is not injective as an abelian group. Thus the argument genuinely uses Ext orthogonality without assuming TJ injective.

The five newly run msearch results were read: the semantic searches give K-injective/K-projective orthogonality, injective dimension, Ext existence and vanishing of derived functors on injectives; Loogle gives no hit; the grep gives three KInjective declarations. I read `Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean`, including its definition, orthogonality equivalence, bounded-below injective criterion and cocycle lemmas. They require K-injectivity or termwise injectivity, whereas the fixed TJ here need not be injective; they do not specialize in one line to this additive-adjoint transfer criterion. The second semantic phrasing confirms no matching leaf. Queries are recorded exactly as run in searches.jsonl and in the item, alongside the retained historical searches.
