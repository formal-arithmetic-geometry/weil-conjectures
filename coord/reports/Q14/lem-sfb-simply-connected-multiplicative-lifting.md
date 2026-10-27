# Stage-1 report: lem-sfb-simply-connected-multiplicative-lifting

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-simply-connected-multiplicative-lifting.json`: statement, split; seven proof steps; no exact Mathlib match. The statement and all statement dependencies are unchanged.
- `citations.json`: one entry for each step/node citation, quoting the literal cited statement, including its hypotheses.
- `report.md`: this report.

There are **0 new nodes and 0 Mathlib leaves**. Candidate reduced-neutral-component and finite-target lemmas were not created: the existing DAG statements give these arguments in a few lines. The recorded exploratory searches for the former remain in `searches.jsonl` and `research/`; they do not support a new-node claim.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the item id/blueprint tag, multiplicative-isogeny terminology, simply connected groups and universal covering. No project declaration states this item. The GroupScheme/Basic.lean results concern translations, identity components and closed images, not this full lifting property. No Lean files were written and no compiler or Lake tool was run.

## WANTED

None. All mathematical sources used are present locally.

## Corrections and source audit

The item was an unsplit supporting lemma, with no previous sandbox node or report and no repair note. Its statement is correct as written. Milne, *Algebraic Groups* (2017), Definition 18.5, Proposition 18.6(a), Definition 18.7 and Proposition 18.8, printed pp.388–389, give precisely the route. Algebraic closedness supplies the perfect-field case, and all kernels are scheme-theoretic. Proposition 18.8's terse assertion that a smooth connected group has no finite quotient must not be interpreted as only a fact about rational points: step 7 gives schematic equality using reduced-source factorization. The pullback is not assumed smooth.

I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` unit files and the direct-images proof, whose step (3) is the inherited ancestor location. This item's inherited chain runs through the alteration/moduli/rank-one SL2 prerequisites of that step. `tools/blueprint_refs.py ancestor` prints `None`; the original node already has `blueprint.from.node = null`. I preserved this value and the existing precise place/via chain rather than invent a blueprint ancestor. Whole-blueprint searches for multiplicative isogeny (0 hits), finite-kernel groups, and reduced identity groups found no statement of this item. The matching `sk-p-geometry` has a characteristic-zero matrix-group context and is not substituted for the arbitrary-characteristic group-scheme inputs here.

The seven steps replace the absent proof, not the statement or the unit route. Generic off-unit tools are declared in `split_report.tool_uses`: affine fibre products, faithful-flat base change, surjectivity on spectra, smooth geometric reducedness, zero loci and radicals, finite-algebra spectra, and reduced-source factorization. These are foundation lemmas, not replacement routes for the unit. The unit is not this item's key statement, so no unit realization file was changed.

## Not duplicates

No new nodes were created, so there are no new/existing-node pairs. In particular, I reused `lem-sfb-locally-algebraic-group-identity-component` (including its reduced smooth component clause), `lem-sfb-group-neutral-component-translates`, `lem-sfb-algebraic-group-homomorphism-factorization`, `lem-sfb-reduced-target-dominant-group-flatness`, and `lem-sfb-split-torus-subgroups-diagonalizable`. The special solvable inverse-image lemma `lem-sfb-central-isogeny-solvable-normal-lift` does not apply to an arbitrary H, and the abelian closed-subgroup reduced-component node assumes an abelian variety; neither was used outside its hypotheses.

## Review by Q14

I read Milne 18.6(a) and 18.8 in full, as well as 1.34–1.39 (components and reduction), 1.68–1.70 (closed images and faithful flatness), and 12.8–12.9 (diagonalizable subgroups). I read the statement of every cited DAG node. The Stacks source checks included 01I4/01JQ (affine fibre products), 00HI/00HQ (faithful-flat base change and surjectivity), 047R (reduced subgroups over perfect fields), 0356 (factorization from reduced schemes), and the finite-spectrum argument in 06RS using 05DR/00GT. All sources are permitted by the no-SGA route lock.

1. The affine-fibre-product node explicitly gives both coordinate projections. The faithful-flat-base-change node applies to F[G]→F[E] along F[G]→F[H], with no condition on q. The group-scheme definition gives the kernel fibre product; componentwise operations and the identification e↦(1,e) are written out. Finiteness of algebra generators proves finite type directly. This establishes the hypotheses for all later group-geometry nodes without assuming the pullback is reduced.
2. The finite-type component/translates node explicitly applies to nonreduced group schemes over an algebraically closed field. The locally-algebraic identity-component node explicitly states that the reduction of the neutral component is smooth, connected and of finite type. It gives the same underlying space, not a claim that the whole pullback is smooth. The closed-immersion affine-quotient criterion makes R affine. These are the actual statements cited, not arguments borrowed from their proofs.
3. The homomorphism-factorization node supplies a closed image and a surjective first map for separated finite-type group schemes. R and H are affine; their diagonals are closed by the displayed surjective multiplication ring map. The spectrum-surjectivity node takes the coordinate faithful flatness already obtained. The identity-component node applies to connected H and supplies geometric irreducibility. I checked the finite-closed-cover argument: images of all translates cover H, irreducibility makes one translate the whole space, and translating back shows the restricted image is H. This is why the reduction of the neutral component still surjects, including inseparable kernels.
4. The smooth-geometrically-reduced node applies to H→Spec F. Its single fibre is H itself. The zero-locus/radical node supplies the exact intersection-of-primes equality used to make r* injective; I added this citation during self-review rather than hide a commutative-algebra fact. The reduced-target group-flatness node requires a finitely generated Hopf injection with reduced domain F[H], not a reduced source F[R]. Every one of these hypotheses is checked. Its conclusion is coordinate faithful flatness, exactly the convention used in this item.
5. The kernel L is the pullback of the closed subgroup R along K→P, so its coordinate algebra is a quotient of the finite-dimensional algebra F[K]. Centrality is checked after every F-algebra extension. The diagonalizable-subgroup node is stated for subgroups of a split torus, so I did not cite it directly for a subgroup of arbitrary D(M): the step constructs the torus immersion using generators of M and an explicit surjective Laurent-polynomial Hopf map. The cited node then gives a finite character group for L. This checks finiteness, centrality and diagonalizability independently, without treating a finite nonreduced kernel as an abstract group of points.
6. The definition of multiplicative simple connectedness in the unchanged item now applies to r with smooth connected affine finite-type source. Taking its inverse and the second projection gives the displayed lift. This is the only elementary step: it uses the established isomorphism and the pullback identity, not a new lifting theorem.
7. The finite-spectrum node has base a local ring with only one prime; the field F satisfies this. It gives finite discreteness for Spec F[K] even when K is nonreduced. Connectedness makes the image of δ a singleton, and evaluation at the identity identifies that singleton. The closed unit immersion is justified by the counit's split surjection. The reduced-source factorization node applies to H (reduced by step 4), not to K, and gives equality as schemes. The final calculation over every F-algebra establishes equality of u and v. No unjustified comparison or pointwise-to-schematic leap remains.

Edge cases: H=1 forces G=1 and E=1 under the smooth-connected finite-kernel hypotheses, so the unique lift exists. For p=id the lift is q. For q=id the simple-connectedness hypothesis forces p to be an isomorphism, consistent with the construction. In characteristic p a μ_p-kernel is explicitly allowed; the pullback can have nilpotents and the argument removes them only in R, while uniqueness uses reduced H. A disconnected pullback is allowed and is exactly why the translates argument is necessary. A torus such as G_m is not assumed simply connected (power isogenies supply the obstruction), so no false lifting claim for tori is introduced.

I checked delivery-errors B–E point by point: no new statement-only-node obligations arise, no duplicate or item-clause node is introduced, every non-elementary step cites the full statements it needs, the proof follows the source, and no unused proof dependency, new hypothesis, circular lifting argument, or SGA reference was added. Each step is under 2000 characters, including after the extra radical citation. The citation JSON covers every uses entry verbatim. The preliminary server `review_split` check passed; the required final delivery dry run follows this report.

## Unfinished work

None in this stage-1 split. The cited unsplit nodes remain separate DAG items under the one-level splitting rule. No claim is made that the associated Lean proofs have been completed.
