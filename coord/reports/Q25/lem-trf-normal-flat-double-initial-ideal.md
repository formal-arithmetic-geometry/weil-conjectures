# Stage-1 report: lem-trf-normal-flat-double-initial-ideal

Group Q25; 2026-10-23. Direct delivery; no second worker and no agents started. Only the sandbox was written. No Lean file, compiler, Lake, repository git command, or launcher modification was used.

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-normal-flat-double-initial-ideal.json`: the item, statement unchanged, split into six proof steps. Mathlib searches do not give the normal-flat tangent-kernel comparison.
- `dag/nodes/sec-trace-formula/lem-trf-normal-flat-hilbert-convolution.json`: one new statement-only numerical theorem, status `unsplit`; no Mathlib match after two semantic phrasings, LeanSearch, Loogle, and source grep.
- `citations.json`: one entry for every step/node citation, each containing the cited statement verbatim.
- `searches.jsonl`: the actual msearch.py log. The item's earlier searches and metadata were retained; the new searches were recorded exactly as executed.
- `report.md`: this report. `build_split.py` is sandbox-only scratch code producing the two JSON files and citation records.

## Attachments

None. Searches in `lean/WeilConjectures/` for the exact blueprint tag, normal flatness, tangent-cone and double-initial terminology found no declaration proving the item. The existing closed-immersion conormal flat-base-change theorem is about a different base-change statement, not this normal-flatness comparison. Mathlib declarations are not treated as project attachments.

## WANTED

WANTED: archival copy of Heisuke Hironaka, *Certain numerical characters of singularities*, J. Math. Kyoto Univ. 10 (1970), 151–187, section 2 p.153 and the paragraph following Example (4.2), p.157, for the item and `lem-trf-normal-flat-hilbert-convolution`. Read online at https://scispace.com/pdf/certain-numerical-characters-of-singularities-18d51ii5bz.pdf; nothing was downloaded into the repository or sandbox.

WANTED: archival original of Hironaka, *Resolution of singularities of an algebraic variety over a field of characteristic zero* (1964), Chapter II, Theorem 2, cited by the 1970 paper for normal flatness and the tangent-cone product. The general normal-flat algebra assertion here does not impose characteristic zero. The 1970 paper states it for Noetherian schemes in section 2.

For a modern comparison I also read Cossart–Jannsen–Saito, March 12 2009 preprint, Theorem 2.2(2), printed p.28, online at https://epub.uni-regensburg.de/13766/1/MP32.pdf. Its introduction to section 2 has excellence and a restriction on components of the center. I did not silently import those hypotheses into the present item and did not use that restricted formulation as its proof.

## Audit findings and changes

The imported statement is retained verbatim: it is true for the specified maps, including nonreduced quotients and mixed characteristic. There is no statement dispute. The item had no proof, no repair note and no completed sandbox split. It was still unsplit when the sandbox was written.

The inherited `source.document` names ILO, but its place already identifies Hironaka as the precise ancillary source. ILO VIII 2.3.13 is only the ancestor's resolution motivation; it is not claimed to state the kernel identity or the numerical formula. The proof is explicitly agent-written, compared with the online source, and the missing archival sources are listed above. No SGA source was used.

The geometric assertion in Hironaka says that, under normal flatness, the tangent cone is the inverse image of the normal-cone fiber under the normal-space projection, and any splitting gives the product. In parameter coordinates that means precisely the kernel extension in the item. I avoided using that whole assertion as a new node: step 4 constructs one kernel inclusion by explicit coefficient lifts, and steps 5–6 derive the reverse inclusion from numerical dimensions.

There is one new numerical input, not a new name for the item's kernel equality. It has no ambient regular ring, parameters, polynomial maps, or ideal-equality conclusion. Its statement gives the cumulative Hilbert function of a general Noetherian local ring from the normal-cone fiber when the quotient is regular. In the embedded case its formula is the numerical content of the normal-flat tangent-cone product on Hironaka p.157. For the arbitrary local ring, the standard passage is to completion and a regular local Cohen presentation, preserving ideal-power quotients and the residue field. This passage and the normal-flat numerical theorem remain work for that unsplit node; they are not asserted to be elementary steps of the present item. A future split may also prove the numerical theorem by the mixed ideal filtrations directly. The new node contains only its statement, not this discussion or a proof sketch.

The latest blueprint ancestor `lem-trf-local-term-locality` was read in `literature/blueprint/latest/`, as were the chapter and unit records. This item is on the already recorded historical resolution branch; no chapter or unit route was changed. The item is not a unit's key statement. Its existing `blueprint.from` and every imported field were preserved, and the new node's `via` list begins with this item, followed by its existing ancestry. Whole-blueprint searches for normal flatness, graded regularity, Hilbert normal, flat graded length and convolution gave no equivalent node; the Fourier convolution node is unrelated.

## Not duplicates

lem-trf-normal-flat-hilbert-convolution vs lem-trf-normal-flat-double-initial-ideal: the new theorem is only a numerical length formula for an arbitrary local ring with regular quotient; the item concerns the kernels of two specified polynomial maps in a regular ambient presentation. Steps 3–4 still prove the essential kernel inclusion, and step 6 proves the reverse inclusion using the dimensions.

lem-trf-normal-flat-hilbert-convolution vs lem-trf-bennett-normal-flat-numerical-criterion: Bennett's existing node assumes a reduced ring essentially of finite type over a field, compares the maximal-ideal length function to the length function of the generic localization, and asserts an equivalence with normal flatness. The new formula uses the closed normal-cone fiber, requires no reducedness or coefficient field, and gives an explicit convolution. The Bennett statement cannot be applied to the nonreduced or mixed-characteristic cases allowed here.

lem-trf-normal-flat-hilbert-convolution vs lem-trf-maximal-adic-graded-length-bridge: the bridge gives length as the sum of the ring's own maximal-ideal graded dimensions. It says nothing about an ideal with regular quotient or the closed normal-cone fiber. It is reused in step 5, rather than recreated.

lem-trf-normal-flat-hilbert-convolution vs lem-trf-hilbert-samuel-near-normal-cone: that node supplies normal flatness and a directrix from a near blowup point for a reduced scheme over Q. It does not state this local numerical formula and its hypotheses do not cover the present item.

lem-trf-normal-flat-hilbert-convolution vs lem-trf-flat-graded-fibre-regular-lift: the existing node gives finite freeness of the graded pieces and lifts a fiber nonzerodivisor to a nonzerodivisor of the ring. It gives no comparison with maximal-ideal powers or the Hilbert function. Finite freeness alone is not silently treated as the convolution formula.

No Stacks tag is claimed for the new normal-flat Hilbert theorem. For the two polynomial presentations I reused `lem-pur-regular-sequence-graded-polynomial` (00LN/061P); I did not add a competing 00NO node or cite the domain-only node for its stronger polynomial-associated-graded content.

## Review by Q25

I checked the six steps against their cited statements and the source with the original parameter maps in view. The main correction to the imported empty split was to distinguish an abstract cone product from the equality for the specified parameters and to expose the numerical normal-flatness input rather than hide it under the word “comparison.”

1. I read Stacks algebra.tex `lemma-regular-ring-CM` (00NQ) and `lemma-regular-quasi-regular` (00LN), with the quasi-regular definition 061P. The first cited node explicitly says that any chosen generating parameter list is a regular sequence and its initial quotients are regular local of the right dimension. The regular-sequence definition makes the x-prefix regular. The second cited theorem explicitly identifies the polynomial map with the associated graded and gives its representative formula. Thus it applies to both the full maximal ideal and P, with exactly the chosen X,Y images. It also gives that A is regular of dimension s; no arbitrary regularity claim is used.
2. I opened the three definition nodes cited here. The polynomial node includes its evaluation universal property, the tensor node includes pure-tensor generation and balancing, and the associated-graded node includes the representative multiplication and homogeneous components. I wrote out the products-of-generators proof of surjectivity, so no uncited generation theorem or right-exactness assertion is hidden in this elementary step. The grading also proves that C is homogeneous.
3. I read the exact statement of `lem-weil-pbc-flat-quotient-tensor-injective` and its source 00HL: it applies when the *cokernel* is flat. Here that cokernel is G_d. Flatness of G_d is justified by its split inclusion in G and the definition of tensor-injection flatness; one must not confuse flatness of the whole normal-cone module with an unstated flatness hypothesis on the ambient quotient. The map A[X]_d to G_d is surjective by step 2's monomial argument before tensoring. Its tensor map is exactly beta_d, not just an unspecified isomorphism. This is why the cited flat-quotient theorem says exactly what the step takes from it.
4. I checked the kernel lift on representatives: the image of t is in I^(d+1), so a lift v exists in P^(d+1), and t-v lies in the actual ideal a. Since P^(d+1) is contained in M^(d+1), the degree-d M-class is the reduction of the P-initial polynomial to k, without extra Y terms. This proves the whole homogeneous relation space lies in the tangent kernel. Taking finite linear combinations, then homogeneous components, gives C times k[X,Y]. The factorization through S[Y] is by coefficients of Y-monomials. This is a few-line representative argument using already established maps, not an independent lemma moved to a node.
5. I read the statement of the new numerical node after writing it, checking each hypothesis and the indexing n+1. R is a nonzero Noetherian local quotient (a is contained in the proper ideal P; ideals of a quotient correspond to ideals above a, so finite generators descend). I is contained in its maximal ideal, A is regular of dimension s by step 1, and the stated flatness is exactly the item's assumption. I also opened the existing maximal-adic graded-length bridge; its formula H_R(n)=sum_{i<n} dim S_i must be used at n+1, as the proof does. The elementary monomial count supplies the same cumulative dimension for S[Y]. The s=0 convention is expressly covered.
6. I checked that step 4 supplies a graded *surjection* and step 5 supplies equality of all finite cumulative dimensions. A basis-lifting argument makes each truncated map injective, hence each homogeneous map injective. Finite sums of homogeneous components then make phi injective as a ring map. This gives equality of the *specified* kernel, not merely equality of Hilbert polynomials or an abstract graded-ring isomorphism.

Every `uses` entry has a verbatim statement in `citations.json`. The regular-parameter and regular-sequence polynomial theorems are declared as generic off-unit tools in the split report; no smooth-purity proof route is imported. All non-elementary steps are shorter than 2000 characters; in fact every step is shorter than 1100 characters. The new node is statement-only, and no node depends back on the item, so the construction adds no cycle.

I checked the following small cases explicitly.

- a=0: C=0, the two parameter presentations give the polynomial associated graded, and the conclusion has zero kernel.
- a=P: R=A and I=0, beta kills every X_i and gamma has kernel (X); the formula still holds.
- s=0: P=M, A=k, and S=gr_m R; the Hilbert convolution reduces to the ordinary cumulative graded-dimension identity, including nilpotent rings.
- R=k[[x,y]]/(x^2), I=(x): G=k[[y]][X]/(X^2) is flat over k[[y]], and both sides give the tangent ideal (X^2). This tests nonreduced R.
- T=Z_p[[x]], P=(x), a=(x^2): A=Z_p, G=A[X]/(X^2) is flat, and the tangent kernel is (X^2) in F_p[X,Y], where Y is the degree-one class of p. No coefficient field or equicharacteristic hypothesis was used.
- Without flatness, R=k[[x,y]]/(xy), I=(x), has G_j=k in positive degrees as a k[[y]]-module. Its fiber S=k[X] has C=0, whereas the tangent kernel is (XY). This detects exactly the hypothesis needed in step 3 and the new numerical formula.
- For the new node, I=0 gives length_A(A/n^(n+1))=binomial(n+s,s), I=m gives s=0 and the standard graded-length sum, and R=k[epsilon]/(epsilon^2), I=(epsilon), gives lengths 1,2,2,... . All agree with its indexing and finite-dimensionality assertions.

The searches actually run are retained in searches.jsonl. I read the hit declarations and source: `Algebra.Smooth.flat` assumes smoothness and only proves flatness; the cotangent hits describe I/I^2; homogeneous-ideal extensionality has no normal-flatness input. For the new theorem `Polynomial.hilbertPoly` is a numerical polynomial construction, not a local ring length comparison, and `rank_pow_quot_aux` in Mathlib/NumberTheory/RamificationInertia/Basic.lean:439 assumes a Dedekind domain and computes a ramification rank recurrence. It does not specialize to this theorem. The remaining search results concern dimension drops for regular sequences, adic separatedness, and generic flatness criteria. None is a match. Unavailable services were not counted as no-match evidence; these logged services answered successfully.

## What remains

The item has a complete one-level assembly proof. The one new numerical input remains unsplit and is the only new task created by this delivery. Server preflight and delivery results are supplied by the required delivery command.
