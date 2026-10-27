# Q92 stage-1 delivery

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-graded-bialgebra-coordinate-derivations.json`: item, statement, split by seven direct calculations; no Mathlib match for the complete signed graded assertion.
- `citations.json`: verbatim statement evidence for the tensor-product leaf cited in steps 2 and 3.
- `searches.jsonl`: actual msearch output records, retained unchanged.
- `report.md`: this report.

No new nodes and no new Mathlib leaves. The existing Mathlib leaf `def-weil-pbc-module-tensor-product` is reused. The item's statement is unchanged, including its unrestricted characteristic and absence of perfectness and cocommutativity assumptions. Only the tensor-product definition was added to its statement dependencies.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag, graded bialgebra, coordinate derivations, invariant derivations and cotangent constructions found no declaration proving all clauses for signed graded algebras. `Bialgebra.exists_derivation_counitAlgHom_comp` and `Bialgebra.exists_derivation_of_cotangent`, in `WeilConjectures/RingTheory/HopfAlgebra/Cartier.lean:468,501`, concern ordinary commutative bialgebras and ordinary derivations. The normalization in `WeilConjectures/RingTheory/Bialgebra/Frobenius.lean:461-490` also uses ordinary commutative algebras. Neither covers the Koszul sign, so neither is an attachment to this item.

## WANTED

None needed for this proof. Waterhouse, *Introduction to Affine Group Schemes*, chapter 11, is already in the repository's Wanted table. I did not claim to have read that unavailable book or to use any unquoted result from it. Its ordinary construction was read directly in the project's Cartier source, then the signed calculation was proved explicitly.

## What was wrong or missing

The item was unsplit with no proof. The statement is correct. In particular, contraction of a dual indecomposable functional need not itself send every chosen generator to a scalar: higher-degree generators can have lower-degree-valued derivatives. The missing normalization is essential. The proof now handles it by descending recursion on the finitely many generator degrees, with the coefficient sign checked explicitly instead of applying an ordinary matrix-inverse result to a signed algebra.

Milne I Lemma 12.2, printed p.55 (PDF p.61), supplies the Borel-structure motivation, not a printed assertion or proof of this coordinate-derivation lemma. The proof is honestly marked agent-written. It does not apply Milne's perfect-field structure theorem to the potentially imperfect field in this item.

The inherited blueprint chain ends with `from.node: null`; `tools/blueprint_refs.py ancestor lem-sfb-graded-bialgebra-coordinate-derivations` reports `None`. I preserved that inherited field and its detailed place/via chain rather than inventing an ancestor. I read the latest blueprint direct-images proof (3), unit and chapter. The inherited chain serves its alteration/Picard prerequisites and ultimately the Borel input; none of that route changes. Searches of all imported blueprint nodes for bialgebra, invariant derivation, derivation and cotangent found no duplicate signed statement. The latest snapshot is main-20261024 at ef6f9619fdbffa59e88528fb56483d76c70258c8. The historical brief references `coord/dag-sync.md`, which is absent in this read clone; the current read-only shared-clone instructions were followed.

## Mathlib searches and results

All new searches ran using the required `msearch.py Q92 lem-sfb-graded-bialgebra-coordinate-derivations ...` command, with raw summaries retained in `searches.jsonl` and recorded in the item. All services answered. Both a coordinate-derivation phrasing and the broader infinitesimal-character/contraction phrasing were tried. Loogle `Bialgebra, Derivation` gave no hit. The main grep found only smooth-manifold invariant derivations, and the bialgebra-subdirectory grep found none. LeanSearch gave ordinary polynomial partial derivatives and `Derivation.mk`; LeanFinder gave graded inclusion/projection maps on the first phrasing and ordinary derivations/square-zero lifts on the second. I read the relevant local signatures of `Derivation` (Mathlib/RingTheory/Derivation/Basic.lean:44-52) and `MvPolynomial.pderiv` (Mathlib/Algebra/MvPolynomial/PDeriv.lean:55-65). The former requires a commutative semiring and uses the unsigned rule; the latter operates on polynomial algebras. Neither specializes in one line to an arbitrary signed graded bialgebra. Earlier searches already present in the live item's JSON were retained, without representing them as searches run by Q92.

## Not duplicates

No new node is proposed. Quotient coordinate functionals, tensor contraction, the two counit substitutions, the coefficient commutation sign and finite descending substitution are explicit elementary steps. They introduce neither a replacement structure theorem nor a new node restating the conclusion. The one tensor-product notion used was found in the whole DAG and reused as `def-weil-pbc-module-tensor-product`, rather than recreated. Its source is Stacks Tag 00CX, `algebra-lemma-tensor-product`, read in `literature/stacks-project/algebra.tex:1716`; the tag map at `tags/tags:477` agrees.

## Review by Q92

I read Milne's actual Lemma 12.2 and its preceding coproduct formula on printed p.55, the item and its parent monomial-basis proof, the current blueprint direct-images proof, the unit and chapter records, and the ordinary construction and normalization in the two project Lean files named above. There are no new nodes needing separate source review. The signed construction is not attributed to a theorem Milne did not state.

Step 1 uses only the given homogeneous basis of I/I². Expanding products into homogeneous components proves that I² is graded. Coordinates in that basis therefore vanish off the selected degree. Expanding a and b into scalar and augmentation parts proves the displayed infinitesimal-character identity, with the product of the two augmentation parts killed in I². No duality or differential-freeness theorem is assumed.

Step 2 cites the complete statement of `def-weil-pbc-module-tensor-product`. I opened it: it says exactly that a bilinear map M×N→P extends uniquely to a linear map M⊗N→P, and that simple tensors span. The base is the field k, hence a commutative ring; M=N=P=A are k-modules. The map (u,v)↦φ_i(u)v is bilinear. Contracting the first factor is an ordinary linear map, with no additional Koszul sign inserted into its definition. The degree and unit claims follow from the displayed contraction, the given total grading and Δ(1)=1⊗1.

Step 3 cites that same leaf only for the legitimacy of expansion and bilinearity, not for the graded Leibniz theorem. That theorem is proved in the step: the bialgebra product contributes (-1)^(deg a₂ deg b₁); the counit and φ supports force this sign to be 1 in the first term and (-1)^(d_i deg a) in the second. The left counit identity then evaluates the two remaining contractions. This is a finite expansion with its two possible nonzero terms, not an invocation of an invariant-derivation theorem. The two citations in steps 2 and 3 have verbatim statement evidence in citations.json.

Step 4 uses the right counit identity from the item itself; applying φ_i to it proves εD_i=φ_i. Combined with the degree computation, this gives exact identity blocks for equal generator degrees, and zero for lower column degrees. It does not claim that the higher entries vanish.

Step 5 checks the coefficient multiplication rule directly. A coefficient of degree e-d multiplies an E of degree -e. Moving that coefficient past a yields the exponent e·deg a+(e-d)·deg a, congruent to d·deg a. This is why the normalization preserves the required signed Leibniz identity even when the coefficient has odd degree. Linearity, vanishing on 1 and homogeneity are preserved term by term. There is no unstated theorem about modules of superderivations.

Step 6 sets up a genuine finite decreasing-degree recursion. The largest-degree maps are D_i; all maps in each later sum have strictly larger generator degree, so they have already been constructed. Equal-degree maps do not depend on each other. Step 5 verifies exactly the hypotheses for each coefficient term, with e=d_j, d=d_i and h=a_ij.

Step 7 verifies the full induction claim (all generator values for previously constructed maps). For a higher-degree x_l precisely the j=l term cancels a_il; for a generator of equal or smaller degree the whole correction sum evaluates to zero, leaving the exact identity block of step 4. The largest-degree base and the case s=0 are written out. No generation of A by the x_i, nilpotence, finite-dimensional matrix inversion, Borel structure theorem or antipode is used secretly.

I checked delivery-errors B through E against the files. There is no statement correction or STATEMENT-DISPUTED issue. Every cited statement is sufficient for the specific use recorded above; no proof-only detail of a cited node is used. All other facts are the explicit coordinate, expansion, degree, sign and recursion calculations just described, hence elementary; they are not outsourced into clause nodes. Each step is under 750 characters, so there is no long step concealing an unseparated lemma. No Stacks tag is used without its matching existing node. No SGA source, Lean edits, compiler or build command is involved.

Small cases were checked mathematically. For A=k the only allowed basis is empty and the conclusion is vacuous. Repeated generator degrees give identity blocks, so no division or same-degree recursion occurs. For an exterior algebra on degree-one u,v, first-factor contraction yields D_v(uv)=-u, as the signed rule requires. In characteristic 2 the signs both become 1, including the coefficient computation. To test the necessary higher-degree correction, take A=F_3[t,y]/(t³,y³), degrees 2 and 4, with primitive t,y, and choose x₁=t, x₂=y+t². Then D₁(x₂)=2t, D₂(x₂)=1 and ∂₁=D₁-2tD₂ sends x₂ to zero and x₁ to one. Imperfect fields cause no change because all functionals are k-linear and no roots or scalar extensions are taken. Terms in negative graded components are zero at the contraction stage and remain zero under the homogeneous corrections.

## Unfinished work

No mathematical part remains. The first required server dry run exited 0 and printed `OK (not pushed)` at 5f399b69081 with preflight passed. After this report update, the final dry run is repeated before pushing. The delivery tool records the final commit and receipt; no compiler or local DAG validator was run.
