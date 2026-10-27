# Q96: lem-trf-separable-prime-coefficient-normalization

## 1. Files written

- `dag/nodes/sec-trace-formula/lem-trf-separable-prime-coefficient-normalization.json`: statement, split into seven steps; no Mathlib match for the full assertion. Its statement and statement dependencies are unchanged.
- `dag/nodes/sec-trace-formula/lem-trf-defectless-base-best-approximation.json`: one new statement-only unsplit node; no Mathlib match after both semantic services, valid Loogle patterns, source grep and a second semantic formulation. No new Mathlib leaf.
- `citations.json`: fourteen step/node pairs, with verbatim supporting portions of the statements.
- `searches.jsonl`: the actual search-command log. The sandbox also retains `write_split.py`, which generated these JSON files; it is not a project delivery file.

## 2. Attachments

None. I searched the project Lean source for the exact blueprint id and for immediate extensions, valued-field orthogonal bases, defectless extensions, best approximation, and the coefficient-normalization notion. No project declaration states this item or the new node. Existing Mathlib leaves are cited as DAG nodes rather than recreated.

## 3. Literature wanted

WANTED: Michael Temkin, *Stable modification of relative curves*, arXiv:0707.3953v3, archival PDF at `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`, §2.1 printed p. 9 and Proposition 6.1.4 printed pp. 39–40, for this item and lem-trf-defectless-base-best-approximation. The PDF is absent from the read clone. I read those places at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf, including the paragraph before Lemma 2.1.5 identifying defectless and Cartesian extensions, and the full separable immediate argument. No repository literature files were written. The item proof is marked agent-written because it expands the source's analytic-disc argument into elementary polynomial algebra and the archival document is unavailable locally.

## 4. Findings and changes

The imported item had no proof. Its statement agrees with the translation inequalities immediately before the substitution a=-a_1 in Temkin's proof. There is no statement dispute. The positive and unattained distance assumptions already appear explicitly, so no extra hypothesis was needed.

The source's exclusion of low-degree closed points from the nonsplit disc needs an actual best-approximation result. The existing finite ramification calculus states that the defect is a power of the residue characteristic; it does not state best approximation. I supplied a separate node for the latter instead of citing the former for something absent from its statement. Applying both gives the needed exclusion. The source's split-disc unit criterion is proved directly for polynomials by factoring and expanding a finite product. No analytic-space definition or general affinoid unit theorem is silently invoked.

The source attributes the irreducible-polynomial coefficient estimate to BGR 3.2.4/3. Here it follows immediately from the already recorded spectral-value supremum formula and uniqueness of the extended absolute value; those nodes are cited. I inspected Mathlib's SpectralNorm.lean lines 101–115, 690–692 and 770–773. The number-field coefficient-bound search hit at Embeddings.lean lines 85–100 has a number-field ground setting and an archimedean combinatorial bound, so it does not state this item. The derivative/Taylor hits merely supply elementary polynomial identities, not valuation normalization. Searches preserve the rejected `Valuation.IsUnramified` query as invalid rather than claiming it was a meaningful empty result; valid `Valuation, Module.finrank` and the quoted-name query supplement it.

The latest blueprint is `literature/blueprint/latest` (main-20261024). I read the chapter/unit records and the current local-term node and proof. This item is a supporting Temkin input along the existing ancestry to lem-trf-local-term-locality; it is not the unit's key statement. The chapter/unit route is unchanged and no realization record is owned by this delivery. The new node's ancestry prepends this item to the inherited via list. Whole-blueprint searches for immediate, orthogonal, orthogonal basis, valuation basis, defect, defectless, best approximation and polynomial produced no equivalent node. The generic field-degree multiplication tool is declared in split_report.tool_uses.

## 5. Unfinished work

Nothing in the item's assembly proof is omitted. The new best-approximation node deliberately remains unsplit, as required for a one-level split. No Lean was written, compiled or built.

## Supporting argument retained for the new node

For the new node, the following proof specifies the intended source consequence without putting a proof in its statement-only JSON. Choose representatives y_i for the e cosets of Gamma_E/Gamma_K, including y_1=1. Choose lifts z_j in E^circ of a residue-field basis of tilde E over tilde K, including z_1=1. Each z_j has absolute value one. For a fixed i and coefficients a_ij in K, divide a nonzero family by one coefficient of maximal absolute value. The resulting residue combination of the z_j is nonzero by residue-basis independence. Thus the sum over j has norm max_j |a_ij|. After multiplication by y_i, nonzero sums for distinct i have norms in distinct Gamma_K cosets, so their largest norm is unique and cannot cancel. Consequently the ef elements y_i z_j satisfy the exact maximum formula for all linear combinations. They are independent and hence form a basis because [E:K]=ef. Expand x in this basis and take c_0 to be its coefficient of y_1 z_1=1. Subtracting any other c changes only that coefficient. The maximum formula shows |x-c_0| is no greater than |x-c| for every c. This also covers n=1 and x in K. No separability or discrete-value-group hypothesis enters this argument.

## Not duplicates

lem-trf-defectless-base-best-approximation vs lem-sfb-finite-ultrametric-best-approximation: the existing statement requires a finite extension of Q_ell and proves approximation in an arbitrary finite-dimensional subspace by properness; the new statement permits an arbitrary complete nonarchimedean base and assumes the finite field extension has degree ef. It cannot be specialized from the Q_ell result.

lem-trf-defectless-base-best-approximation vs lem-trf-finite-ultrametric-almost-orthogonal-basis: the existing statement gives only an r-orthogonal basis for each r<1, which does not imply attainment of any distance infimum. The new statement uses defect zero to give exact attainment by the base field.

lem-trf-defectless-base-best-approximation vs lem-trf-valued-finite-ramification-calculus: that statement gives completeness and the numerical defect/ramification laws, but no orthogonal basis or distance-minimizing element. Both inputs are needed in Step 2.

lem-trf-defectless-base-best-approximation vs lem-trf-tate-ideal-best-approximation: the existing node concerns ideals in a Tate algebra with Gauss norm; the new node concerns the ground-field subspace of a finite valued field extension with its multiplicative absolute value.

lem-trf-defectless-base-best-approximation vs lem-trf-separable-prime-coefficient-normalization: the new node has no chosen prime-degree immediate generator, derivative or coefficient-normalization conclusion. It is used in auxiliary extensions K(z)/K of degrees strictly less than p, not in the original immediate degree-p extension. It is neither a clause nor a restatement of the item.

## Review by Q96

I checked the item against Temkin Proposition 6.1.4, pp. 39–40, particularly the simultaneous higher-derivative shrinking, the fixed coefficient norms on all subsequent translations, and the final additional shrinking. For the new node I read the Cartesian/defectless paragraph of §2.1, p. 9, and supplied the residue/value-group basis argument above to justify best approximation with a basis containing 1. I checked its hypotheses on the identity extension, on x in K, on non-discrete value groups, on imperfect residue fields and on inseparable finite extensions. The proof uses no local compactness and would not justify dropping the equality n=ef; that equality is explicitly present.

Step 1 uses exactly the degree-product conclusion of lem-weil-pbc-field-degree-multiplicativity, the minimal-polynomial kernel/irreducibility definition, existence of an algebraic closure in def-weil-algebraic-closure, and the extending multiplicative spectral norm and its uniqueness. I opened all five statements. The ground field is complete and nontrivially nonarchimedean as they require. Algebraicity over K follows by a finite-dimensional coefficient argument, and the quotient-by-minimal-polynomial degree computation is written out; injective multiplication on a finite-dimensional domain supplies the inverse needed to identify the generated algebra and field.

Step 2 uses the actual completeness and p-power-defect clauses of lem-trf-valued-finite-ramification-calculus and the exact best-approximation assertion in the new node. I checked n<p before setting the defect equal to one, and I checked that it is the extension K(z)/K, not L/K, that receives this application. Equality of the two distance functions follows from a strict ultrametric inequality and contradicts attainment even on the boundary |alpha-z|=r. The minimal-polynomial definition supplies divisibility by a polynomial vanishing at z. The supporting quoted clauses are copied verbatim, not inferred from proofs of the cited nodes.

Step 3 uses the formal derivative and coprimality definition; each nonzero higher derivative has degree less than p, the factorials are units, and separability makes the first derivative nonzero. The finite set of roots admits one simultaneous radius greater than r. Step 4 uses the already obtained root distances and algebraic-closure definition; its finite-product expansion proves the strict coefficient and evaluation inequalities explicitly. A zero derivative is handled separately. This is an elementary polynomial calculation, not an unproved invocation of an analytic invertibility criterion.

Step 5 uses only the two opened definitions of minimal polynomial and derivative, previous steps, and the binomial expansion to identify translated coefficients. I checked the sign in f_c(T)=f_0(T+c), the inclusion |c-c_*|<=R_*, and the fact |i|=1 for 1<=i<p. These are what turn derivative dominance into the intermediate-coefficient inequalities.

Step 6 uses the entire supremum formula in lem-trf-spectral-norm-algebraic-extension and uniqueness in lem-sfb-algebraic-absolute-value-unique; its degree-one supremum term is exactly |h_1(c)|^(1/(p-1)). No number-field estimate or unproved equality of conjugate norms is substituted. Only after coefficient norms are fixed do I pass the radii to their infimum. The strict inequality R_*>r is retained to derive A_i<r^(p-i). Step 7 chooses a common real neighborhood for finitely many strict inequalities and then a K-approximation. I checked p=2 (no intermediate indices), characteristic p (|p|=0), zero intermediate coefficients and the allowed equality A_1=r^(p-1).

I checked B–E of delivery-errors against these files: the new statement is self-contained with definitions and has no proof/dependencies; its search records are from actual commands, including the invalid identifier diagnostic; relevant existing nodes are distinguished above; there is no clause moved out of the item. Every non-elementary input is a cited statement with its hypotheses verified, and citations.json provides a verbatim supporting passage for each step/node pair. All proof steps are under 2000 characters. I made no change to the item statement or its hypotheses and used no prohibited SGA route. Validation is by the required remote dry run, not by local checker or compiler execution.
