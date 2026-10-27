# Stage-1 report: lem-sfb-mu-n-fixed-subgroup-smooth

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-mu-n-fixed-subgroup-smooth.json`: split item; unchanged statement; no Mathlib match.
- `citations.json`: verbatim statement excerpts (the full cited statements) for all 21 step/node pairs.
- `searches.jsonl`: actual search-command records for this item. Original searches in the live node were preserved and fresh logged searches appended to the node.

New nodes: 0. New Mathlib leaves: 0. The proof needs no additional unsplit fact: the only substantive scheme-action input is the existing integer-grading theorem, and the residue-zero projection, finite ideal generation, and subgroup operations are written out in the item's steps.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact id, fixed subgroups, diagonalizable groups, centralizers, roots of unity, and the group-scheme directories. The nearby declarations concern fixed abelian groups, Frobenius fixed points, invariant rings of finite abstract groups, or centralizer equations for matrix groups; none states this relative smoothness assertion. No Lean was written and no compiler, Lake, or build tool was run.

## Literature wanted

WANTED: Conrad, *Reductive group schemes* (2014), Lemma 2.2.4, Example 2.2.6 and the proof of Lemma 4.2.2, for the item's original reference; local archive `literature/conrad-reductive-group-schemes.pdf` is absent. The author PDF at https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf was read online. No download was written to the read-only repository. The delivered proof does not assume the centralizer theorem: it is marked agent-written and uses the locally available Stacks grading and lifting statements.

## What was wrong or incomplete

The item was statement-only and required a proof that works when the order of the roots-of-unity scheme is not invertible. Finite abstract group averaging or a field-only centralizer theorem would not give it. The statement is correct and has not been changed. The original group-scheme reference `def-sc-group-scheme` is field-based, but the item explicitly defines the required operations and diagrams over its arbitrary base; the proof uses that inline definition and does not specialize the base to a field.

The current blueprint and its direct-image proof (3) were read at `literature/blueprint/latest/`; the item is a supporting node in the inherited contracted-curve linearization chain, not a key statement of its unit. No unit/chapter file is changed. `blueprint_refs.py ancestor` reports `None` for this inherited chain; the original `from.node=null`, precise `from.place`, and `via` list are retained. Searches across the imported blueprint for fixed subgroups, diagonalizable groups and roots of unity found no equivalent statement. Existing general grading and ring results are reused.

## What could not be finished

Nothing mathematical remains in this split. The newly specified proof is natural-language stage 1 only. Delivery validation is recorded below after the required dry run.

## Not duplicates

No new nodes are proposed, so there are no new-node/existing-node tag pairs to distinguish. The existing `lem-sfb-gm-fixed-square-zero-lifting` was read: it lifts points fixed by the whole multiplicative group, whereas this item concerns its possibly nonreduced finite subgroup. It is not cited as though it applied to mu_n. Instead its elementary projection idea is carried out explicitly for residue weights. The general `lem-sfb-group-algebra-coaction-grading` and diagonalizable representation nodes were also found; the already available `lem-sfb-gm-affine-action-grading` supplies exactly the algebra grading and point evaluation formula needed here.

## Review by NC

I read Stacks `groupoids.tex`, Tag 0EKK (`lemma-complete-reducibility-Gm`) and its proof by unique Laurent coefficients, together with Tag 0EKJ (`example-Gm-on-affine`). I also read `algebra.tex` Tag 00F3 (`definition-finite-type`) and the surrounding presentation discussion, Tag 00TN (`proposition-smooth-formally-smooth`), and `more-morphisms.tex` Tags 02H4 (`lemma-affine-formally-smooth`) and 02H6 (`lemma-smooth-formally-smooth`). Conrad Lemma 2.2.4 corroborates the relative theorem including nonsmooth multiplicative-type subgroups; Example 2.2.6 explains the semidirect-product application. I do not cite any SGA source, or use an omitted SGA proof. There are no new nodes whose sources need independent checking.

I opened every cited DAG node and checked its statement, rather than taking facts from its proof. Step 1 uses `lem-sfb-gm-affine-action-grading` for the R-submodule decomposition, multiplication of weights and homogeneous point-evaluation formula; all are expressly in that statement. `lem-weil-pbc-lfp-affine-opens-finite-presentation` applies to the whole affine source and base and gives a finite algebra presentation. Regrouping into Z/nZ residues is a finite-support rearrangement, with no flatness assumption.

Step 2 uses the grading evaluation formula and `lem-weil-pbc-monic-quotient-free`, which explicitly supplies the basis 1,u,...,u^(n-1) for the monic quotient over an arbitrary coefficient ring. The universal unit in B[u]/(u^n-1) detects all the nonzero residue weights even when geometric points do not. The coefficient of u^r, for 0<r<n, is x(c_k), so no cancellation, separability or invertibility of n is assumed. For the zero coefficient ring all values are zero and the conclusion is immediate. The converse is checked on every algebra extension, not just on B-valued roots.

Step 3 uses the affine spectrum correspondence and the affine quotient characterization that `def-weil-closed-immersion` actually states. The ideal I is an explicit construction. The factorization through the quotient is the elementary universal property of a quotient ring.

Step 4 uses `lem-weil-pbc-fibre-product-affine-spectra` for the coordinate ring D tensor_R D and its two universal maps, and the affine spectrum correspondence for the three group operations. The pointwise subgroup condition gives vanishing of I on each universal operation, so it really gives morphisms, not only a group structure on geometric points. Injectivity of the inclusion on all test algebras verifies the group diagrams. This handles the arbitrary-base group definition explicitly.

Step 5 gives the finite-generator argument inside the item, rather than proposing it as a new node. The finitely many homogeneous components of finitely many algebra generators still generate. Projecting a polynomial expression onto a nonzero residue class leaves only monomials divisible by a bad-residue generator, proving that those finitely many generators generate I. `lem-weil-pbc-finite-presentation-quotient-fg-ideal` states precisely the resulting finite presentation of D. No Noetherian hypothesis is inserted.

Step 6 uses `lem-weil-pbc-smooth-ring-map-iff-smooth-affine` on the actual affine smooth morphism H -> S. The statement of `lem-weil-pbc-smooth-ring-map-square-zero-lifting` explicitly allows every R-algebra B, any ideal J with J^2=0, and any map to B/J; these are exactly the hypotheses here. In particular I did not cite only a definition of smoothness for a separate exactness or obstruction theorem.

Step 7 is the elementary three-case multiplication check for projection to residue zero. The case r+s=0 with r nonzero is written separately: both f(a) and f(b) lie in J, so their product vanishes by J^2=0. Thus the projection is a ring map in precisely this lifting situation, not an asserted ring map on the original graded algebra. It kills the generators of I and hence I, and its reduction equals the original map on every residue component. This is one direct computation, not a hidden equivariant lifting lemma.

Step 8 applies `lem-weil-pbc-fp-square-zero-lifting-smooth-ring-map` with exactly the finite presentation and all square-zero lifts proved in steps 5--7. The affine smoothness comparison then gives smoothness of F -> S. The cited qcqs permanence statement explicitly gives finite presentation for an affine source over a quasi-separated target with local finite presentation; S is affine. The finite algebra presentation supplies the required whole affine chart, as `def-sbc-locally-finite-presentation` states. The two smooth ring-map inputs are generic off-unit tools, declared in `split_report.tool_uses`; neither replaces a unit route step.

Step 9 uses the base-change definition and fibre-product universal property exactly as their statements give them: B-points over R' are the original B-points with their fixed R'-structure. Every B-algebra inherits that structure, so the two fixedness quantifiers are identical. This proves arbitrary base change by functors directly; it does not identify an invariant submodule after a nonflat tensor product. For closedness, the fibre-product affine coordinate statement gives the tensor algebras and the explicit mutually inverse quotient maps give the quotient presentation; `def-weil-closed-immersion` then applies. This quotient identification is written with its maps rather than hiding an exactness claim.

I tested n=1 (I=0, the projection is the identity and F=H), the trivial action (again I=0), the zero ring (all tests are vacuous), and H=G_a with weight k. In the last example F=G_a when n divides k and is the identity section otherwise, including R=F_p and n=p. Thus weight one has trivial fixed subgroup for mu_p despite every field-valued p-th root being 1; this specifically tests the scheme-theoretic condition. I also checked opposite residue weights on R[x,y] with weights 1 and -1: the projection kills their individual lift values in J and their product in J^2, exactly as step 7 needs. No step exceeds 2000 characters. The nine steps have actual uses equal to proof_deps, and citations.json contains each full verbatim statement.

The main correction while writing was to avoid treating the whole-G_m fixed lifting node as a theorem for mu_n, and to avoid using the field-only group-scheme definition as a theorem over an arbitrary ring. Both issues are resolved by the explicit residue computation and the universal coordinate formulas above.

## Validation

The required `deliver.py NC lem-sfb-mu-n-fixed-subgroup-smooth --no-push` exited 0 and printed `OK (not pushed)` at 76999075edf: server preflight passed, including the DAG and split checks. It created the delivery in its own worktree; no git command was run by the worker in the shared repository. A final dry run checks this validation note before pushing.
