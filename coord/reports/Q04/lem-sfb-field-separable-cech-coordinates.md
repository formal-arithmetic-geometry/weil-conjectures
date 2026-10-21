# Q04: lem-sfb-field-separable-cech-coordinates

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-field-separable-cech-coordinates.json`: statement, split into ten proof steps; not a Mathlib leaf.
- `citations.json`: one verbatim statement quotation for each node cited in each step.
- `report.md`: this report and signed mathematical review.

There are **0 new nodes and 0 new Mathlib leaves**. The auxiliary text extractions, search log, and sandbox script are research records, not delivered node files.

## Attachments

None. I searched the live `lean/WeilConjectures/` by item id, Cech/Galois keywords, and lisse/field notions. `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_iso_biproduct_of_isAlgClosed` in `SixFunctors/ProEtale/Adic/AlgClosedField.lean:52` concerns algebraically closed geometric fields and the restricted adic coefficient construction. It does not state the arbitrary separably closed geometric-field, arbitrary continuous normed-coefficient, Cech, and scalar-extension clauses. The field-coefficient `Constructible.lean` defines lisse and pullback stability, but supplies no declaration stating this whole item. No partial declaration is claimed as an attachment.

## WANTED

None. All sources needed for the proof are present locally. No SGA source is used.

## Corrections and scope

The item's statement is unchanged; no statement dispute was found. It had an empty proof, and its source cited Lemmas 7.3.9 and 7.4.10 as background for an agent expansion. Neither is by itself an arbitrary-topological-coefficient Cech theorem: the first concerns set local systems and the second fundamental groups. The proof now uses explicit finite Galois algebra, the Krull limit, the existing condensed evaluation theorem and the split-cover criterion. `proof_origin.by` remains `agent` because the assembled incremental-coordinate and scalar-matrix argument is an expansion rather than a verbatim proof in the cited paper.

I added statement dependencies for the fibre product, the profinite test object and the coefficient morphism, all notions appearing in the statement. The original statement dependencies were retained. The blueprint place now identifies direct-images proof (3) and the generic-field use in the parent monodromy proof. The current `blueprint_refs.py ancestor` returns `None` for the existing created-item chain; I preserved that linkage and filled its exact place rather than inventing an imported ancestor. This item is not the unit's key statement, so it does not fill the unit's realized fields. The current main-20261015 unit is in `sec-six-functors-basics/sk-thm-sf-ctf-stability/`; the existing same-named unit JSON retains an older `sec-six-functors` route. Neither is edited here.

The Cech-ring scalar clause means the coefficient morphism and ordinary internal module extension. It does not assert the generally unjustified equality `C(S,A) tensor_A B = C(S,B)` for global-section tensor products. The coequalizer calculation is internal to sheaves and specializes correctly to free modules.

## What remains

No unfinished part of this stage-1 item. The cited existing unsplit dependencies remain their own items. No Lean file was written, no compiler/build tool was run, no agent was started, and the repository was only read.

## Not duplicates

No new nodes. I searched the whole DAG by separable closure, Cech/Galois, continuous coefficients, weak contractibility, tensor colimits, and affine limits, and ran blueprint searches for separable, continuous, Galois, tensor, and clopen. The whole item has no equivalent imported blueprint node. Existing more general inputs are cited instead of duplicating them: finite-set containment in a finite Galois subextension, the Krull finite limit, finite Galois tensor decomposition, geometric-point coefficient evaluation, w-contractible clopen refinements, internal/sectionwise modules, and continuous coefficient realization.

## Mathlib searches

The item's previous recorded searches were preserved. New searches were run only through `batch2/msearch.py`; exact queries and returned declaration names are appended to its `mathlib_searches`, with the command log retained in `searches.jsonl`. I used LeanFinder twice with different formulations, Loogle, LeanSearch, and source grep. Both LeanFinder phrasings returned algebraic etaleness/separability and rank-at-stalk results, not the item. LeanSearch returned free module sheaves and their pullbacks; I read `Mathlib/Algebra/Category/ModuleCat/Sheaf/Free.lean` and the field-etaleness candidates in `Mathlib/RingTheory/Etale/Field.lean`. They are relevant components but do not imply the whole geometric Cech/coefficient statement by a one-line specialization. Loogle and the concept grep returned no hits. All these services ran successfully; none was recorded as unavailable or as an unexecuted query.

## Review by Q04

I read Bhatt–Scholze Example 4.1.4, Definition 4.1.1, Lemma 4.2.12 and the following component-space discussion, Example 7.3.5, Lemma 7.3.9 and Lemma 7.4.10 in the locally extracted paper, and Hemo–Richarz–Scholbach Example 3.1 (p. 6). I also read the main-20261015 chapter, the unit and direct-images proof (3), the geometric-point coefficient proof, and the w-contractible clopen-partition proof. For the algebraic bridge I read Stacks `fields.tex`, labels `lemma-infinite-galois-limit` (0BU2), `lemma-normal-closure` (09DT), `lemma-normal-closure-galois` (0EXM), `pione.tex` section `section-finite-etale-under-galois` (03SF), and `limits.tex` label `lemma-directed-inverse-system-affine-schemes-has-limit` (01YW). Stacks `proetale.tex`, label `lemma-w-local-strictly-henselian-extremally-disconnected` (0982), verifies the contractibility criterion. There are no new nodes requiring additional source audits.

For step 1 I opened the statements of the separable-closure Galois node, finite-subset Galois-containment node, algebraic-separable-smooth node, ind-etale stability node, separable-closure definition and site definition. They respectively give normality/separability, containment INSIDE the chosen closure (not merely embeddings into an abstract extension), finite etale stages, weak etaleness, faithful flatness and the actual affine covering criterion. Directedness is written out by taking a finite union of generating sets. The index is a set of intermediate fields inside the fixed universe, not an arbitrary large category.

For step 2 I read both clauses of `lem-exc-finite-galois-tensor-decomposition` and deliberately use its algebra clause (1), not its etale sheaf evaluation clause (2) for a non-etale infinite cover. The tensor-pushout node says exactly the bilinear multiplication and universal property used for base change. The iteration and finite-product passage are written in the step; there is no new lemma merely restating the two-fold Cech clause. The successive-increment formula was checked at q=0, q=1, and q=2, including the multiplication order.

For step 3 the tensor-colimit statement applies to a small directed system of underlying k-modules and gives the required canonical maps; these maps preserve products on pure tensors, hence the identifications are algebra identifications too. The affine Spec-colimit statement is precisely the schemes-limit assertion needed. The Krull node actually says topological group isomorphism and directedness; it is not cited for the field-union assertion, which step 1 already establishes from the finite-subset node. The profinite-test-object definition gives exactly the inverse limit over finite quotients. Compactness reduces every finite clopen quotient of the finite power to one finite Galois stage, with the cylinder/common-upper-bound argument included. The fibre-product definition and tensor pushout are used only through their displayed universal properties.

Step 4 is the explicit elementary substitution on those coordinates, not a reference to an unspecified standard Cech convention. On triples the vertices are x, xg, xgh; the transition from the last vertex to the first is the product c(g)c(h), so the chosen equation is c(gh)=c(g)c(h). The first face also changes the base vertex, which is retained in the argument.

For step 5 I opened `det-pe-condensed-point-coefficients`, the point-pullback composition definition, pulled-back-coefficient definition, the continuous-field realization node and the locally-constant prime-spectrum node. The first works for SEPARABLY closed Omega and ANY topological ring, not just a locally compact coefficient. The composition node is explicitly monoidal, so it identifies the ring structure, not just an underlying set. The realization node assumes a totally disconnected normed field; the clopen-ball argument verifies that hypothesis without completeness. Its adjoint characterization and actual continuous-function model justify the face maps even when the first vertex moves. The spectrum node gives the topology S because Spec Omega is a singleton. No faithful geometric-stalk detection claim is used.

For step 6 I checked the actual definitions of w-strict locality and strict henselianity, then the full conclusion of `det-pe-wcb-clopen-partition`. For a separably closed field the henselian ideal is zero, so lifting is identity on each finite algebra. The partition theorem supplies morphisms from the clopen pieces into covering members; connectedness and nonemptiness of this point turn one of those into a section. It is not being cited just for an epimorphism, nor for contractibility without its hypotheses. The lisse definition explicitly allows rank zero and varying local ranks; choosing a section suffices regardless of those variations.

Step 7 cites the general-condensed module pullback/composition statement, not the finite-coefficient-only equivalence or the admissible-only Cartesian-coefficient theorem. The strong monoidal coefficient composition and the left-adjoint scalar-extension definition justify pulling a trivialization back to the point and retaining its regular free module. The identities use u composed with s equal to the identity. This is an elementary consequence of the cited functor constructions, with no extra coefficient-field hypothesis.

For step 8 I read the internal-abelian/sectionwise module equivalence: it keeps sections and restrictions IDENTICALLY and applies to a commutative ring object with the specified site-size and monoidal-sheafification assumptions. Those are the project's existing small-site conventions. The proof then explicitly evaluates standard basis sections and reconstructs each morphism sectionwise. Its matrix entries are in A because step 5 with q=0 gives Gamma(R_A)=A. Both empty matrix dimensions are checked.

Steps 9 and 10 cite, respectively, the continuous-map ring-morphism definition and the ORDINARY internal coequalizer scalar-extension definition. I checked that the former says postcomposition and strict functoriality, and the latter supplies the two balancing arrows and left adjunction. The formulas b tensor a -> b phi(a), b -> b tensor 1 are inverse by those balancing relations; applying a matrix to the basis gives entrywise phi. Precomposition with each face commutes with postcomposition by associativity of function composition. Nothing requires flatness of a tensor product of section rings, a completed tensor, or completeness of A or B.

Against delivery-errors B–E: every proof citation has a verbatim statement quotation in `citations.json`; every cited statement was opened; proof_deps is their union; off-unit statements are explicitly declared as generic tool uses; no new unsplit node hides a proof, repeats a clause, or duplicates an existing node. All ten steps are below 2000 characters. I checked no cited dependency reaches the item. I tested k separably closed (G=1), q=0, q=1, q=2, m=0, n=0, incomplete coefficients such as a normed algebraic closure, and imperfect separably closed geometric fields. These checks leave the statement unchanged and establish each compatibility claimed, within the ordinary internal-module interpretation above.

Q04 signs this split and its source/citation audit.
