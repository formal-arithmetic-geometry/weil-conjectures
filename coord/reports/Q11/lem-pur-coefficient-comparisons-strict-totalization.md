## Worker report

The delivery states `CategoryTheory.CochainPullback.StrictCoefficient.coefficientComparisonsStrictTotalization` in `Sheaf.SecSmoothPurity.CoefficientComparisonsStrictTotalization`. Its proof is the sole `sorry`. Every helper is a definition with actual data or an explicit proposition; no map or isomorphism is obtained from an unconstrained existence assumption.

Sources read: Stacks `sites-modules.tex`, Section 03EK (the sheafified tensor and its bilinear universal property), Tag 03EL `lemma-tensor-product-pullback`; `sites-cohomology.tex`, Tag 07A4 `lemma-pullback-tensor-product` (its ordinary total-complex constituents); the full item and its eight proof steps; the current blueprint `sec-six-functors-basics/sk-def-purity-conv/def-weil-frobenius-coefficient-twists.md` (finite reduction/scalar-extension compatibility). The ordinary comparison here needs neither K-flatness nor flat terms: those hypotheses in the derived source are used only to represent derived tensor by ordinary total tensor, whereas this item explicitly concerns the ordinary total.

The item statement is unchanged. Its `stmt_deps` gains the already landed `def-pur-normalized-coefficient-diagram`, whose record attaches the exact definition interface already present in `StrictCoefficientComparisonCalculus`. No new node or dependency module is introduced. In particular, `strictCoefficientComparisonCalculus` is neither an assumption nor a proof input. As disclosed by the existing unit/composition sibling, importing these definitions prevents the parent module from importing this proof module directly without factoring its interface later; no theorem-level dependency cycle is introduced in the DAG.

Hypothesis-by-hypothesis correspondence:

| Node input | Lean rendering |
| --- | --- |
| Two small sites and a geometric morphism | independent `C : Type uC`, `Category.{vC} C`, `D : Type uD`, `Category.{vD} D`, `EssentiallySmall.{w}` and topologies `J`, `K`; `d.inverse`, `d.direct`, `d.adj`, `d.finiteLimits` |
| Two inverse sequences of commutative rings on each site and maps between them | the 0 and 1 rows of `d.R`, `d.S : Fin 3 × ℕᵒᵖ ⥤ Sheaf ... CommRingCat.{w}`; natural coefficient arrows are their horizontal maps, and all sequence arrows are retained |
| Algebraic inverse images and compatible phi | `d.RI`, `d.algebraic`, `d.graph`, and the natural transformation `d.phi`; `Diagram.square` supplies the coefficient square |
| Actual module sheaves and tensors | `Modules`, transparently `ringedSiteModules`/Mathlib `SheafOfModules`; `cochainModulesMonoidal`, its sheafification tensor, and `total P Q = P ⊗ Q` |
| F and S are the given tensor constructions | `d.ringed i`, with `L`, `hobj`, `hmap`, module adjunction presentation; `extensionFunctor`, `extend` for S; no arbitrary substitute functor |
| All integer degrees and unbounded direct sums | `Complex R = CochainComplex (Modules R) ℤ`; the existing tensor is `CochainComplex.mapBifunctor` with summands p+q=n and signed differential |
| Normalized degreewise k, s and fixed c | `e : Comparisons d`, `c : ∀ i, Comparison (d.ringed i)`, `e.Normalized c`; `IsScalarAssociation` fixes k on generalized scalar-unit generators, hence by balancing/linearity on all b tensor (a tensor x); `Comparison` contains naturality and the generalized pure-tensor prescription fixing s and c and their inverses |
| Arbitrary semilinear chain transitions | every quantified `f : (extend rho).obj P ⟶ P'` and `g : ... ⟶ Q'` is an arbitrary scalar-extension adjoint of a semilinear chain map; it is not an isomorphism or a unit transition |
| Strict morphisms | the same arbitrary linear/semilinear arrows are quantified in the naturality and transition laws; applying these laws to the constituent arrows gives naturality for every strict morphism |

The existing index contains three rows because it is shared with the successive-extension sibling. This does not require extra input: extend any two-row diagram by repeating row 1 at row 2, with identity 1-to-2 maps; the same algebraic inverse images, phi and pullback presentations extend by repetition. All conclusions are local to a chosen arrow/square. Conversely restricting to rows 0 and 1 recovers exactly this item's data. The theorem does not assume any unit/composition/transition predicate from the parent; it asserts only this item's laws. This is the same definition interface used by the landed unit/composition item.

Clause-by-clause correspondence:

| Node conclusion | Lean rendering |
| --- | --- |
| Degreewise k is a natural chain isomorphism | existing `e.kappa` is a natural module isomorphism, and `e.kappaC` is exactly its `NatIso.mapHomologicalComplex` lift. Its hom and inverse are chain maps in every degree, naturally in every input complex |
| s and c are the direct-sum total chain isomorphisms | existing `sigmaRC`, `sigmaSC`, `comparison`; `TotalSummands` asserts in both directions that the whole-total map restricts to the normalized module map on every inclusion, for all p,q,n |
| Separate differential commutation for k and inverse | `e.KappaDifferentials`, `v : Fin 2`, both hom and inv equations; the two branches are actual Mathlib `mapBifunctor.D₁` and `D₂` |
| Separate differential commutation for s,c and inverses | `TotalDifferentials` for each vertex and both scalar extensions; four equations specify D₁/D₂ for hom/inv. D₂ already carries (-1)^p, including negative p |
| Naturality in both arguments | `TotalNaturality` for c and both s, with separate forward/inverse equations. Naturality of k is in the original `e.kappa` natural isomorphism |
| k and inverse commute with all sequence transitions | `e.KappaTransitionLaws` on every commuting square and arbitrary f; the inverse equation follows by cancelling the comparison isomorphisms, with no cancellation of f. `kappaTransitionForward` and `kappaTransitionInverse` are the actual comparison-then-transition routes |
| s and inverse commute with all transitions | `TensorTransitionLaws d.R e.sigmaR` and its S counterpart, on arbitrary f,g; the inverse square is equivalent by cancelling the displayed comparison isos, never f or g |
| c and inverse commute with all transitions | `e.PullTensorTransitions c`, again arbitrary f,g. Inverse compatibility is obtained by cancelling only the c/s isomorphisms |
| k transition value rho_X^1(b) i_n(rho_X^0(a)) tensor (1 tensor t_K x) | first conjunct of `e.KappaTransitionValues`, with coefficients `v,z`; `inverseSectionMap` is the actual algebraic inverse-image t_K and `diagramInsertion` supplies the inner unit |
| inverse k transition value rho_X^1(b) phi_n(u^{-1}rho_Y^1(d)) tensor (1 tensor t_K x) | second conjunct of `e.KappaTransitionValues`, coefficient `z' : d.RI.obj j`; its formula contains `d.RI.map s` then `d.phi.app l` |
| s transition value (rho_W^1(b) tensor t_K x) tensor (1 tensor t_H y) | first conjunct of `TensorTransitionValues` for both ring diagrams; `totalPure` includes the prescribed section in the actual p,q summand |
| inverse s transition value rho_W^1(b)rho_W^1(d) tensor (t_K x tensor t_H y) | second conjunct of `TensorTransitionValues`, with coefficients `v,v'`; it multiplies the two images under `B.map s` |
| c transition value (rho_X^a(a) tensor t_K x) tensor (1 tensor t_H y) | `e.PullTensorTransitionValues c`; generalized x,y,z with their explicit homogeneous tensor relation, then application of the same inverse-image functor and canonical generator maps |
| Both orders have the displayed transition values | the displayed-value predicates give the comparison-then-transition route; the corresponding whole-total transition equalities give the other route, including inverse comparison by cancellation |
| c1 F1(sY) k = T1(k,k) sX SX(c0), including inverse equality | `e.TensorSquare c`, equality of the actual composite chain isomorphisms; applying inverse to this equality gives precisely the reverse composite equality |
| Full-generator value (b i_X(a) tensor (1 tensor x)) tensor (1 tensor (1 tensor y)) | `e.TensorSquareValue c`: coefficients `b,b'`, generalized homogeneous input z, and output coefficient `b * d.S.map a b'`; the two inner insertions are `insertion`, and the target uses the actual pullback generator |
| Entire totals, not merely individual pure tensors | all comparison and transition equations are equations of morphisms/isomorphisms of full cochain complexes; `TotalSummands` specifies every direct-sum inclusion. There is no global pure-section generation assumption |
| No flatness, bounds or invertibility of transition adjoints | no such binder is present; degrees are all ℤ and f,g are arbitrary |

`semilinearSectionMap` uses the scalar-extension unit followed by the chain map, so t_K and t_H are the underlying semilinear maps, not the scalar-extended adjoints evaluated without a unit. `inverseSectionMap` transports this map through the recorded module-underlying inverse-image isomorphisms; it never assumes an inverse-image local section lifts to a source local section. `diagramGeneratorSection` simply exposes that same section in its module carrier so its scalar action elaborates.

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the existing Mathlib module-sheaf category.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: `SheafOfModules.cochainModulesMonoidal`, `cochainModulesPreadditive`, `cochainTensorLeftPreservesColimits`, `cochainTensorRightPreservesColimits`; all are the existing localization tensor with independent site universes.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`, `ιMapBifunctor`; `Mathlib.Algebra.Homology.Bifunctor`: `mapBifunctor.D₁`, `D₂`.
- `Sheaf.SecSmoothPurity.CoefficientComparisonsBalancedConstruction`: `CoefficientComparisonsBalanced.coefficientComparisons_balanced_construction`, `Square`, `PullbackFormulas`, `ViaCommonPullback`, `ScalarTensorFormulas`, `ScalarTensorConstruction`. Read their full definitions: the assumed normalized isomorphisms are canonical, natural in every module morphism, and use actual sheafified tensors.
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`: `CochainPullback.cochainPullbackTensorCoherence`, `HasTensorCoherence`; its public `CochainTensorCoherenceData`/`CochainCoefficientArrows` give `Modules`, `Complex`, `RingedPullback`, `Comparison`, `pull`, `comparison`, `extensionFunctor`, `extend`, `insertion`, `generator`, `extensionTmul`.
- `Sheaf.SecSmoothPurity.StrictCoefficientComparisonCalculus`: the definition-only record of `def-pur-normalized-coefficient-diagram`, including `Diagram`, `Comparisons`, `Normalized`, `kappaC`, `sigmaRC`, `sigmaSC`, `pullArrow`, `tensorArrow`, `squareArrow`, `TensorTransitionLaws`, `KappaTransitionLaws`, `total`, `totalMap`, `totalIso`. Its existence theorem is not used.
- Proof imports: `Mathlib.CategoryTheory.Limits.HasLimits` (colimit), `Mathlib.CategoryTheory.Adjunction.Limits` (`Adjunction.leftAdjoint_preservesColimits`), `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal` (`tensor_bilinear_universal`), and `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction` (the recorded general module adjunction). These are the stated proof dependencies and are imported without `public` when used only in the future proof.

Edge cases checked mathematically before finalizing: zero rings and zero modules require no cancellation of coefficients; zero transition maps are valid arbitrary f/g and send all displayed values to zero; identity scalar extensions insert and multiply 1; non-flat scalar extension such as Z to Z/2 is permitted (the statement is ordinary tensor, not homology); negative odd p gives the same negative sign on both sides because comparisons preserve bidegree; unbounded complexes and infinitely many pairs p+q=n use coproducts, not products. An empty site and all-zero complexes remain valid. No independent index universe or equality of site-object and site-morphism universes is imposed.

Searches made with `msearch.py Q11 lem-pur-coefficient-comparisons-strict-totalization`:

- LeanFinder: “Degreewise scalar extension and pullback tensor comparisons on unbounded cochain complexes commute with semilinear inverse sequence transitions”. Eight hits: homological-complex unitors, `ConnectData.restrictionLEIso_inv_f`, extend-single maps and a HomComplex identity. No strict coefficient comparison statement.
- Loogle: `HomologicalComplex.mapBifunctorMap, CochainComplex.mapBifunctor`. Four hits, the first/second bifunctor-shift naturality lemmas and associated forms. They do not state coefficient or semilinear-transition compatibility.
- Grep: `semilinear|[Ss]trict[Ss]ystem` in `Mathlib/Algebra/Homology`: zero hits.
- Project rg: `Strict.*(System|Cochain)|strict.*(System|Cochain)|Semilinear|semilinear|CoefficientComparisons`, followed by targeted searches in `SecSmoothPurity`, `CategoryTheory`, and upstream `WeilConjectures`. Found the landed normalized-diagram interface and unit/composition sibling, which are reused. The parent theorem asserts the entire simultaneous calculus including units/composition and existence/uniqueness, and is not this conditional strict-totalization lemma.
- Project/upstream rg for this item id, `strict.*totalization`, `strictTotalization`: only unrelated totalization comments; no existing statement.
- Searched helper names `semilinearSectionMap`, `TotalDifferentials`, `KappaTransitionValues` in Sheaf, WeilConjectures and `dag/lean_names_upstream.json`: no conflicts.

The module contains 20 helper definitions and one theorem, each documented with source and blueprint id. The theorem docstring supplies all eight proof steps and their dependency uses. The helpers package only this node's own clauses and canonical routes; none moves an independent mathematical assertion into a new prerequisite. No statement fault or disputed assertion was found.

Validation: every compile uses `scompile.py`, compiling the sandbox module and the actual module name independently against the published live build. The final delivery dry run and delivery results are recorded below after completion.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
