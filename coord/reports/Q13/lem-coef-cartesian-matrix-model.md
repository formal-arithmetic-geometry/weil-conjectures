## Worker report

`Sheaf.CategoryTheory.CartesianMatrixModel` states
`HomotopicalAlgebra.cartesianMatrixModel`. Its sole postponed proof is that theorem.
Its conclusion is `Nonempty (CartesianMatrixModelData V S)`: an existential witness
containing the actual model and monoidal structures, their properties, the canonical
convolution maps and coherence, and both natural adjunctions. No witness is chosen
from this existence theorem. The supporting definitions contain explicit data only.
All supporting declarations belong to the matrix construction specified by this
node and are listed in `lean.declarations`; no independent notion or new DAG node
is introduced. The node changes only in `lean`.

The source was opened at
https://msp.org/agt/2011/11-3/agt-v11-n3-p13-p.pdf, Definition 10.1 (printed pp.
1595–1596), Remark 10.2 and Proposition 10.3 (pp. 1596–1597). These give the two
factor orderings and both internal-hom formulas used here. The all-cofibrant
cartesian specialization and additional left-properness and tractability assertions
are exactly those in the node and its twelve proof steps.

Hypothesis correspondence:

| Node hypothesis/convention | Lean rendering |
| --- | --- |
| A category with the model classes and model axioms | `[Category.{v} V] [ModelCategory V]` |
| Complete and cocomplete in the chosen small universe | `[HasLimits V] [HasColimits V]` |
| Combinatorial, including set-generated weak factorization systems and functorial factorizations | `_hV : CombinatorialModelCategory.{u, v, v} V` |
| Every object cofibrant | `_hcof : ∀ X : V, IsCofibrant X` |
| Tractable: generating cofibrations have cofibrant sources | Already follows from `_hV.cofibrationsGenerated` and `_hcof`; no extra assumption is required |
| Cartesian closed underlying category | `[CartesianMonoidalCategory V] [MonoidalClosed V]`, the current Mathlib encoding of cartesian closedness |
| Cartesian pushout-product axiom and its two trivial cases | `_hprod`: for arbitrary arrows `f g`, cofibrations imply a cofibration pushout product, and a weak-equivalence input implies a weak-equivalence output |
| Left proper | `_hleft`: `WeakEquivalence e → Cofibration i → WeakEquivalence (pushout.inr e i)` |
| Any small vertex set, including empty | `(S : Type v)`, with no nonemptiness or finiteness instance |

Conclusion correspondence, using fields of `CartesianMatrixModelData`:

| Node clause | Lean rendering |
| --- | --- |
| Families and coordinatewise morphisms | The existing Pi category on `S → S → V` |
| There exists a model structure | The instance field `model`, under `Nonempty` |
| Combinatorial | `combinatorial`, in the same small universe `v` |
| Weak equivalences, fibrations, cofibrations all coordinatewise | `weakEquivalences_iff`, `fibrations_iff`, `cofibrations_iff`, each for every family arrow and every pair `s t` |
| Every graph cofibrant | `all_cofibrant` |
| Left proper | `left_proper`, the pushout condition on family arrows |
| Tractable | `tractable`, a small generating cofibration family with cofibrant sources |
| Given any base generating families I,J, their supported maps generate | `generators`, universally quantified over both families and their generating equalities, with `matrixSupportedArrow d (i a)` and `matrixSupportedArrow d (j a)` |
| A supported arrow is the input at d and identity of zero elsewhere | `matrixSupportedArrow` reuses `GradedObject.single (C := V) d` on endpoints and morphisms, then rewrites the pair index as two indices |
| Limits and colimits exist and are coordinatewise | `limits`, `colimits`, and `coordinate_limits`, `coordinate_colimits` for every `matrixEvaluation s t`; the evaluations of a Pi category jointly detect the universal properties |
| Tensor object at (s,t) is the coproduct of P(r,t)×Q(s,r) | `tensor_obj`, using the explicit `matrixConvolution` |
| Tensor on arrows is coproduct of product maps | `tensor_map`, equality after each `matrixTensorInclusion` |
| Unit is terminal on the diagonal, initial elsewhere | `unit_diagonal`, `unit_off_diagonal` |
| Reassociation and reindexing give the associator | `associator_summand`: the same two intermediate vertices on both sides, and the base product associator on the three factors |
| The two unitors delete the diagonal terminal factor | `left_unitor_summand`, `right_unitor_summand`, using the base cartesian unitors |
| Monoidal naturality, triangle and pentagon | The `monoidal : MonoidalCategory (S → S → V)` field; the three summand fields specify the canonical coherence, not arbitrary objectwise isomorphisms |
| Right adjoint of P⋆−, with the displayed product/exponential formula | `rightHom`, `rightHom_obj`, `rightHom_map`, `right_adjunction`; `matrixConvolutionRightHom P H s r = ∏ᶜ t, [P(r,t),H(s,t)]` |
| Right adjoint of −⋆Q, with the displayed product/exponential formula | `leftHom`, `leftHom_obj`, `leftHom_map`, `left_adjunction`; `matrixConvolutionLeftHom Q H r t = ∏ᶜ s, [Q(s,r),H(s,t)]` |
| The two adjunctions are natural | Actual functors and Mathlib `Adjunction` data, with map formulas fixed by `matrixRightHomMap` and `matrixLeftHomMap` |
| Cofibrant unit | `unit_cofibrant` |
| Graph pushout-product axiom, including either trivial input | `pushout_product` |
| Nonsymmetric monoid axiom | `monoid_axiom : NonsymmetricMonoidAxiom (S → S → V)`, the recorded dependency's full definition |
| No symmetry assertion | No graph braiding or symmetry field is requested |
| Chosen universes retained | Objects of V are `Type u`; Hom sets, S, all generator index sets and all limit/colimit shapes are in universe v. Family objects are `Type (max u v)`, and family Hom sets remain `Type v`. No larger index universe is introduced |

Dependency declarations read and used:

- `lem-coef-model-infinity-derived-adjunction`: imported
  `Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction`; read the full signature and
  docstring of `HomotopicalAlgebra.ModelInfinity.quillenAdjunctionInfinityLocalization`.
  Its model-category/cofibrancy conventions use Mathlib's `ModelCategory`,
  `Cofibration`, `Fibration`, `WeakEquivalence`, `IsCofibrant`, `HasLimits`,
  `HasColimits`, with functorial factorizations made explicit.
- `lem-coef-combinatorial-localization-presentability`: imported
  `Sheaf.CategoryTheory.CombinatorialLocalizationPresentability`; read its theorem
  `HomotopicalAlgebra.ModelLocalization.combinatorialLocalizationPresentability`.
  The precise `CombinatorialModelCategory` record used here is declared in its
  public import `Sheaf.CategoryTheory.ModelColimitLocalizationComparison` and was
  read in full: local presentability, two small generating families and two
  functorial factorizations.
- `def-coef-nonsymmetric-monoid-axiom`: imported
  `Sheaf.CategoryTheory.NonsymmetricMonoidAxiom`; read both
  `HomotopicalAlgebra.nonsymmetricMonoidGenerators` and
  `HomotopicalAlgebra.NonsymmetricMonoidAxiom`. This includes arbitrary auxiliary
  objects, nonempty left-associated products, and pushout, transfinite and retract
  closure in universe v.
- `def-sfb-monoidal-category`: its Mathlib match
  `CategoryTheory.MonoidalCategory`, including `MonoidalCategoryStruct`, naturality,
  pentagon and triangle, read in `Mathlib.CategoryTheory.Monoidal.Category`.

The stated proof leaves are imported for stage 3: `Mathlib.CategoryTheory.Presentable.Presheaf`
(and `Type`) for presheaf local presentability; `Presentable.LocallyPresentable`
for object presentability; `Mathlib.SetTheory.Cardinal.HasCardinalLT` for regular
bounds; `Mathlib.CategoryTheory.MorphismProperty.LiftingProperty` for lifting-class
closure; and `Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting`
for transfinite closure. Their recorded declaration signatures were read.

Edge cases checked before the final statement:

- Empty S: there are no tensor summands or supported generators. The family category
  has one object and one arrow; all coordinatewise conditions and normalization
  equations are vacuous. Products and coproducts in V remain the ordinary empty
  ones. No `Nonempty S` is used.
- Singleton S: exactly one convolution summand and one internal-hom product recover
  the base cartesian tensor and exponential; both unitor orientations agree.
- An initial or terminal entry is allowed. Off-diagonal unit entries are initial,
  so their product summands vanish because the base is cartesian closed.
- Empty I or J is allowed. `generators` quantifies over every base generating family,
  not just a chosen or nonempty one. Both trivial-input cases, including both inputs
  trivial, are retained by the disjunction in the pushout-product axioms.
- The associator keeps intermediate vertices r,q in the same order: its source
  factors are `(P(q,t) × Q(r,q)) × T(s,r)` and its target factors are
  `P(q,t) × (Q(r,q) × T(s,r))`. No graph-factor interchange is imposed.

Searches executed for this delivery (2026-10-17 UTC):

- `msearch.py ... leanfinder "Matrix convolution on enriched graphs is a biclosed monoidal model category"`:
  eight hits, chiefly `MonoidalClosed.enrichedCategorySelf`, `EnrichedCat` and
  enriched-category operations; none states this graph model construction.
- `msearch.py ... loogle "CategoryTheory.MonoidalCategory, HomotopicalAlgebra.ModelCategory"`:
  zero hits.
- `msearch.py ... leansearch "Matrix convolution monoidal structure on families in a cartesian closed model category"`:
  eight hits for Day convolution and morphism convolution, including
  `DayConvolution.convolution`; none is the fixed-vertex matrix model theorem.
- `msearch.py ... grep "matrix|convolution|monoid.?axiom" CategoryTheory/Monoidal`:
  25 hits, mostly Day convolution. Read its interface: it is convolution of functors
  along a monoidal category's tensor, not this supported matrix model structure.
- Read `Mathlib.CategoryTheory.Pi.Monoidal`: its tensor is pointwise and cannot be
  reused as the matrix tensor.
- `rg` for `matrixConvolution|cartesianMatrixModel|lem-coef-cartesian-matrix-model`
  over upstream `WeilConjectures`, the shared `lean/Sheaf`, and
  `dag/lean_names_upstream.json` found no existing declaration. Broader graph/matrix/
  monoid-axiom searches found the already recorded nonsymmetric-monoid definition
  and unrelated graph constructions, which were inspected or excluded by topic. A further single-coordinate search found `CategoryTheory.GradedObject.single` in `Mathlib.CategoryTheory.GradedObject.Single`; read its full definition and reused it in `matrixSupportedArrow` rather than rebuilding the initial extension.

No source-based node correction, disputed statement, new definition node or
unusable-dependency repair was required. The final module uses only real data
constructions and one theorem ending in `sorry`; the proof docstring records all
twelve DAG steps with their named dependencies.

## Second reading by Q13

This is a separate second pass in the same worker session. The dispatcher explicitly
forbids starting another agent; the maintainer's independent review follows delivery.
It is not represented here as a review by another worker.

Re-read the complete node, source formulas and final module. This second pass found
and repaired deficiencies in the initial draft: arbitrary I,J had to yield graph
(not merely base) generators; objectwise Hom-set bijections needed actual natural
adjunctions; left properness and the graph pushout-product axiom needed explicit
conclusion fields; the internal-hom formulas should be definitions and functor
normalizations, not tautological equalities; and the convolution coherence needed
its summand formulas. All are present in `CartesianMatrixModelData` as matched above. The supported-arrow wrapper was subsequently changed to reuse Mathlib’s `GradedObject.single`; only the coordinate format is adapted.
Also repaired the signature record to stop before the proof delimiter, matching the
preflight parser. The S=empty and singleton cases, tensor factor order, coproduct
reindexing, both unitor orientations, arbitrary generating sets, and both weak-input
cases were checked again. No mismatch remains in this reading. No node statement or
dependency was changed to accommodate the Lean implementation.
