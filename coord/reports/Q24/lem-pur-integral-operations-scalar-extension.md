## Worker report

The module `Sheaf.Paper.IntegralOperationsScalarExtension` states
`WeilConjectures.integralOperationsScalarExtension`. Its sole theorem has proof
`sorry`. Its conclusion is `IntegralScalarOperations.Comparisons ...`:
an existential predicate of the three comparison families, their naturality and their
composition/identity diagrams. All helper abbreviations expand to the dependency
constructions; `site` is the explicit two-element selection of X and Y. The predicate
is an explicit existential/conjunction formula of witnesses and equations, not an
assumption on the input. The named clauses below are marked by matching comments in
the definition; data witnesses retain their binder names. No operation
or coefficient category is replaced by a new construction.

Hypotheses and clauses, one by one:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- A fixed algebraic closure of Q_l: `Ω`, `[Field Ω]`, `[Algebra ℚ_[l] Ω]`,
  `[IsAlgClosure ℚ_[l] Ω]`. The fields in every family range over the recorded
  `Padic.FiniteCoefficientFields l Ω`; its elements are exactly finite intermediate
  fields. The actual inclusion is `IntermediateField.inclusion h` for `h : E ≤ L`.
  All finite extensions and all towers, including equalities, are covered.
- Schemes X,Y and their morphism: `(X Y : Scheme.{u}) (f : X ⟶ Y)`.
  `_hX` and `_hY` say that l is a unit in every local ring. No Noetherian,
  separatedness, finite-type, dimension, finite-Tor, or perfectness condition is added.
- W in {X,Y}: `site X Y w`, with `w : Bool`; true is X, false is Y. This still
  covers both choices when X=Y and does not require the schemes to be distinct.
- The integral ambient category is `DerivedCategory (integralTowerModules l E.val W)`.
  This is the completed coefficient ring, not the constant integral coefficient ring.
- Scalar extension is exactly `integralScalarExtension` for the inclusion, with its
  published K-flat strict quotient-tower/Roos construction. The package's
  `preserves_complete` and `preserves_constructible` record the stipulated domain and
  codomain conditions. `constructible` expands to `sfIntegralConstructible`, which
  includes derived completeness, each positive constructible reduction and a single
  uniform finite cohomological interval. No auxiliary finite-field datum is required.
- K in D^b_c(Y,O_E): the `K` and `hK` arguments of `pullback`. Its isomorphism is
  `(extend h X).obj ((integralDerivedPullback ...).obj K) ≅
  (integralDerivedPullback ...).obj ((extend h Y).obj K)`, exactly the first display.
- M,N in D^b_c(W,O_E): the `M,N,hM,hN` arguments of `tensor` and `hom`.
  `tensor` uses `integralCompletedTensor`, on the left before scalar extension and on
  the right after extending each argument. `hom` uses `integralDerivedInternalHom`,
  with its first argument in the opposite category, in exactly the same way.
- The parenthetical completeness of internal Hom is `hom_complete`. It does not
  assert constructibility of that Hom or require its constructibility as a hypothesis.
- Naturality in every variable is `pullback_naturality`, `tensor_naturality` and
  `hom_naturality`. In the last clause the first-variable arrow is M'→M and enters
  the functor as `a.op`; the second-variable arrow is N→N'. The statements range over
  every ambient morphism between constructible objects, since the category is full.
- For E⊆L⊆F, the three diagrams are `pullback_comp`, `tensor_comp`, `hom_comp`.
  `scalarComp` has exactly the direction `(K⊗O_L)⊗O_F → K⊗O_F` in the node.
  The Hom diagram uses the inverse first-variable associator and forward second-variable
  associator, so both sides have the same source and target.
- The associators in those diagrams are fixed, rather than arbitrary existential
  isomorphisms: `completion_normalization` specifies the ambient ordinary-to-completed
  comparison on every good K-flat representative using the existing
  `integralScalarCompletionChain` and `integralScalarExtensionComparison`.
  `scalarComp_normalization` is its square with the existing
  `integralOrdinaryDerivedScalarComp`, whose pure-tensor rule is multiplication.
  `completion_isIso` covers all complete objects, including the nonconstructible Hom
  and outputs to which the scalar associator is applied. These are witness
  characterizations for the canonical scalar identifications used in the node's diagrams;
  they impose no extra input hypothesis and supply no arbitrary map.
- L=E is included by `le_refl E`, not excluded by strict inclusion. `scalarUnit` is the
  completion augmentation, fixed by `scalarUnit_normalization` using the published
  multiplication unit and the normalized completion map. `pullback_unit`, `tensor_unit`
  and `hom_unit` state that the comparison is identity after this identification.
  The Hom unit equation is written without an arbitrary inverse: precompose with
  Hom(η_M,id) and obtain Hom(id,η_N). Since η_M and η_N are isomorphisms on the
  complete inputs, this is exactly the usual identity diagram. The other unit diagrams
  also imply invertibility of the completion unit on their complete operation outputs.

Dependency declarations read and used:

- `Sheaf.Paper.IntegralDerivedOperations`: `integralDerivedPullback`,
  `integralCompletedTensor`, `integralDerivedInternalHom`, with their comparison
  definitions and complete docstrings. The first two use strict compatible reductions;
  the third is the ambient K-injective derived internal Hom.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and its full
  subcategory; its recorded repair avoids an auxiliary finite-field restriction.
  Its import supplies `IsSfDerivedComplete` from `SfDerivedComplete`.
- `Sheaf.Paper.IntegralScalarExtension`: `integralScalarExtension`,
  `integralScalarExtensionComparison`, `integralOrdinaryDerivedScalar`,
  `integralOrdinaryScalar`, the completed-ring map and exact ordinary tensor model.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: the inherited coefficient
  definitions and `Padic.finite_coefficientExtensionRing`; the full underlying
  `CoefficientExtension` module was read for the ring, uniformizer and quotients.
- `def-weil-scheme-morphism-properties` is the recorded convention node and has no
  declaration. Its scheme and morphism notation is used literally.
- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`: `Padic.FiniteCoefficientFields`
  and `Padic.finiteCoefficientField_finiteDimensional`.
- `Sheaf.Paper.IntegralScalarExtensionConstructible`: the already published
  `integralScalarCompletionChain` and its two-coordinate normalization; no finite-field
  argument occurs in that helper. Only the helper is used, not a restricted category.
- `Sheaf.Paper.ScalarExtensionComposition`: `integralOrdinaryDerivedScalarComp` and
  `integralOrdinaryDerivedScalarUnit`, read together with their pure-tensor defining
  theorems. They too have no finite-field or characteristic restriction.

The last three already-landed nodes were added to stmt_deps because they provide
respectively the index of actual finite coefficient fields and the canonical maps
needed to state the composition and identity clauses. A full dependency traversal
found no return path from any of these nodes to this item. No other DAG node is
restated, no dependency module is changed, and no new definition node is needed.
The proof-only imports follow every stated proof dependency, including its recorded
current module or exact Mathlib leaf. The theorem docstring gives all nine proof
steps with their dependencies, including the strict cone normalization, cofinal
compression and internal Hom argument; none is proved here.

Edge cases checked before writing: equal coefficient fields and repeated fields in
three-stage towers; the identity inclusion versus a genuinely larger field; ramified
extensions (the comparison is completed, not an equality of same-exponent quotients);
zero complexes and zero morphisms; empty schemes; X=Y and identity scheme morphisms;
negative cohomological degrees; nonperfect constructible inputs and nonconstructible
internal Hom outputs. No positive-level reduction is omitted: the dependencies use
n+1 for every n:ℕ. The ambient universe u is common to the algebraic closure and the
schemes, allowing any initial sizes by enlarging u; site object and morphism universes
remain u+1 and u inside the imported definitions, and are never identified.

Searches (2026-10-16):

- `msearch.py ... leanfinder "Integral derived pullback completed tensor and internal
  Hom commute naturally with finite extension of l-adic coefficient fields"`: eight
  unrelated results (BDeRhamPlus, scheme tensor-product points, condensed Hom points,
  adic-completion tensor). None states these comparisons.
- `msearch.py ... loogle "NatIso, Functor.prod, Functor.op"`: zero hits; service reports
  NatIso is an unknown identifier in that query. Source inspection was used for the API.
- `msearch.py ... grep "scalar.*[Tt]ensor|[Tt]ensor.*[Ss]calar|[Ss]calar.*[Hh]om"
  CategoryTheory`: three scalarRestriction_hom lines in Monoidal/Mod, no derived
  integral scalar comparison.
- `rg` of the item id and integral scalar/pullback/tensor/Hom comparison names in
  slopmaster2/WeilConjectures and lean/Sheaf: no statement of this item. Searches of
  scalar composition/comparison modules found the helpers above, which are reused.
- Read Mathlib CategoryTheory/Products/Basic for `Prod.mkHom`; product arrows are
  constructed explicitly, avoiding unresolved object-pair inference.

The initial dependent-record presentation elaborated, but its module-output pass
exceeded the default timeout. It was replaced by the equivalent explicit existential
predicate, avoiding generated recursors/projections for the large dependent record;
no mathematical clause or input changed.

No statement correction and no STATEMENT-DISPUTED finding. No direct repository
write or Git command was performed. Compilation and delivery bookkeeping use only
the prescribed wrappers. Validation: the final existential-predicate file passed both scompile.py checks
without errors or warnings (11.9 s for the sandbox check, 13.5 s at its library
module path). The required deliver2.py --no-push dry run printed OK: compilation and preflight
passed except for the intentionally pending second reading. Nothing was pushed.
The second reading is left to the assigned second reader.

## Second reading by Q24

Independent second reading, 2026-10-16. I opened the item's JSON, its complete
Lean module, the cited blueprint definition's integral/common-stage paragraph,
and the declarations of every statement dependency. The source is a blueprint
construction, explicitly not a standalone Stacks scalar-extension theorem.
The blueprint assumes a prime, finite coefficient extensions, the small pro-etale
sites and schemes with ell invertible; it does not impose geometric finiteness,
perfectness or finite Tor dimension. I also read Stacks sites-cohomology.tex,
lemma-pullback-tensor-product (07A4) and lemma-restriction-RHom-to-U (08JB), and
sites-modules.tex, lemma-internal-hom-adjoint-tensor (03EO). Their hypotheses
are ringed topoi/sites, not Noetherian schemes or perfect complexes.

Here is my inventory of the node, matched against the Lean with a verdict for
each object, hypothesis and conclusion. Names of clauses below refer to the
comments inside `IntegralScalarOperations.Comparisons`, not to projections of
a nonexistent record.

1. Prime ell: `(l : ℕ) [Fact l.Prime]`. Verdict: exact; includes ell = 2.
2. Fixed algebraic closure: `Ω`, `[Field Ω]`, `[Algebra ℚ_[l] Ω]`,
   `[IsAlgClosure ℚ_[l] Ω]`. Verdict: exact, with no norm or valuation supplied
   as extra input. The coefficient dependency constructs the spectral absolute
   value, valuation ring, uniformizer and quotient rings.
3. All finite extensions inside that closure and their inclusions:
   `Padic.FiniteCoefficientFields l Ω`, `h : E ≤ L` and
   `IntermediateField.inclusion h`. I opened its subtype definition and the
   finite-dimensional instance. Verdict: exact; E and L are finite over Q_l,
   and h is actual inclusion, not an arbitrary ring homomorphism or strict inclusion.
4. Schemes and morphism: `X Y : AlgebraicGeometry.Scheme.{u}` and `f : X ⟶ Y`.
   Verdict: exact; the scheme-properties dependency is a convention node, so
   there is no additional structure to instantiate.
5. Ell invertible on both schemes: `_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x)`
   and the analogous `_hY`. Verdict: precisely local invertibility everywhere,
   equivalent to invertibility of the integer section. No field of definition,
   finite type, separatedness, Noetherian or dimension hypothesis was added.
6. W in {X,Y}: `site X Y w` for `w : Bool`, false selecting Y and true X.
   Verdict: exact finite choice, including X = Y. It creates no independent site.
7. Ambient integral category: `Ambient` expands to
   `DerivedCategory (integralTowerModules.{u,u} l E.val W)`. I checked the
   integral operations and completed coefficients modules: the coefficient
   ring is the limit of constant positive quotient sheaves, with its recorded
   commutative structure. Verdict: the completed ring, exactly as required.
8. Scalar extension: `extend` is the recorded `integralScalarExtension` for h.
   I read its K-flat localization and representative comparison; it is the
   strict quotient-tower/Roos functor, not ordinary scalar extension substituted
   for completion. `preserves_complete` and `preserves_constructible` express
   the domain/codomain assertions of the node. Verdict: exact. These are
   conclusions inside the existential predicate, not extra hypotheses.
9. Constructible inputs: `constructible` expands to `sfIntegralConstructible`.
   Opening that definition shows derived completeness, every positive intrinsic
   constructible reduction and one common interval [a,b] with a ≤ b. Verdict:
   exactly the detailed integral-category node; no auxiliary finite-field datum
   or perfectness requirement. Full-subcategory morphisms are ambient morphisms.
10. Pullback comparison: `pullback E L h K hK` has source extension on X of
    `integralDerivedPullback l E.val f` applied to K, and target pullback over L
    of extension on Y of K. `K : Ambient ... E Y` and `hK` give precisely
    K in D^b_c(Y,O_E). Verdict: first display, correct variance and coefficient rings.
11. Tensor comparison: `tensor E L h w M N hM hN` extends
    `integralCompletedTensor` over E on the left and applies completed tensor
    over L to the two extended inputs on the right. Verdict: second display
    with both inputs constructible, not an ordinary tensor substituted for it.
12. Hom comparison: `hom E L h w M N hM hN` extends the ambient
    `integralDerivedInternalHom` over E and compares with that over L on
    `(op (extend M), extend N)`. `hom_complete` asserts completeness of its
    source Hom. Verdict: third display and its parenthetical assertion;
    constructibility of Hom is neither required nor claimed.
13. Naturality: `pullback_naturality` covers every K→K'; `tensor_naturality`
    covers all M→M', N→N'; `hom_naturality` covers all M'→M, N→N' using `a.op`.
    Verdict: all variables and the contravariant Hom slot are correct.
14. Coefficient towers: `scalarComp E L F h k w` points from successive extension
    to direct extension. The three `*_comp` equations compare both complete
    routes. In `hom_comp`, the first-slot associator is inverse and the second
    is forward. Verdict: exactly the stipulated three composition diagrams.
    The auxiliary completion and scalar associator are fixed by
    `completion_normalization` and `scalarComp_normalization`, not merely by
    existence of an arbitrary isomorphism. I opened
    `integralScalarCompletionChain_existsUnique`: the quotient section formula
    and zero shifted cone coordinate determine the map. I opened
    `integralOrdinaryScalarComp_existsUnique` and the induced derived iso:
    their rule is c⊗(b⊗x) ↦ c*j(b)⊗x. Neither helper carries a finite-field
    datum. Normalizing on all good representatives determines the ambient
    comparison; invertibility on complete objects also covers the Hom output.
    The ambient extension of these normalizations introduces no input condition.
15. Identity extension: `le_refl E` is permitted throughout. `scalarUnit_normalization`
    fixes its map as the ordinary inverse unit followed by canonical completion.
    `completion_isIso` makes it invertible on complete inputs. The equations
    `pullback_unit`, `tensor_unit`, `hom_unit` therefore say identity after this
    identification. In the Hom equation, precomposition by Hom(η_M,id) supplies
    the contravariant inverse implicitly; it is invertible since M is complete.
    Verdict: exactly the usual identity clause, not literal equality of a Roos
    functor with the identity. No arbitrary scalar-unit witness is allowed.

Edge cases: E=L, repeated fields in a tower and the identity scheme morphism are
included. Ramification is handled by the completed tower, without identifying
same-exponent quotients. Empty schemes make the local-unit hypotheses vacuous
as they should. Zero complexes and zero morphisms are allowed without a nonzero
or nonempty assumption. Every positive finite level occurs as n+1 (including
the first at n=0); exponent zero is not a missing coefficient level. Cohomology
is indexed by all integers. The theorem does not restrict the characteristic
beyond ell being a unit, nor the scheme's geometry. All universes and variables
are explicitly bound. The imported small site retains object universe u+1 and
morphism universe u; none is identified with the other. The closure and schemes
use a common ambient size, as do the recorded intrinsic constructibility and
scalar-extension interfaces; their initial sizes can be accommodated by a
common larger universe. There is no quantification over a smaller independent
universe of test objects that could render a condition vacuous.

Independent searches:

- `msearch.py ... leanfinder "Finite free coefficient base change commutes with
  derived sheaf internal Hom and completed tensor on the proetale site"` returned
  eight results on light condensed internal Hom, free sheaves and free pullback.
  None states the integral completed coefficient comparisons of this item.
- `msearch.py ... loogle "Functor, NatIso"` returned no hits and reported
  `NatIso` unknown. I did not treat the failed identifier resolution as proof
  of absence; I used direct source searches as well.
- `msearch.py ... grep "baseChange.*[Hh]om|[Hh]om.*baseChange|scalar.*[Cc]ompar"
  CategoryTheory` found four unrelated Kan-extension/morphism-property lines.
- Direct `rg` searches for internal-Hom/base-change and scalar comparison terms
  in Mathlib CategoryTheory and Algebra/Homology, upstream WeilConjectures and
  this project's lean/Sheaf found no exact statement. Focused searches in the
  upstream SixFunctors/CategoryTheory and project Paper modules led to
  IntegralHomReductionComparison (reduction to a finite quotient),
  LisseTensorScalarExtension (underived finite lisse sheaves on the etale site),
  and FieldDerivedScalarTower (ordinary field-module derived categories).
  I opened their relevant declarations: none has this item's completed
  pro-etale categories and three operations. The existing scalar/completion
  helpers in ScalarExtensionComposition and IntegralScalarExtensionConstructible
  are already reused. An exact-name/id search in dag/lean_names_upstream.json,
  upstream WeilConjectures and lean/Sheaf found no existing item declaration.

No mismatch found; I changed no Lean declaration or node field. Only this second
reading was appended. The helper abbreviations are transparent references to
existing notions; `site` and `Comparisons` are explicit finite selection and a
fully written existential/equational predicate. They contain no postponed data,
private construction or new independent mathematical notion requiring a node.
There are no new nodes or dependency modules in this delivery, and no statement
correction, so no correction/citer audit is needed. The three additional statement
dependencies are already recorded landed interfaces used by the normalization.
Every declaration has its source/blueprint docstring; the sole theorem has `sorry`
as its entire proof, with the nine proof steps in its docstring. I checked that
`lean.statement` is verbatim the theorem signature and no Lean line exceeds 100
characters. No mathematical result was proved during the reading.

Second-reader validation: the sole delivered Lean module passed scompile.py in
both sandbox and library-path checks (17.0 s and 16.3 s), with no diagnostics.
