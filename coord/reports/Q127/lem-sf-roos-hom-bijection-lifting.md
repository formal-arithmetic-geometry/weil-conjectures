## Worker report

Item: lem-sf-roos-hom-bijection-lifting. The new module
`Sheaf.CategoryTheory.Triangulated.RoosHomBijectionLifting` states
`CategoryTheory.Functor.map_bijective_of_roos`, with proof `sorry`.
It introduces no definitions, no new nodes, and no dependency repairs.
The node is unchanged except for `lean`.

Source read: the whole integral-stage paragraph of
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/`
`sk-prop-sf-closed-unit/prop-sf-closed-unit-all-stages.proof.md`.
It compares the two product terms in the two Roos triangles, then applies
Hom exactness and the five lemma to the map induced by the exact functor.
The declaration docstring carries all five proof steps of the node, including
commutativity of the square containing the transported connecting arrow.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Locally small categories C and D: `{C : Type u₁} [Category.{v₁} C]`
  and `{D : Type u₂} [Category.{v₂} D]`. All four universes are explicit
  and independent. No smallness relation or equality is imposed.
- Pretriangulated structures: each category has `HasZeroObject`, `HasShift … ℤ`,
  `Preadditive`, additive shifts for every integer, and `Pretriangulated`.
  This is exactly the dependency's Mathlib encoding of TR1--TR3; no octahedral
  axiom (`CategoryTheory.IsTriangulated C`) is assumed.
- Countable products: `[HasCountableProducts C] [HasCountableProducts D]`.
  They supply the products of T and of the image family.
- The additive exact functor with specified shift comparison is
  `(F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]`, as in the dependency's
  `mathlib_match.how`. The latter supplies `F.Additive`; a second additive
  assumption is unnecessary. The actual chosen comparisons are
  `F.commShiftIso m`, not arbitrary isomorphisms chosen during a proof.
- Objects P,Q: `(P Q : C)`.
- Tower: `(T : ℕ → C) (t : ∀ n : ℕ, T (n + 1) ⟶ T n)`.
  Term `T n` is the paper's term numbered n+1. This is exactly the transition
  data accepted by the recorded `Functor.ofOpSequence`; the dependency node
  explicitly gives this family/transition presentation as equivalent to the
  functor presentation. We do not duplicate its definition.
- B and its shift: B is the existing product `∏ᶜ T`.
  The existing `towerProductShift t` is `Pi.lift (fun n ↦ Pi.π T (n+1) ≫ t n)`;
  `towerTransitionEndomorphism t` is exactly `𝟙 _ - towerProductShift t`.
- Specified augmentation and connecting arrow: `(q : Q ⟶ ∏ᶜ T)` and
  `(d : ∏ᶜ T ⟶ Q⟦(1 : ℤ)⟧)`, with
  `(hQ : IsDerivedLimitTriangle t Q q d)`. This existing predicate says
  `Triangle.mk q (towerTransitionEndomorphism t) d ∈ distTriang C`.
  Thus the actual triangle, not just existence of some reconstruction of Q,
  is retained.
- Canonical product comparison: `[IsIso (piComparison F T)]`.
  Mathlib defines `piComparison F T` as `Pi.lift (fun n ↦ F.map (Pi.π T n))`;
  `piComparison_comp_π` gives exactly the node's projection identity.
  This assumes preservation of this product only, not all products by F.
- The D-triangle is the transported image of this specific triangle, rather
  than independent input data. The docstring spells out its augmentation
  `F.map q ≫ piComparison F T` and connecting arrow
  `inv (piComparison F T) ≫ F.map d ≫ (F.commShiftIso 1).hom.app Q`.
  `F.mapTriangle` uses precisely `F.map d` followed by that shift comparison;
  transport uses the canonical product comparison, whose invertibility is
  assumed. The middle arrow becomes the image tower's `1-s` by projections
  and additivity. Since the node introduces no independent D-triangle, the
  theorem likewise has no free target triangle or independently chosen boundary.
- Every n and every integer m: `hT : ∀ (n : ℕ) (m : ℤ), …`.
  Its function is literally
  `fun (a : P⟦m⟧ ⟶ T n) ↦ (F.commShiftIso m).inv.app P ≫ F.map a`.
  The inverse comparison changes source from `(F.obj P)⟦m⟧` to `F.obj (P⟦m⟧)`;
  hence the codomain is exactly Hom_D((FP)[m],F(T n)).
  The predicate is `Function.Bijective`, with neither injectivity nor
  surjectivity omitted.
- The conclusion is `Function.Bijective (fun (a : P ⟶ Q) ↦ F.map a)`.
  It is about the specified functor map on Hom, not an existential equivalence.
  No vanishing, ML, or boundedness condition appears.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`:
  `CategoryTheory.Pretriangulated`, `Pretriangulated.distinguishedTriangles`;
  the proof plan uses `Pretriangulated.Triangle.coyoneda_exact₂`,
  `coyoneda_exact₁`, and triangle rotation, as recorded for
  lem-weil-pbc-hom-into-triangle-exact.
- `Mathlib.CategoryTheory.Triangulated.Functor`:
  `Functor.CommShift` (through its shift import), `Functor.commShiftIso`,
  `Functor.IsTriangulated`, its additive instance, and `Functor.mapTriangle`.
- `Mathlib.CategoryTheory.Functor.OfSequence`:
  `Functor.ofOpSequence` and the family/transition interface described above.
- `Mathlib.CategoryTheory.Limits.Shapes.Products`:
  `piObj`, `Pi.π`, `Pi.lift`, `Pi.map`, and `piComparison`.
- `Mathlib.CategoryTheory.Limits.Shapes.Countable`:
  `HasCountableProducts`, including its instance for any countable index type.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimitTriangle` (the node's recorded auxiliary
  declaration; read together with `IsDerivedLimit`). Its upstream import
  `WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism` provides
  the actual product shift and `1-s` construction.
- `Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four`:
  `CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono` is imported
  for the stated proof dependency lem-weil-pbc-five-lemma.

The statement dependencies are public imports. The two Hom-exactness/five-lemma
proof modules are plain imports. All variables are explicitly bound;
`set_option autoImplicit false` enforces this.

Edge cases checked before writing: the zero object P makes all Hom sets
singletons, consistently; the zero tower gives an isomorphism `1-s`, so the
Roos triangle forces Q to be zero. The constant identity tower is allowed;
there is no assumption killing the boundary. Nonzero boundaries and non-ML
towers are allowed. The indexing reparametrization ℕ -> positive integers is
a bijection and drops no term. All positive, zero, and negative shifts are
quantified; independent object and morphism universes remain unrestricted.
Countable products, rather than arbitrary products, suffice. No node fault or
STATEMENT-DISPUTED issue was found.

Searches for an existing declaration (2026-10-23):

1. msearch.py leanfinder, query:
   "An exact functor preserving the product in a specified Roos triangle gives
   a bijection on Hom from P to the homotopy limit if it gives bijections on
   Hom from every shift of P to each tower term".
   Result: OK, 8 hits, including `Functor.map_distinguished_exact`,
   `map_distinguished_op_exact`, `IsHomological.exact`, and homology-sequence
   exactness. None states the tower-to-Roos Hom bijection criterion.
2. msearch.py loogle, query: `CategoryTheory.Functor.IsTriangulated`.
   Result: OK, 12 hits for the class, its instances, and preservation of
   distinguished triangles; no matching statement.
3. msearch.py grep, query:
   `Roos|homotopyLimit.*[Bb]ijective|[Bb]ijective.*homotopyLimit`,
   directory `CategoryTheory`. Result: OK, 0 hits.
4. msearch.py leansearch, query:
   "An exact functor gives a bijection on Hom into a Roos homotopy inverse
   limit if it preserves the tower product and gives bijections on Hom from
   all shifts into every tower term".
   Result: OK, 8 hits, including `exactFunctor`, `ExactFunctor.of`,
   `IsHomological.mk` and left/right exact functors; no match.
5. rg in both project roots for `IsDerivedLimitTriangle`,
   `map_bijective.*[Ll]imit`, `[Rr]oos.*[Bb]iject`, and `[Bb]iject.*[Rr]oos`.
   Hits give the shared derived-limit predicates and related Roos results,
   not this criterion. Broader Roos/Hom searches likewise found no duplicate.
   `grep -rn 'lem-sf-roos-hom-bijection-lifting' lean/WeilConjectures`
   returned no hits. A name-clash search for `map_bijective_of_roos` in
   Mathlib, WeilConjectures, and Sheaf returned no hits.

Validation: scompile.py compiled the delivered file both as sandbox and library
module on the server, with no errors or warnings reported (4.6 s and 1.3 s).
The proof remains `sorry`, as required by stage 2.

## Second reading by Q127

This is a same-worker rereading; the dispatcher brief assigns the independent
review to the maintainer and prohibits starting other agents. I reread the
node, dependency definitions, and completed signature. The crucial checks
were the inverse direction of the source shift comparison in hT, the actual
q and d bound in hQ, the canonical piComparison rather than arbitrary product
isomorphism, and the literal F.map conclusion. All match. The target triangle
is determined from these inputs; its boundary is explicitly documented as
the transported F.map d, so no extra compatibility hypothesis is needed.
No statement or signature changes were needed after this rereading.
