## Worker report

Item: def-sfb-adequately-affine-morphism. The module
`Sheaf.AlgebraicGeometry.AdequatelyAffineMorphism` defines
`CategoryTheory.IsAdequatelyAffineMorphism`, together with the smooth scheme-test,
test-arrow, compatible-section and restriction helpers used to expand its definition.
All data is explicit. There are no theorems and no `sorry`s in this delivery.
The node statement is unchanged. Its `stmt_deps` gains the already landed
`def-sfb-moduli-chart-normalization`, solely for its canonical
`CategoryTheory.moduliTwoFiberMapRight` helper. No dependency record is repaired,
and no new independent definition node is needed: every helper is a construction
explicitly described in this item's own statement.

Source read: Alper, arXiv:1005.2398v3, §2 and Definitions 3.4.1 and 4.1.1,
printed pp. 14 and 16, https://arxiv.org/pdf/1005.2398v3 . The local PDF is marked
WANTED in the inherited source, so the primary online source was read. The two
definitions agree with the node's smooth-test power-lifting formulation; it does
not require a uniform exponent over all sections, all cover members or all algebras.

Clause-by-clause rendering:

- The field is `{k : Type u} [Field k]`. Both stacks are based categories over
  `Over (Spec (.of k))`, with independent endpoint levels `v₁ w₁` and `v₂ w₂`.
  The explicit arguments `hU : IsAlgebraicModuliStack U` and
  `_hV : IsAlgebraicModuliStack V` express the stated ambient algebraicity.
  The latter is a domain-of-definition condition, not an additional property
  claimed inside adequate affineness. Fibredness is the recorded `hU.1.1`.
- The universe/skeleton convention is implemented by explicit universe binders,
  the existing size-polymorphic based categories, and `I : Type u` for covering
  families of schemes in `Scheme.{u}`. The qc predicate uses its common ambient
  test bound `max u v₁ v₂` and `max (u+1) w₁ w₂`, by taking the optional extra
  enlargements to be zero. It does not equate the endpoint or site universes.
  Algebras use exactly the ambient ring universe of the recorded
  `ModuliAlgebraSheaf` interface; there is no finite-generation restriction.
- A smooth test is `T : Over S` and a based functor
  `t : BasedFunctor (discreteModuli (yoneda.obj T)) V` with
  `IsSmoothModuliSchemeTest t`. That predicate tests every scheme map `W → V`,
  asks for the actual algebraic-space presentation by `HasSpaceBaseChange`,
  and applies the recorded `SpaceMapIsSmooth` to its projection. The latter
  tests Mathlib `Smooth` on every étale scheme chart. Neither the test map nor
  its base-change projection is required to be surjective.
- The node's test-site arrows are `ModuliSchemeTestArrow t t'`: the field
  `schemeMap : T ⟶ T'` is the scheme map over S, and `comparison` is the based
  natural isomorphism from its composite with `t'` to `t`. A based natural
  isomorphism has components over identity base maps, exactly the recorded
  2-morphism notion. Restricting endpoints to smooth tests gives precisely
  the arrows described for Lis-ét. No isomorphism classes of objects replace
  the fibred categories.
- `moduliSchemeTestSections f A t` is Mathlib's `RingCat.sectionsSubring`
  for `(moduliTwoFiberFst f t).toFunctor.op ⋙ A.right.obj`, after forgetting
  commutativity. Thus a section is a family on ALL objects of the actual
  `moduliTwoFiberProduct f t`, compatible along ALL of its arrows. This is
  Γ(U ×_V T, A|), with literal precomposition by the canonical first projection,
  as prescribed by the dependency's global-section convention. Ring operations
  are pointwise and each value remains a commutative ring. The helper keeps
  the section subring rather than choosing any abstract isomorphic ring.
- `moduliSchemeTestRestriction f A a s` restricts that family by the recorded
  `moduliTwoFiberMapRight f ... a.comparison`; its first component on U is
  unchanged and its right component is the specified scheme-test map.
  The compatibility proof is the original family's compatibility applied to
  this functor's actual arrow. Both the scheme map and its specified 2-isomorphism
  are retained. These definitions expand the node's direct-image formula;
  no arbitrary direct-image map is assumed or chosen.
- Universal adequacy is `IsUniversallyAdequateModuliDirectImage f q`.
  It quantifies over EVERY `T`, EVERY `t`, and EVERY compatible target section `s`
  whenever the test is smooth. Its covering family is explicitly
  `I`, `W : I → Over S`, `j : ∀ i, W i ⟶ T`, with
  `∀ i, Etale (j i).left` and the joint-surjectivity clause
  `∀ x, ∃ i y, (j i).left y = x`. These are exactly the node's étale coverings.
  The test on each member is the actual composite
  `(discreteModuliMap (yoneda.map (j i))).comp t`. Such a composite is smooth
  because an étale scheme map followed by a smooth stack map is smooth;
  the quantified power-lifting formula does not add an extra smoothness demand.
- For EACH cover member the formula supplies `N : ℕ`, `0 < N`, and a compatible
  source section `r`. The equation at EVERY object `x` applies
  `q.right.hom.app (op x.obj.left)` to `r.1 (op x)` and equates it to the N-th
  power of `moduliSchemeTestRestriction f B ⟨j i, Iso.refl _⟩ s` at `x`.
  The reflexive comparison is canonical because the chosen source test IS
  that exact composite. It does not restrict general test-site arrows.
  Equality at every object is equality of compatible section families, so
  this is precisely the induced f_*q power-lifting equation.
- Adequate affineness itself is the conjunction of the recorded
  `IsQuasiCompactAlgebraicModuliMap f`, `IsQuasiSeparatedAlgebraicModuliMap f`,
  and the universal adequacy condition for every `A B` and every `q : A ⟶ B`
  with `IsQuasicoherentModuliAlgebra A`, `IsQuasicoherentModuliAlgebra B`, and
  `IsSurjectiveModuliAlgebra q`. These are the actual recorded algebra-sheaf,
  quasi-coherence and locally-surjective predicates, not pointwise surjectivity.

The lisse-étale site is expanded through its smooth tests, test arrows and étale
coverings; the definition does not need a second bundled sheaf category or
sheafification of the direct image. In particular its section formula is on the
actual 2-fibre product, so it uses neither the downstream adequate-product theorem
nor an arbitrary surrogate map. The recorded dependency `moduliDirectImage` has an
algebraic-SPACE target and an étale site. It cannot be applied to this item's
algebraic-STACK target and smooth tests. The helpers here supply exactly the
additional formula owned by the present node, while reusing its underlying algebra
and global-section convention. They do not replace that dependency interface.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (the dependency's Mathlib match).
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `IsAlgebraicModuliStack`, `SpaceMapIsSmooth`, via its given
  `HasSpaceBaseChange` presentations. Full signatures and docstrings were read.
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`:
  `IsQuasiCompactAlgebraicModuliMap`, `IsQuasiSeparatedAlgebraicModuliMap`.
  Their actual atlas and diagonal test definitions were read; no DM assumption
  or finite-type condition is imposed.
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`:
  `ModuliAlgebraSheaf`, `IsQuasicoherentModuliAlgebra`,
  `IsSurjectiveModuliAlgebra`, and its compatible-family global-section convention
  (`moduliGlobalSections`, `moduliGlobalSectionsRing`). The algebra value and
  operations are always those of `A.right.obj`; no algebra is recreated.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `BasedFunctor`, `IsFibredInGroupoids`, `discreteModuli`, `discreteModuliMap`,
  `moduliTwoFiberProduct`, `moduliTwoFiberFst`, `HasSpaceBaseChange`.
  The based-natural-isomorphism interface from Mathlib
  `CategoryTheory.FiberedCategory.BasedCategory` is the same 2-isomorphism notion.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: recorded generic site convention.
  Its module is imported; this predicate expands the concrete cover families.
- `def-weil-size-convention` is explicitly a convention record with no declaration;
  it is implemented by the stated universes rather than a new proposition.
- The added, already landed `def-sfb-moduli-chart-normalization` supplies
  `Sheaf.AlgebraicGeometry.ModuliChartNormalization`:
  `CategoryTheory.moduliTwoFiberMapRight`. Its full source signature and docstring
  were read. Only its canonical base-change helper is used, not the normalization
  predicate or a normalization theorem.
- `Mathlib.Algebra.Category.Ring.Limits`: `RingCat.sectionsSubring` is the existing
  definition of compatible ring sections used in the recorded algebra dependency.

Edge cases checked semantically against the definitions:

- Empty scheme test and empty cover: `I` has no Nonempty assumption. An empty family
  can cover only an empty scheme, because joint surjectivity is explicit.
- Nonempty test: an empty family cannot witness the cover condition.
- Zero section: exponent one and zero source section are allowed. No nonzero
  section or nontrivial algebra hypothesis was introduced; zero rings are allowed.
- Zero exponent: excluded by `0 < N`, as required. Exponents may vary with the
  test, section and cover member; no uniform bound was silently imposed.
- Arbitrary infinite algebras and non-Noetherian field extensions: no finite type,
  finite presentation, dimension or characteristic condition occurs in the formula.
- Identity/affine morphisms and empty source: the same canonical pullback section
  formula applies. There is no requirement that test maps be atlases or surjective.
- Independent stack universes: the successful compile keeps all four endpoint
  levels; the base-change section type is inferred without equating universes.
  Cover families are small as in the node's skeleton convention. Larger presentations
  of a scheme cover can be refined by choosing a cover member over each point,
  so the `Type u` index bound loses no local-lifting condition.

Searches performed on 2026-10-24 (using the prescribed msearch.py wrapper):

- leanfinder: "An adequately affine morphism of algebraic stacks is quasi compact
  quasi separated and sends all surjections of quasi coherent algebras to universally
  adequate maps with etale local positive power lifting". Eight hits, all scheme
  affine-target/morphism predicates; no matching stack definition.
- loogle: `"adequate"`. Zero hits.
- grep: `adequat|lis.?etale|SmoothStackTest`, subdirectory `AlgebraicGeometry`.
  Zero Mathlib hits.
- leansearch: "Adequately affine morphism of algebraic stacks universally adequate
  pushforward". Eight hits, including scheme module pushforward and scheme affineness;
  no matching definition.
- rg in project `lean/WeilConjectures` and `lean/Sheaf` for adequate-affine and
  universally-adequate spellings, and `rg -n def-sfb-adequately-affine-morphism` in
  `lean/WeilConjectures`: no existing exact definition. The relevant nearby hits
  were PGL reductivity, affine quotient theorem docstrings, and a polynomial
  ring-level adequacy lemma, none the current predicate.
- rg over Mathlib and both project roots for all final six declaration names:
  no existing declaration. The canonical map search found the already landed
  `moduliTwoFiberMapRight`; its node and declaration were read and reused.

Validation: prescribed scompile.py compiles both the sandbox check and the actual
module path with no errors or warnings (2026-10-24). `set_option autoImplicit false`
is enabled; every variable and universe is explicit. No local instance, notation,
private definition, axiom or proof obligation is introduced. No statement fault or
STATEMENT-DISPUTED finding remains.

## Second reading by O2

The dispatched worker reread the node and final file after compilation; the
maintainer's independent review remains the separate review required by the brief.
This is not a claim that another agent was started. The reread checked the field,
both algebraicity assumptions, the independent universes, every qcqs conjunct,
both quasi-coherence hypotheses, local sheaf surjectivity, all smooth tests,
all compatible sections, the jointly surjective étale family, positivity and
per-member variability of the exponent, and the componentwise canonical equation.
An early draft tested smoothness over the base field rather than the projection
of a stack base change; that mismatch was removed before the final compile.
The reread also checked that test arrows retain their 2-isomorphism, that restriction
uses `moduliTwoFiberMapRight` and that the section-ring formula uses the full
2-fibre product rather than a chosen atlas. There are no new nodes or dependency
repairs to read. The added dependency is solely for its existing canonical helper.
