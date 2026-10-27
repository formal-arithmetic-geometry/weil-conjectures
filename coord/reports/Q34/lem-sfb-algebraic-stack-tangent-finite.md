## Worker report

The statement is `AlgebraicGeometry.StackDeformation.algebraicStack_tangent_finite` in
`Sheaf.AlgebraicGeometry.AlgebraicStackTangentFinite`. Its only proof is `sorry`.
The node statement and accepted proof split are unchanged. One definition node is added
for the marked stack deformation construction used in the statement.

Source read: `literature/stacks-project/artin.tex`, Tag 07X1
(`lemma-finite-dimension`, including the complete proof), and Tag 07T4
(`equation-predeformation-category`, the preceding object/morphism definition and
`equation-factor`). The affine Noetherian specialization and tangent-only conclusion
are exactly the assigned node. No source webpage was needed: its TeX is present locally.

Hypotheses and clauses, matched with the Lean:

- Commutative Noetherian R: `{R : Type u} [CommRing R] [IsNoetherianRing R]`.
  S is literally `Spec (.of R)`; every base category is `Over (Spec (.of R))`.
- Scheme sizes: explicit `universe u v w`; schemes and test rings have universe u,
  while the total stack has independent morphism/object universes v and w through
  `BasedCategory.{v,w}`. Increasing u includes any pair of base/residue rings.
- Algebraic stack: `F` and `hF : IsAlgebraicModuliStack F`, using Q18's exact
  definition, which includes the fibred-groupoid, descent, diagonal and atlas conditions.
- The given scheme atlas: `U : Over (Spec (.of R))`,
  `a : BasedFunctor (discreteModuli (yoneda.obj U)) F`, and
  `ha : IsSmoothModuliAtlas F U a`. This retains the representable algebraic-space
  base changes and their actual smooth surjective projections.
- The atlas structural morphism is locally finite type: `hU : LocallyOfFiniteType U.hom`.
- Finite-type field over R: `{k : Type u} [Field k] [Algebra R k]
  [Algebra.FiniteType R k]`.
- The S-point x: `x : Functor.Fiber F.p (affine (CommAlgCat.of R k))`.
  A stack point from the representable spectrum is equivalently its fibre object;
  a specified transport cleavage is unnecessary for the statement.
- The entire marked test category is `ArtinDeformation.TestCategory R k`.
  `Marked F x A` is a full subcategory of structured arrows from `x.val` to the
  inclusion of the fibre over Spec A, restricted by `IsHomLift` over the residue
  immersion. Thus objects retain the marking, and arrows lie over the identity and
  commute with it. Since F is fibred in groupoids, every arrow is cartesian; this
  says precisely that the reduction is identified with x. Reversing that marking
  isomorphism converts the arrow convention to the node's alpha: eta|k ≅ x.
- Pullback transport: `PullsBack` requires an actual arrow above Spec of the test
  morphism, with equality on the two markings. Every such arrow is cartesian under hF.
  This relation specifies pullback without choosing a new object from an existence theorem.
- Tangent set: `Tangent F x` is the quotient by marked isomorphism of `Marked` at
  the recorded `squareZeroTest k`, whose ring is k ⊕ k with square-zero ideal.
- Vector-space and finiteness conclusion: existential `AddCommGroup` and `Module k`
  structures on that exact quotient, followed by `FiniteDimensional k (Tangent F x)`.
  These are not arbitrary structures: the subsequent iff clauses determine their
  zero, scalar action and addition by the actual geometric operations.
- Zero: `IsZeroClass F x t ↔ t = 0`. The relation requires a projection back to x
  above the constant inclusion and a splitting of the marking, hence the constant lift.
- Scalars: `IsScalarClass F x c t s ↔ s = c • t`, with the actual recorded
  `squareZeroMap (c • LinearMap.id)` giving epsilon ↦ c epsilon.
- Addition: `IsSumClass F x t s r ↔ r = t + s`, using one marked object over
  `squareZeroTest (k × k)`, its two projection restrictions, then the sum map.
  The ring is exactly k[epsilon1,epsilon2]/(epsilon1,epsilon2)^2.
- The parenthetical uniqueness assertion is explicit: for each pair t,s there exists
  a marked pair-lift Z and every other pair-lift Z' has `Nonempty (Z ≅ Z')`.
- No properness, separatedness, smoothness of F over R or stabilizer assumption occurs.

Dependency declarations used, with signatures and docstrings read:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (abbreviation of
  `IsNoetherian R R`, all ideals finitely generated).
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`,
  `IsSmoothModuliAtlas`, and their actual projection predicates; these use
  `BasedCategory`, `IsModuliStack`, `IsFibredInGroupoids` and `discreteModuli` from
  `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`.
- `Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory`:
  `TestCategory`, `ring`, `squareZeroAlgebra`, `squareZeroTest`.
- `Sheaf.AlgebraicGeometry.ArtinRSTangentTensor`: `squareZeroMap`, reusing the existing
  canonical residue-preserving map for every finite-dimensional direction module.
- Mathlib's `Functor.Fiber`, `Functor.Fiber.fiberInclusion`, `StructuredArrow`,
  `ObjectProperty.FullSubcategory` and `isIsomorphicSetoid` construct marked categories
  and their quotient, rather than a private category or equivalence relation.
- `WeilConjectures.AlgebraicGeometry.DensePoints` is the non-public import of the stated
  proof dependency `Scheme.Hom.dense_setOf_isClosed_finite_isSeparable`.
  The other proof-only nodes (algebraic-stack RS, marked tangent field extension,
  smooth-space infinitesimal lifting) have no landed Lean records and are not imported.
  Their proof uses are retained verbatim in the theorem docstring. Algebraic spaces and
  tensor products are available through the existing public dependency imports.
- `def-weil-size-convention` is explicitly recorded as a convention without a declaration;
  it is implemented by the universe binders, not restated as a Lean object.

Edge cases checked against the definitions: k=R a field; the constant stack point with
zero tangent dimension; the empty affine-generator set n=0; arbitrary characteristic,
including characteristic 2 (no division by 2 occurs); an empty stack admits no such x,
so the theorem has no artificial nonemptiness hypothesis; nonseparated stacks and stacks
with nontrivial stabilizers remain allowed. Marked automorphisms are retained before the
quotient. For R=F_p(s) and B=l=R[t]/(t^p-s), the source's point-ideal argument is invalid
(ker of the identity point is zero but t may lift to t+c epsilon); the inherited split
correctly uses algebra generators. This is a source-proof issue already documented in
stage 1, not a statement fault or correction.

Searches actually run through `msearch.py`:

- LeanFinder: "The marked deformation tangent space of a locally finite type algebraic
  stack is finite dimensional". Results concern finite Kaehler/cotangent modules and
  scheme morphisms; no marked-stack theorem.
- Loogle: "FiniteDimensional, Derivation". Zero hits; no algebraic-stack theorem
  or marked groupoid construction.
- Mathlib grep: "[Ss]tack.*[Tt]angent|[Tt]angent.*[Ss]tack". No relevant stack tangent result;
  text matches in project cotangent source citations do not define this notion.
- LeanSearch: "marked deformations of an object of a category fibred in groupoids over
  schemes". Eight scheme smoothness/formal-unramifiedness hits; no marked construction.
- LeanFinder: "marked deformation groupoid of an object of a stack over an augmented
  algebra". Eight generic stack/descent/groupoid hits; no marked construction.
- Mathlib grep: "[Mm]arked[Dd]eformation|[Dd]eformation[Gg]roupoid": zero hits.
- Project rg for `MarkedDeformation`, `markedDeformation`, `tangentModule`,
  `canonicalTangent`, stack/tangent phrases and the item id, in both WeilConjectures
  and Sheaf: the proper-curve specialization and the Artin criterion over Spec Z are
  present, but neither works over the arbitrary Spec R of this statement. The latter's
  full `MarkedDeformation` and `FiniteTangent` signatures and docstrings were read.
- DAG search of definition ids and marked/deformation keywords: scheme lifts, proper
  curves, marked module lifts and infinitesimal automorphisms concern different objects.
- `tools/blueprint_refs.py search 'marked deformation'`: 0 matching blueprint nodes.
  `ancestor lem-sfb-algebraic-stack-tangent-finite` reports inherited ancestor None;
  the new node retains that inherited null ancestor and the complete via chain.
- Proposed namespace/declaration names were searched in `dag/lean_names_upstream.json`,
  WeilConjectures and Sheaf: no collision.

Validation: both delivered files compiled separately through scompile.py, against the
published live build, with no errors or warnings. Definitions contain real data and no
sorry; the sole theorem has sorry. All variables/universes are explicit, autoImplicit is
false, and no line exceeds 100 characters. An initial default-opposite-action mismatch
for the constant ring map was repaired by using the exact restricted scalar structure
of `squareZeroAlgebra`, and both modules then compiled cleanly.

## New nodes

`def-sfb-marked-stack-deformations`, module
`Sheaf.AlgebraicGeometry.MarkedStackDeformations`, defines marked categories over the
existing Artinian test category, their class sets, tangent set and the canonical
operation relations. Source: Tag 07T4 and equation-tangent-space in artin.tex, with the
two-direction operation of formal-defos.tex Tag 06IH. The three recorded search types
and their actual outputs are in its mathlib_searches. The older proper-curve construction
is specialized to proper curves and the Artin-criterion construction to Spec Z; there is
no general marked-stack construction over Spec R to reuse. The full subcategory of
structured arrows constructs the category with real data. The affine maps are Spec of
the existing algebra homomorphisms, and the square-zero test maps are reused from
`lem-sfb-artin-rs-tangent-tensor`. This new definition asserts no existence, vector law or
finiteness theorem. The item's stmt_deps gains precisely this new node.

Delivery validation: the prescribed dry run passed preflight and both per-file compiles.
The first preflight requested the new node field `import_flags` and the complete theorem
signature (including named arguments); both metadata issues were repaired.

## Second reading by Q34

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
