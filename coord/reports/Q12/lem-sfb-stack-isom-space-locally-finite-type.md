## Worker report

The module `Sheaf.AlgebraicGeometry.StackIsomSpaceLocallyFiniteType` states
`CategoryTheory.moduli_isom_space_locallyOfFiniteType`. Its sole postponed proof is
`sorry`. The two helper structures package the exact representing objects and maps
asserted by this node; neither constructs data by choice or by a postponed proof.
Every declaration has the owning node's blueprint/source docstring. The theorem's
nine-step proof docstring follows the node's nine proof steps and the source at
`literature/stacks-project/stacks-morphisms.tex`, Tag 04XR, lines 55–95, and the
following `lemma-isom-pseudo-torsor-aut(1)`. No statement correction is needed.

Hypotheses and clauses, with the node and Lean source open:

- The arbitrary scheme S is `{S : Scheme.{u}}`; the arbitrary fibred category X
  is `F : BasedCategory.{v, w} (Over S)`. The three universes are explicitly bound.
  They are not identified, and no smallness assumption is imposed on the total category.
- X is an algebraic stack: `hF : IsAlgebraicModuliStack F`. Reading that definition
  gives exactly `IsModuliStack F`, `HasAlgebraicSpaceDiagonal F`, and the existence
  of `IsSmoothModuliAtlas F U a`. The latter specifies every scheme 2-base change,
  its projection to the test scheme, chartwise smoothness, and surjectivity on points.
  It uses the recorded definitions in StablePointedModuliGroupoids, not a replacement.
  The landed node `def-sfb-algebraic-moduli-stack` is added to statement dependencies.
- T is an S-scheme: `T : Over S`, with no finiteness, separation, or nonemptiness
  assumption. Its two objects are
  `a b : BasedFunctor (discreteModuli (yoneda.obj T)) F`. Fibred Yoneda identifies
  these maps h_T → X with objects of X(T), retaining all arrows and automorphisms.
  Since all arrows in a fibred groupoid are cartesian, no additional cartesian-map
  hypothesis is needed on these based functors.
- The Isom sheaf is represented by the first conjunct's `I : ModuliIsomSpace T a b`.
  Its `space : AlgebraicSpace S` is the existing fppf-sheaf algebraic-space notion,
  and its `projection` gives the specified map to T. For every V/S and every
  `t : yoneda.obj V ⟶ yoneda.obj T`, `comparison V t` is a bijection from sections
  of I over t to `ModuliTwoIso ((discreteModuliMap t).comp a)
  ((discreteModuliMap t).comp b)`. Thus it identifies exactly the isomorphisms of
  the two pulled-back objects, not their isomorphism classes, their cardinalities,
  or a chosen arbitrary map. `naturality` equates their components after restriction
  along every `f : W ⟶ V`. Testing all components is equality of the restricted
  natural transformations. These bijections naturally identify the original Isom
  presheaf with an algebraic-space sheaf, hence include the asserted sheaf condition.
- Local finite type over T is the first conjunct's
  `∀ V c, AlgebraicSpace.IsEtale c →
    LocallyOfFiniteType ((yoneda.preimage (c ≫ I.projection)).left)`.
  It tests every representable étale source scheme chart using Mathlib's exact
  scheme property. The target T itself is a scheme, so its identity is an étale
  target chart; testing all source charts into that target is the usual equivalent
  chartwise criterion. This does not assume quasi-compactness or finite presentation.
- The second conjunct uses `G : ModuliAutomorphismGroupSpace T a`, extending
  `ModuliIsomSpace T a a`, so it represents exactly Aut_X,T(a) = Isom_X,T(a,a).
  It has the same local-finite-type condition over the same T.
- This is a group algebraic space: `unit`, `inverse`, and `multiply` are natural
  transformations of the actual representing presheaves, with multiplication
  domain `pullback projection projection`. Since algebraic spaces form a full
  subcategory of sheaves, these are algebraic-space morphisms over T. `laws` is
  the existing `AlgebraicSpace.IsPresheafGroupoid projection projection ...`, whose
  source and target coincide and whose identity, inverse, associativity and
  projection laws are exactly the group-object laws over T. The landed node
  `def-sfb-algebraic-space-groupoid` is added to statement dependencies.
- Multiplication is the specified composition, not an unrelated group law:
  `multiply_comparison` says that the image of a product of sections g,h is
  `(comparison ... h).hom ≫ (comparison ... g).hom`, componentwise, meaning g
  after h. The pullback universal property supplies every pair of sections over
  the same test map t. `unit_comparison` and `inverse_comparison` likewise identify
  the identity and inversion. The conclusions of these implications are not
  vacuous: the structural projection laws ensure that products, units and inverses
  belong to the displayed fibre, and the presheaf pullback supplies q.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  read their full structure signatures and docstrings in the pinned local Mathlib.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids` (through public
  `AlgebraicModuliStack`): `IsFibredInGroupoids`, `IsModuliStack`, `ModuliTwoIso`,
  `discreteModuli`, `discreteModuliMap`, `HasSpaceBaseChange`,
  `HasAlgebraicSpaceDiagonal`, and `SpaceMapIsSurjective`; read lines 364–545.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace` (through those public imports):
  `AlgebraicSpace`, `IsRepresentableWith`, `IsRepresentable`, `IsAlgebraicSpace`,
  `IsEtale`; read their full definitions and source docstrings, lines 40–91.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth` (through public `AlgebraicModuliStack`):
  `AlgebraicGeometry.Smooth`; read the affine-local full class signature and docstring.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; read the full affine-local class definition.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`,
  `IsSmoothModuliAtlas`, `SpaceMapIsSmooth`; read the complete module, and confirmed
  the current published source with `scompile.py --source`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceGroupoid`:
  `AlgebraicSpace.IsPresheafGroupoid`; read the complete structure with all its laws.

Proof-only imports follow the recorded proof plan: the finite-presentation,
universally-open, affine quasi-separatedness and fpqc Mathlib modules;
`AlgebraicSpaceFibreProductsEtaleCovers`, `ChartwiseEtalePermanence`, and
`Morphisms.LocallyOfFiniteTypeOfFpqcCover`. The smooth-flat and affine-compactness
facts, scheme fibre products and finite-type cancellation are available through
these modules and the statement imports. `lem-sfb-stack-finite-type-calculus` has
no Lean record or Mathlib match, so its module cannot yet be imported; its use in
the proof is retained in the docstring and the DAG. Nothing from that node is
needed to type this statement. No dependency interface is repaired.

Searches (2026-10-24):

- `msearch.py ... leanfinder "The isomorphism sheaf of two objects of an algebraic
  stack is an algebraic space locally of finite type"`: eight hits, all unrelated
  scheme isomorphism or finite-presentation declarations; no matching stack theorem.
- `msearch.py ... loogle "AlgebraicGeometry.LocallyOfFiniteType,
  CategoryTheory.IsModuliStack"`: zero hits, unknown identifier IsModuliStack in
  Mathlib. The project definition is used directly.
- `msearch.py ... grep "Isom.*[Ll]ocally|[Ii]som.*[Ss]tack|AlgebraicStack"
  AlgebraicGeometry`: two hits in Mathlib's LocalIso, no algebraic-stack Isom theorem.
- `rg` of Isom/Aut presheaf, Isom local finite type, algebraic-stack and smooth-map
  predicates in `lean/WeilConjectures` and `lean/Sheaf`: no matching theorem;
  found and reused AlgebraicModuliStack and AlgebraicSpaceGroupoid. Searching the
  exact node id in WeilConjectures found no declaration. Searches of all three new
  declaration names in both source trees found no existing names.
- Read the existing `DmPointStabilizer.IsModuliAutomorphismSpace` predicate: it is
  the same natural identification in the special a=a case. It neither supplies
  the general Isom representation nor specifies group operations or local finite
  type. The structures here package the full witnesses requested by this node;
  they do not restate that existing predicate or its theorem. No import of this
  downstream consumer is needed, avoiding an eventual proof-import cycle.
- Checked `dag/lean_names_upstream.json` and the relevant DAG records; no upstream
  algebraic-stack Isom theorem is attached. The added dependencies already have
  landed modules; no new independent notion node is introduced.

Edge cases checked before writing and again against the finished signature:
empty T; the empty Isom space for non-isomorphic objects; a=b with nontrivial,
possibly nonreduced automorphism space (for example the additive group); arbitrary
characteristic; arbitrary and non-separated base S; non-quasi-compact atlases; and
unrelated total-category universes v,w. No restriction to field-valued, reduced,
affine, smooth, or finite-type test schemes is made. The trivial automorphism over
empty T is permitted. No finiteness of the automorphism group is asserted.

Validation: the prescribed `scompile.py Q12 ...` compiled the module independently
in sandbox and library modes in 5.6 and 5.8 seconds, with no errors or warnings.

## Second reading by Q12

I reread the node's statement, the complete delivered module and the definitions
of IsAlgebraicModuliStack and IsPresheafGroupoid after the successful compile.
This is a self-reading: the dispatcher explicitly prohibits starting other agents;
the maintainer's independent delivery review remains separate.

The S/T binders, algebraicity hypothesis, test-scheme bijections and restriction
law, actual algebraic-space carrier, specified projection, chartwise local finite
type, and a=a group case agree clause by clause as detailed above. I checked the
order of multiplication carefully: c(g,h) is g after h, and Lean's forward
composition is `theta(h).hom ≫ theta(g).hom`. The two equal projection maps make
all elements over a common test map composable. Identity and inverse are normalized
by the same comparison. The equivalence is on vertical isomorphisms, retaining
all automorphisms. No change to the node's statement or proof was needed. The two
added dependencies cite already existing definitions instead of making private copies.
