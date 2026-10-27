## Worker report

The module `Sheaf.AlgebraicGeometry.AffineFiniteFreeHom` states
`AlgebraicGeometry.exists_affine_finite_free_hom`, with its entire proof `sorry`.
It represents exactly the pair-valued functor in the node by an affine scheme,
using the already landed `relativeMorphismsPresheaf`. There are no new definitions,
new nodes, dependency repairs, or statement corrections. The only node changes are
`lean` and addition of the landed definition `def-sfb-relative-morphisms-presheaf`
to `stmt_deps`.

Hypotheses and clauses, in order:

- Scheme and size convention: `(S : Scheme.{u})`, with explicit `universe u` and
  `set_option autoImplicit false`. All rings are `Type u` and all test schemes are
  arbitrary objects of `Over S` (objects live in `Type (u+1)`, morphisms in `Type u`).
  There is no restriction to affine test schemes.
- The three affine schemes are literally `Spec (.of R)`, `Spec (.of B)`, and
  `Spec (.of C)`, for arbitrary commutative rings `R B C`. The given maps to `T`
  are `Spec.map (CommRingCat.ofHom (algebraMap R B))` and its `C` analogue.
  `[Algebra R B]` and `[Algebra R C]` encode exactly the induced ring maps.
  By affine duality this covers every pair of affine morphisms in the node.
- The external `S`-structure on `T` is `(t : Spec (.of R) ⟶ S)`; composing the two
  displayed morphisms with `t` gives the `S`-structures on `Z` and `Y`, so their
  being `S`-morphisms is built in rather than a further condition.
- The finite free hypothesis is precisely `(m : ℕ)` and
  `(_basis : Module.Basis (Fin m) R B)`. The underscore suppresses the unused
  binder warning in this statement-only module; the basis is a real argument.
  This is the finite-indexed basis notion from the recorded free-module node,
  not an additional finite-presentation or nontriviality assumption.
- At `U : Over S`, `a : U ⟶ Over.mk t` is exactly an `S`-morphism `U → T`.
  For this `a`, the value of `relativeMorphismsPresheaf z x` at
  `op (Over.mk a.left)` consists of maps `U ×_T Z → Y` over `T`.
  Its definition is `(Over.pullback z ⋙ Over.map z).op ⋙ yoneda.obj (Over.mk x)`:
  its objects have underlying pullback `pullback a.left z`, and the `Over T`
  morphism to `Over.mk x` imposes precisely that the map is over `T`.
  Thus the dependent sum `Σ a, ...` is exactly `F(U)`, including both entries.
- Existence of an affine scheme over `T` is the existential `(M : Scheme.{u})`
  and `(p : M ⟶ Spec (.of R))` with `IsAffine M`. Its structure over `S` is
  `p ≫ t`. No affineness requirement on `S` is introduced.
- The existential `b` is a universal relative morphism at the `T`-scheme
  `Over.mk p`. For every `U : Over S`, the displayed `Function.Bijective` maps
  `f : U ⟶ Over.mk (p ≫ t)` to the pair with first entry `f.left ≫ p` and
  second entry the presheaf restriction of `b` along `f.left`.
  A bijective function gives precisely a bijection, with no arbitrary family of
  maps or extra representability hypotheses.
- Compatibility with `Mor_S(U,T)` is explicit in the first component,
  `Over.homMk (f.left ≫ p) ...`. Naturality is enforced by the formula, not
  omitted: for any `g : V ⟶ U` over `S`, the first component of the image of
  `g ≫ f` is `g.left ≫ f.left ≫ p`; its second is the restriction of `b` along
  the same composite over `T`. The presheaf composition law identifies it with
  the restriction of the second component for `f` along the induced pullback
  map `V ×_T Z → U ×_T Z`. This is exactly the node's restriction operation.
  Conversely any natural bijection compatible with the first projections yields
  this `b` by applying it to `id_M`; naturality forces the displayed formula.
  Thus using a universal element introduces no stronger conclusion.
- `C` has only a commutative ring and `R`-algebra structure. There is no
  `FiniteType`, `FinitePresentation`, finite generator, or Noetherian condition.
- Rank zero is included: `Fin 0` is allowed and there is no `0 < m` or
  `Nontrivial B` assumption.

Dependency declarations used (source signatures and docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`. These and the fibre-product modules are available through
  the public import of the existing relative morphism presheaf.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.map`, used by that presheaf; scheme
  pullbacks exist via `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free` and its basis notion
  `Module.Basis`, used explicitly at index `Fin m` (Basis/Defs.lean).
- `def-weil-size-convention`: the recorded metatheoretic convention has no
  declaration; explicit Lean universes implement it.
- `Sheaf.AlgebraicGeometry.RelativeMorphismsPresheaf`:
  `AlgebraicGeometry.relativeMorphismsPresheaf` (the existing node added to
  `stmt_deps`), with full body and its base-change functor inspected.

The proof dependencies are Mathlib leaves, not absent project prerequisites.
Their modules are imported for the proof plan: polynomial Basic/Eval;
Ideal.Quotient.Operations and Ideal.Operations; RingTheory.TensorProduct.Maps;
LinearAlgebra.TensorProduct.Basis; AlgebraicGeometry.Gluing. The affine tensor
spectrum formula is in Pullbacks, already publicly imported by the presheaf.
The docstring records all seven proof steps, including arbitrary presentations,
coefficient relations, basis uniqueness, the algebra-map bijection, universal
morphism, affine-open gluing, and the external `S`-structure and rank-zero case.

Edge cases checked mathematically before writing:

- `m = 0`: `B` is zero, `Z` is empty, and `F(U) = Mor_S(U,T)` for every `U`;
  `M = T` represents it, including nonzero `C`.
- Empty `U`: its unique map to `T` has empty pullback and a unique relative map;
  there is also exactly one map from empty `U` to `M`.
- Zero base ring: all unital `R`-algebras are zero, all three spectra are empty;
  only test schemes admitting a map to empty `T` contribute to the dependent sum.
  The formula retains the empty/nonempty cases correctly.
- `B = R` with rank one: the functor reduces to morphisms into `Y`, so `M = Y`.
- `C = R`: the second entry is uniquely the structure map, so `M = T`.
- `B = R[epsilon]/epsilon^2`, `C = R[x]`: the coefficient construction gives
  affine two-space. Arbitrarily many generators or relations in `C` are allowed.

Searches for existing notions and statements:

- `msearch.py ... leanfinder` query: "For affine schemes Z and Y over affine T,
  with Z finite free over T, the relative Hom functor from Z to Y is represented
  by an affine scheme". Eight hits: `AffineScheme.ofHom`, `AffineSpace`,
  `AffineSpace.instIsAffineHomOverSchemeInferInstanceOverClass`,
  `AffineSpace.homOverEquiv`, `AffineSpace.instIsOverHomOfVectorOverSchemeInferInstanceOverClass`,
  `instCategoryAffineScheme`, `AffineSpace.over`, `AffineSpace.homOverEquiv_apply`.
  These define affine schemes/space and its coordinates, not this representability
  statement for arbitrary affine targets.
- `msearch.py ... loogle 'AlgebraicGeometry.Scheme, Module.Basis'`: zero hits.
- `msearch.py ... grep 'WeilRestrict|[Rr]elativeHom|homFromFinite|finiteFree.*[Rr]epresent'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and Mathlib AlgebraicGeometry for
  `relativeHom|RelativeHom|homFunctor|HomFunctor|homFrom|HomFrom|weilRestrict|WeilRestrict`:
  mostly internal module-sheaf Hom; `RelativeHomSchemeData` in HighGenusHomClosure
  has extra geometric covering data and is not this functor or theorem.
- `grep -rn lem-sfb-affine-finite-free-hom lean/WeilConjectures`: no match;
  searches of the upstream declaration index and repair notes found no binding
  or repair requirement for this item.
- DAG search for relative morphism functors found
  `def-sfb-relative-morphisms-presheaf`. Opened its full node record and module:
  its landed definition is exactly the needed fixed-`a` functor. It is reused,
  not restated, and added to `stmt_deps` under the landed-node allowance.

Source checked: local Stacks more-morphisms.tex, Tag 05Y6, including the preceding
`equation-hom-functor` and its polynomial coefficient construction. The external
`S` and dependent pair in the node are the disjoint union of that represented
functor over the possible maps `a : U → T`. No statement fault or dispute found.

Validation: prescribed `scompile.py` compiled both its sandbox check and the
actual module cleanly. The initial elaboration needed an explicit associativity
identity for the `Over S` map; using `(Category.assoc f.left p t).trans f.w`
resolved it. No diagnostic declarations remain.

## Second reading by Q147

Author's second pass, not an independent review (the dispatcher brief forbids
starting other agents; the maintainer supplies independent review).
Re-read the node and final module together. The basis is genuinely finite, the
zero rank is admitted, all three coordinate rings are arbitrary, and `S` itself
is arbitrary. The use of `Over S` includes exactly the node's `S`-morphisms.
The dependent sum preserves `a`; the fixed-`a` fibre is the already defined
relative morphism functor. Its restriction along `Over.homMk f.left rfl` is the
canonical induced fibre-product map, so naturality is part of the universal
formula and compatibility with `Mor_S(U,T)` is literally its first projection.
Checked that the converse reconstruction of the universal `b` from a natural
bijection shows no strengthening. No missing clause or added hypothesis found.
Only the associativity proof needed a compile repair; no mathematical statement
was changed. Every theorem proof in the delivered module is exactly `sorry`.
