## Worker report

The module `Sheaf.CategoryTheory.Adjunction.LeftCoefficientProjectionAction` defines
`CategoryTheory.Adjunction.leftCoefficientProjectionMap` by the exact symmetry conjugate in
the node, and states `leftCoefficientProjectionMap_coherence` with `sorry`. No proof is supplied.
Only the item's `lean` field changes. There are no new nodes, dependency repairs, statement
corrections, or disputed statements.

Source read: `literature/stacks-project/sites-cohomology.tex`, lines 13657–13678, Tag 0B56,
`equation-projection-formula-map`. It defines the right-coefficient projection by the counit
adjunct. The node's five categorical calculations supply the symmetry, naturality, unit, and
associativity proof, reproduced step by step in the theorem docstring. I also read the current
main-20261015 `sec-six-functors-basics/sk-prop-cohsm/sk-prop-cohsm.proof.md`, (G13), where the
projection formula is used. The item is an auxiliary categorical lemma, not the unit statement.

Hypothesis and clause correspondence:

- The categories C and D have separately explicit object universes u₁, u₂ and morphism
  universes v₁, v₂: `[Category.{v₁} C]`, `[Category.{v₂} D]`. Both have `MonoidalCategory`
  and `SymmetricCategory` instances. The latter includes natural swaps, the two hexagons,
  and involutivity; no strictness or size identification is imposed.
- `F : C ⥤ D`, `R : D ⥤ C`, `[F.Braided]`, and `(adj : F ⊣ R)` render the symmetric strong
  monoidal functor and its given right adjunction. `Functor.Braided` extends `Functor.Monoidal`
  and preservation of the braiding. This is exactly symmetric strong monoidal between
  symmetric categories. `adj.homEquiv` and `adj.counit` use the recorded adjunction convention.
- The node's inverse tensorator δ is `Functor.OplaxMonoidal.δ F`, and its inverse unit map e
  is `Functor.OplaxMonoidal.η F`. Mathlib `Functor.Monoidal.μIso` and `.εIso` have these as
  their inverses, so this is the same strong monoidal data as `CoreMonoidal`, not a new notion.
- The node's ρ is the component
  `((adj.rightAdjointProjectionMap (Functor.OplaxMonoidal.δNatTrans F)).app N).app B`.
  Reading its definition shows that it is `adj.homEquiv` applied to δ followed by
  `adj.counit.app N ⊗ 1`. It is reused, not redefined.
- The definition `leftCoefficientProjectionMap adj B N` is precisely β(B,RN), then that ρ,
  then `R.map (β_ N (F.obj B)).hom`. Its declared source and target are `B ⊗ R.obj N` and
  `R.obj (F.obj B ⊗ N)`, as for t in the node.
- The first conjunct quantifies over arbitrary B, B', N, N' and maps f and g. It states
  `t ≫ R.map (F.map f ⊗ₘ g) = (f ⊗ₘ R.map g) ≫ t`, the joint naturality square, hence
  exactly naturality in both arguments.
- The second conjunct, for every B and N, is `F.map t ≫ adj.counit.app (F.obj B ⊗ N) =
  δ F B (R.obj N) ≫ (𝟙 (F.obj B) ⊗ₘ adj.counit.app N)`. Lean composition is left to right;
  this is the displayed transpose equation with the node's right-to-left convention.
- The third conjunct is `t(unit,N) ≫ R.map ((η F ⊗ₘ 𝟙 N) ≫ (λ_ N).hom) = (λ_ (R.obj N)).hom`.
  The inline argument of `R.map` is exactly h^F_N, with no extra hypothesis or conclusion.
- The fourth conjunct, for every B, B', N, is `t(B⊗B',N) ≫ R.map a = α ≫ (1 ⊗ t(B',N)) ≫
  t(B,FB'⊗N)`, with a written out as `(δ F B B' ⊗ₘ 𝟙 N) ≫ (α_ (F.obj B) (F.obj B') N).hom`.
  This is precisely the node's associativity clause. Neither ρ nor t has an `IsIso` binder.

Dependency declarations read and used:

- `def-sfb-monoidal-category`: `CategoryTheory.MonoidalCategory`,
  `Mathlib.CategoryTheory.Monoidal.Category`, full data and axioms at lines 87–210.
- `def-sfb-strong-monoidal-functor`: `CategoryTheory.Functor.CoreMonoidal`,
  `Mathlib.CategoryTheory.Monoidal.Functor`, lines 620–651; equivalent instance interface
  `Functor.Monoidal` and its `.μIso`, `.εIso` at lines 389–415. `Functor.Braided` extends
  this standard interface, rather than introducing another strong monoidal structure.
- `lem-weil-pbc-adjunction-of-natural-bijection`: `CategoryTheory.Adjunction.mkOfHomEquiv`,
  `Mathlib.CategoryTheory.Adjunction.Basic`, with `CoreHomEquiv` and the standard homEquiv
  formulas. The statement takes the resulting adjunction as given; its transpose is
  `F.map v ≫ adj.counit.app _`, exactly `Adjunction.homEquiv_counit`.
- Reused canonical map: `CategoryTheory.Adjunction.rightAdjointProjectionMap` and its
  component formula, `WeilConjectures.CategoryTheory.Adjunction.ProjectionMap`, lines 170–222.
- Reused inverse tensorator transformation: `CategoryTheory.Functor.OplaxMonoidal.δNatTrans`,
  `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor`.
- Symmetry: `SymmetricCategory`, `Functor.Braided`,
  `Mathlib.CategoryTheory.Monoidal.Braided.Basic`, including full signatures and docstrings.
  All statement and proof dependencies are Mathlib leaves and available through these imports.

Edge cases checked before writing: the identity adjunction reduces t to the identity
(two swaps cancel); B or B' equal to the tensor unit gives the stated unitor equations;
there are no zero-object, nonempty, additive, dualizability, or invertibility assumptions.
For free abelian group from cartesian Set to tensor Ab, left adjoint to underlying set,
the strong monoidal functor gives a noninvertible example: B empty makes the domain of t
empty but its target the singleton underlying zero group. The formulation retains it.
Empty categories introduce no object-level exceptions, and all four universes are independent.

Searches actually run:

- `msearch.py leanfinder`: “The symmetry conjugated counit projection map B tensor R N to R
  of F B tensor N for a symmetric strong monoidal adjunction is natural and satisfies unit
  and associativity”. Eight hits, including `Adjunction.map_μ_comp_counit_app_tensor` and
  the unit identities for a monoidal adjunction. They concern the two-counit lax monoidal
  map, not this symmetry conjugate and its four assertions.
- `msearch.py loogle`: `CategoryTheory.Adjunction, CategoryTheory.Functor.Monoidal`.
  Twelve hits on monoidal-adjunction unit/counit and monoid-object adjunctions, no exact match.
- `msearch.py grep`: `projection|Projection`, `CategoryTheory/Monoidal`.
  Seven hits: ring-object simps projections, Day convolution, action endomorphisms and
  cartesian projections, none this lemma.
- `msearch.py leansearch`: “The right adjoint counit projection with coefficient on the left
  satisfies the tensor unit and associativity identities”. Eight hits, including monoidal
  counit and comonoid identities, none this lemma.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for `rightAdjointProjection`,
  `leftProjection`, `projectionMap`, `projectionFormulaMap`, `leftCoefficient`, and the item id.
  Found the general right projection and right-coefficient associativity/unit modules;
  read `ProjectionMap`, `ProjectionMapMonoidal`, `ProjectionMapUnit`, and `ProjectionMapAssoc`.
  These do not state the symmetry-conjugated left-coefficient equations. The exact item id
  has no upstream Lean hit.
- `rg` in Mathlib, both project roots, and `dag/lean_names_upstream.json` for
  `leftCoefficientProjectionMap|leftProjectionMap|leftProjection.*coherence`: no hits.

Validation: prescribed `scompile.py Q01 lem-pur-adjoint-left-projection-action <module>`
passed both sandbox and library-module compilation, 2.8 s and 2.0 s, with no warnings or errors.

## Second reading by Q01

I reread the node's full statement alongside the final Lean file as a separate checking pass.
This is a self-check by the sole dispatched worker; the brief forbids starting agents, and
independent delivery review belongs to the maintainer. The mathematical checks were:
F.Braided includes exactly strong monoidality and swap preservation; δ and η are the
inverse structure maps (not the forward ones); the existing ρ uses the counit on its first
factor; the two symmetry maps have respectively B,RN and N,FB as their arguments. All
four conjuncts were checked with Lean's composition order reversed against the TeX:
the naturality square, F(t) followed by the counit, t followed by R(h), and t followed by
R(a) versus α followed by 1⊗t and then t. The outer quantifiers include all objects and
all naturality morphisms. There are no extra assumptions on R or on projection components,
no let binders, no file-local notation, no hidden choice of a projection map, and no
universe equality. No mismatch was found and no correction was necessary.
