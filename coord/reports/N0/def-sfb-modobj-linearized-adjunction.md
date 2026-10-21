## Worker report

Existing match: `CategoryTheory.Functor.ProjectionFormula.mapModAdjunction`, in
`WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula` (source lines 473–487).
The associated `smul_comp_eq_iff` (456–471) states the linearity equivalence explicitly.
The delivery changes only the item's `lean` field and introduces no Lean module.
The source and its enclosing binders were read locally and confirmed using
`scompile.py --source WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`.
No repair note exists for this item.

Source: current blueprint `main-20261015`, chapter `sec-proetale-coefficients`, unit
`sk-def-sfb-transport`, `def-sfb-modobj-linearized-adjunction.md` and its proof file.
The recorded source statement is unchanged.

Hypothesis-by-hypothesis correspondence:

- Arbitrary monoidal categories C and D: `{C : Type u₁} [Category.{v₁} C]
  [MonoidalCategory C] {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]`.
  The four universes are independent.
- The strong monoidal functor is `{S : D ⥤ C} [S.Monoidal]`; its transport supplies
  the monoid structure on `S.obj B`.
- The functor and coherent projection formula are `{P : C ⥤ D}` and
  `(pf : S.ProjectionFormula P)`. The structure's `iso`, `natural_left`,
  `natural_right`, `unit`, and `assoc` give exactly the assumed projection formula.
- The assumed adjunction is `{G : D ⥤ C} (adj : P ⊣ G)`. There is no assumption
  that G equals S, nor any additivity, exactness, braiding, or commutativity assumption.
- The coefficient object is `(B : D) [MonObj B]`, subsequently made implicit
  with `variable {B}` before the recorded adjunction declaration.
- The arbitrary module objects in the restricted bijection are
  `(M : Mod C (S.obj B)) (N : Mod D B)`.

Clause-by-clause correspondence:

- The left linearization is exactly `pf.mapModLeft B`, with action
  `pf.smul B M.X = (pf.iso B M.X).inv ≫ P.map γ[S.obj B,M.X]`.
- The right linearization is exactly `pf.mapModRight adj B`, with action
  `pf.rightSMul adj B N.X = pf.theta adj B N.X ≫ G.map γ[B,N.X]`.
  Here `theta` is the adjoint of the projection isomorphism followed by
  `B ◁ adj.counit.app N.X`, as required by the dependency.
- B-linearity of an underlying map `φ : P.obj M.X ⟶ N.X` is
  `pf.smul B M.X ≫ φ = B ◁ φ ≫ γ[B,N.X]`. The forward side of
  `pf.smul_comp_eq_iff adj M N φ` is exactly this equation.
- The other side of that iff is
  `γ[S.obj B,M.X] ≫ adj.homEquiv M.X N.X φ =
   S.obj B ◁ adj.homEquiv M.X N.X φ ≫ pf.rightSMul adj B N.X`.
  This is precisely S(B)-linearity of the original adjoint map.
- The adjunction's `homEquiv` has `toFun φ` equal to
  `Mod.Hom.mk' (adj.homEquiv M.X N.X φ.hom)` with the forward linearity proof.
  Its `invFun ψ` uses `(adj.homEquiv M.X N.X).symm ψ.hom` and the reverse
  linearity proof. Thus it is the restriction of this particular original
  adjunction bijection, not an arbitrary adjunction between these functors.
- The inverse identities are the original equivalence's inverse identities,
  lifted using equality of underlying module maps.
- `homEquiv_naturality_left_symm` and `homEquiv_naturality_right` are filled by
  the original `adj.homEquiv_naturality_left_symm` and
  `adj.homEquiv_naturality_right`, using `Mod.hom_ext`. Therefore
  `Adjunction.mkOfHomEquiv` constructs exactly
  `pf.mapModLeft B ⊣ pf.mapModRight adj B` with the required naturality.

Dependency declarations read and used:

- `def-sfb-modobj-linearization`: the recorded
  `CategoryTheory.Functor.ProjectionFormula.mapModLeft`, in
  `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`, including
  `smul`, `modObj`, and the object/map/forgetful formulas.
- `def-sfb-modobj-linearization-right-adjoint`: the recorded
  `CategoryTheory.Functor.ProjectionFormula.mapModRight`, in the same module,
  including `theta`, `rightSMul`, `rightModObj`, and its forgetful formula.
- `sk-def-sfb-module-objects`: `CategoryTheory.Mod` in
  `Mathlib.CategoryTheory.Monoidal.Mod`, with `ModObj`, `Mod.Hom`,
  `Mod.Hom.mk'`, and `Mod.forget`. The generic module-object clause is exactly
  what this generic adjunction uses; no pro-etale specialization is required.
- The proof dependency `def-sfb-projection-formula` records
  `CategoryTheory.Functor.ProjectionFormula` in the same upstream module;
  its complete structure signature and coherence fields were read.

Edge cases checked by reading the full construction: it applies to arbitrary,
possibly noncommutative monoid objects; neither category must be abelian or
symmetric. The identity adjunction and unit coefficient monoid are included,
as are zero module objects whenever they exist. Neither hom-set must be
nonempty: the equivalence and its restrictions are defined without choosing
an element. Four independent universes preserve unequal category sizes.
The proof uses invertibility of the specified projection formula and the
specified counit; it assumes no invertibility of the mate theta. No node
fault or STATEMENT-DISPUTED issue was found.

Searches (all through the required msearch wrapper where applicable):

- LeanFinder: `An adjunction restricts to module objects using a projection formula`:
  eight results on ordinary modules, including `ModuleCat.restrictCoextendScalarsAdj`,
  `ModuleCat.adj`, and restriction/coextension unit/counit formulas; no generic match.
- Loogle: `"mapModAdjunction"`: zero Mathlib hits.
- LeanSearch: `projection formula gives an adjunction between module object categories`:
  eight specialized sheaf/module adjunctions, including scheme module pullback,
  sheafification, and extension/restriction; no generic match.
- Mathlib grep: `mapModAdjunction|linearized.*adjunction` in CategoryTheory:
  zero hits.
- Project rg: `mapModAdjunction|def-sfb-modobj-linearized-adjunction` in
  `lean/WeilConjectures` and `lean/Sheaf`: the exact match is
  `ProjectionFormula.lean:475`; the other `Adjunction.mapModAdjunction` in
  `MapMod.lean:276` concerns transport along monoidal functors and is distinct.
- `dag/lean_names_upstream.json` search for `mapModAdjunction|smul_comp_eq_iff`:
  no hits, illustrating that the live source is newer than this name index.
- Live source retrieval with `scompile.py --source` confirmed the exact same
  declaration, helper equivalence, and dependency constructions.

Validation: this is an existing-only attachment. Per brief-stage2 section 1,
there is no new Lean file to compile; the delivery dry run validates the
existing binding. No proof or data definition was added or changed.

## Second reading by N0

A second in-thread reading compared the unchanged node, both current blueprint
files, and the complete upstream `mapModAdjunction` construction and its
`smul_comp_eq_iff` helper. The left/right functor order agrees with the source:
left functor from `Mod C (S.obj B)` to `Mod D B`, right functor in reverse.
The two action formulas are precisely those already recorded by the two
linearization dependency nodes. Forward and inverse hom maps use `adj` itself,
and both naturality fields use its naturality. In particular the construction
does not silently specialize to G = S. The inherited universes introduce no
extra equality. No mismatch was found and no statement correction was made.
This is a worker rereading, not a claim of an independent second agent review;
the dispatcher prohibits spawning another agent and the maintainer supplies
the independent review.
