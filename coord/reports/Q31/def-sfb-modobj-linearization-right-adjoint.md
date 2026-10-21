## Worker report

The node is realized exactly by existing declaration
`CategoryTheory.Functor.ProjectionFormula.mapModRight` in
`WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula` (source lines 424–450).
No Lean module is added. Only the item's `lean` field is changed; its statement,
dependencies, and proof remain verbatim. There is no statement dispute or dependency repair.
The local source and the current live server source, read with
`scompile.py --source WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`,
agree on the definition and every clause below.

Hypotheses and clauses, with `pf` denoting the node's π:

- Monoidal categories C and D: `{C : Type u₁} [Category.{v₁} C]
  [MonoidalCategory C]` and `{D : Type u₂} [Category.{v₂} D]
  [MonoidalCategory D]`; all four universes are independent.
- Strong monoidal S and arbitrary P: `{S : D ⥤ C} [S.Monoidal]
  {P : C ⥤ D}`. The assumed coherent projection formula is
  `(pf : S.ProjectionFormula P)`, the recorded dependency declaration itself.
- Right adjoint with counit c: `{G : D ⥤ C} (adj : P ⊣ G)`;
  c is `adj.counit`. G is not required to be S or to be monoidal.
- The specified mate θ is `pf.theta adj L N`, defined by
  `adj.homEquiv _ _ ((pf.iso L (G.obj N)).hom ≫ L ◁ adj.counit.app N)`.
  `homEquiv_symm_theta` and `map_theta_comp_counit` explicitly verify its transpose.
- The coefficient monoid is `(B : D) [MonObj B]`. The target coefficient is
  `S.obj B` with Mathlib's transported `Functor.monObjObj`; its unit and
  multiplication are `ε S ≫ S.map η` and `μ S B B ≫ S.map μ`, respectively.
- A B-module N is `(N : D) [ModObj B N]`, or bundled `(N : Mod D B)`.
  `pf.rightSMul adj B N` is exactly
  `pf.theta adj B N ≫ G.map γ[B,N]`. `pf.rightModObj adj B N` installs this
  as the action and proves `one_smul` and `mul_smul`. Thus the module structure
  has exactly the source's action, rather than an arbitrary chosen structure.
- A B-linear f is `(f : N ⟶ N')` in `Mod D B`. `mapModRight` constructs its
  image with `Mod.Hom.mk' (G.map f.hom)` and verifies action compatibility
  using `Mod.act_hom` and `theta_natural_right`. No additional linearity
  hypothesis is required of G.
- The displayed functor is precisely
  `pf.mapModRight adj B : Mod D B ⥤ Mod C (S.obj B)`.
  `mapModRight_obj_X`, `mapModRight_map_hom`, and `mapModRight_obj_smul`
  identify its object, map, and action with those specified in the node.
- Commutation with the forgetful functors is the existing equality
  `pf.mapModRight adj B ⋙ Mod.forget (S.obj B) = Mod.forget B ⋙ G`, named
  `mapModRight_comp_forget`. It is strict equality, as in the node's last proof step.

Dependency declarations read and used:

- `def-sfb-projection-formula`: `CategoryTheory.Functor.ProjectionFormula`, in
  `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`. Read its
  docstring and all fields: `iso`, `natural_left`, `natural_right`, `unit`, `assoc`.
- `sk-def-sfb-module-objects`: `CategoryTheory.Mod`, in
  `Mathlib.CategoryTheory.Monoidal.Mod`. Read `ModObj`, its two axioms,
  `IsModHom`, bundled `Mod`, `Mod.Hom`, and `Mod.forget`. Tensoring is the
  canonical self-action of a monoidal category; no separate encoding is used.
- `def-sfb-modobj-transport`: its current `lean.declarations` and closed audit
  identify `CategoryTheory.Functor.mapMod`, `modObjObj`, and `act_mapMod_obj`
  in `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod`. Their full signatures
  and docstrings were read. For the coefficient monoid, the same existing
  Mathlib `Functor.monObjObj`, `Functor.obj.η_def`, and `Functor.obj.μ_def`
  implement the monoid-transport clause. No module transport along G is assumed.

Source and edge cases:

Read the current blueprint file at
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/`
`sk-def-sfb-transport/def-sfb-modobj-linearization-right-adjoint.md` and the
item's complete six-step proof. The existing mate coherences, module laws,
and linear-map construction implement precisely those steps.
No additive, abelian, symmetric, exactness, closedness, nonzero, or size-equality
hypotheses occur. The unit coefficient monoid is admitted, as are zero objects
and zero coefficient monoids wherever available. Empty categories introduce no
extra case restriction: the input monoid B is an object as required. The identity
functors with their identity adjunction recover the original module action.
Arbitrary adjunctions and unrelated S and G remain allowed.

Searches for an existing notion:

- `msearch.py ... leanfinder "A projection formula linearizes the right adjoint
  into a functor on module objects using its counit mate"`: 8 hits, concerning
  `ModuleCat.RestrictionCoextensionAdj` counits, `ModuleCat.adj`,
  `ModuleCat.monoidalClosed_pre_app`, and representation coinduction; none is
  this general construction.
- `msearch.py ... loogle "CategoryTheory.Adjunction.rightAdjointLaxMonoidal_μ"`:
  one valid hit in `Mathlib.CategoryTheory.Monoidal.Functor`; related monoidal
  adjunction infrastructure, not a projection-formula module linearization.
- `msearch.py ... grep "mapModRight|rightModObj|rightAdjointLaxMonoidal"
  CategoryTheory`: five Mathlib hits, all generic right-adjoint lax monoidal
  infrastructure in `Monoidal/Functor.lean`.
- `rg -n 'mapModRight|linearization.right|linearization.*adjoint|def-sfb-modobj-linearization-right-adjoint'
  lean/WeilConjectures lean/Sheaf`: exact upstream `mapModRight` at line 427,
  its mate at 332, action at 399, module structure at 405, and forgetful
  equality at 449. No duplicate Sheaf construction was found.
- `grep -rn 'def-sfb-modobj-linearization-right-adjoint' lean/WeilConjectures`:
  no blueprint-id annotation; the construction is present under its Lean name.
- `rg -n 'mapModRight|rightModObj' dag/lean_names_upstream.json`: no indexed hit;
  direct source lookup and the current server source establish availability.

Validation: the dry run passed preflight and server compilation. Both delivery
commands compile server-side `#check @...`
probes for every declaration recorded in `lean.declarations`; no new module
requires compilation. The maintainer performs the independent review.

## Second reading by Q31

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
