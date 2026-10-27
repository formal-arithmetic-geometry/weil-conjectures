## Worker report

The module `Sheaf.AlgebraicGeometry.FinitePresentationStalkBasisSpread` states
`AlgebraicGeometry.RingedSpace.exists_free_neighbourhood_prescribed_stalk_basis`,
with `sorry` as its entire proof. No definitions, auxiliary theorems, new nodes,
or dependency repairs are needed. The node is unchanged except for `lean`.

Source read: Stacks Project, `modules.tex`, lemma-finite-presentation-stalk-free,
Tag 0B8J, lines 1537–1564. The proof starts with a chosen stalk basis and retains
its lifted sections throughout both shrinkings, giving precisely the prescribed
basis refinement in this node. The theorem docstring carries all six DAG proof
steps, including the finite-coordinate kernel argument and gluing of the inverse.

Hypothesis and conclusion correspondence:

- The general ringed space `(Y, O_Y)` is `Y : RingedSpace.{u}`. In particular,
  no locally ringed, scheme, Noetherian, or nonzero-ring hypothesis is imposed.
- The sheaf `G` of `O_Y`-modules is
  `G : ringedSiteModules (moduleRings Y)`. The first abbreviation is the recorded
  general-site category, transparently Mathlib `SheafOfModules`; `moduleRings`
  is the established structure sheaf with its commutativity forgotten.
- Finite presentation is exactly `[G.IsFinitePresentation]`, Mathlib's local
  finite cokernel presentation condition, not categorical finite presentability.
- The point and nonnegative rank are `y : Y` and `r : ℕ`. There is no positivity
  assumption on `r`.
- The prescribed basis is
  `b : Module.Basis (Fin r) (Y.presheaf.stalk y) ((moduleStalkFunctor Y y).obj G)`.
  This is the actual given basis, rather than a freeness or existence assertion.
- An open neighbourhood is `∃ (V : Opens Y) (hyV : y ∈ V)`.
- Its sections are `t : Fin r → G.val.obj (op V)`.
- Their prescribed germs are the first conjunct:
  `∀ i : Fin r, TopCat.Presheaf.germ G.val.presheaf V y hyV (t i) = b i`.
- The map has precisely domain
  `SheafOfModules.free (R := (moduleRings Y).over V) (ULift.{u} (Fin r))`
  and codomain `G.over V`. These are the standard free module and restriction
  on the slice site of opens contained in V. That slice site is canonically
  the opens of V, so this is the specified `O_V`-module map. The ULift changes
  only the universe of the finite indexing type, as in the recorded kernel lemma.
- `IsIso ψ` states that this module morphism is an isomorphism.
- The final equality
  `((G.over V).freeHomEquiv ψ (ULift.up i)).val (op (Over.mk (𝟙 V))) = t i`
  specifies `e_i ↦ t_i`. Mathlib's `freeHomEquiv` takes a map to the compatible
  family of images of its standard generators. Evaluating at the terminal open
  `V → V` gives its section over V; all other components are its restrictions.
  Thus this clause determines the requested map without introducing a new map
  construction or an arbitrary unrelated isomorphism.

Dependencies read and used:

- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`: `RingedSpace`,
  `PresheafedSpace.Hom`, `LocallyRingedSpace`, `LocallyRingedSpace.Hom` from
  def-weil-locally-ringed-space-morphism. Only the general ringed-space part is
  needed; the recorded module exports it.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  from def-weil-sheaf-of-modules-category, used explicitly in the binder.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` and `.Quasicoherent`:
  `SheafOfModules.IsFiniteType` and `SheafOfModules.IsFinitePresentation` from
  def-weil-pbc-module-finite-type-presentation. The former is the recorded module,
  and the latter actually declares finite presentation. Also read `.Free`:
  `SheafOfModules.free`, `ιFree`, `freeHomEquiv`, and their definitions.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.stalkObj`, `stalkAddMap`, `stalkMap_linear`, `stalkMap`,
  `stalkMap_id`, `stalkMap_comp`, `moduleStalkFunctor`, from
  def-weil-pbc-module-stalk. This recorded module is imported publicly.
  As directed by that node's note for sheaves on ringed spaces, the signature
  uses `AlgebraicGeometry.RingedSpace.moduleStalkFunctor` from
  `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`; its carrier is the same
  Mathlib stalk of `G.val.presheaf`. The germ map is Mathlib's existing map.
- `WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris` supplies the shared
  `AlgebraicGeometry.moduleRings` and exports the standard open restriction API.
- Proof-only import `WeilConjectures.Topology.FiniteTypeSurjectiveNearStalk`:
  `AlgebraicGeometry.RingedSpace.exists_surjective_neighbourhood_of_surjective_stalk`.
- Proof-only import
  `WeilConjectures.AlgebraicGeometry.FinitePresentationKernelSurjectionFiniteType`:
  `AlgebraicGeometry.RingedSpace.finitePresentation_kernel_surjection_finiteType`.
  Both full theorem signatures and proof docstrings were read.

Edge cases checked before writing: for `r = 0`, `Fin r` and its ULift are empty,
so both generator formulas are vacuous and the domain of ψ is the zero sheaf.
The conclusion therefore states exactly that G restricts to zero. An empty space
has no point y, so the pointwise statement is correctly vacuous. For a one-point
space this reduces to the given module basis. A zero stalk ring is allowed;
bases over it and the zero module are not excluded by a nontriviality assumption.
No module-local-ring assumption is needed. All universes and variables are
explicitly bound; no private definitions, local notation, or local instances occur.

Searches for an existing statement:

- msearch.py leanfinder: “A finite basis of the stalk of a finitely presented
  sheaf of modules extends to a free trivialization on an open neighbourhood”.
  Eight hits, including localGeneratorsDataOfIsFiniteType, existence of finite
  local generators, and finite presentation data. None asserts an isomorphism
  retaining prescribed stalk basis vectors.
- msearch.py loogle: `SheafOfModules.IsFinitePresentation, SheafOfModules.free`.
  Zero hits.
- msearch.py grep: `stalk.*(basis|free)|(basis|free).*stalk` in
  `Algebra/Category/ModuleCat`. Zero hits.
- msearch.py leansearch: “A prescribed finite basis of a stalk of a finitely
  presented sheaf of modules on a ringed space extends to an isomorphism with a
  finite free sheaf on an open neighbourhood”. Eight hits: finite presentation,
  free sheaves, finite type, and Tilde stalks. None is the statement here.
- rg on both `lean/WeilConjectures` and `lean/Sheaf` with
  `stalk.*(basis|free)|(basis|free).*stalk|stalk_basis|basis_spread`, followed by
  neighbourhood/basis and free/stalk refinements. Hits concern local generators,
  maps between free sheaves, affine stalk realizations, schemes/coherent sheaves,
  and the parent flat-fibre theorem. None gives the general ringed-space theorem
  with this prescribed basis. Searching the item id in `lean/WeilConjectures`
  gave no hit. The chosen theorem name and module name gave no hit in either
  project root, Mathlib, or `dag/lean_names_upstream.json`.

Validation: scompile.py compiled the delivered module both as the sandbox check
and under its library module name against the published server build. Both
checks passed without errors or non-sorry warnings. No statement is disputed.

## Second reading by Q142

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
