## Worker report

Q79 states `lem-trf-flat-relative-associated-specialization`, Stacks Tag 0GSI,
without changing its mathematical statement or its stage-1 split. The previous
attempt concerned the superseded stage-1 assignment; this delivery is stage 2.
No assertion is proved. The main theorem has one `sorry`; all definitions have real data.
There are two modules:

- `Sheaf.AlgebraicGeometry.RelativeAssassin` defines associated points of an arbitrary
  module sheaf and its fibrewise relative assassin.
- `Sheaf.AlgebraicGeometry.FlatRelativeAssociatedSpecialization` constructs the reduced
  point closure's morphism to the base and its fibre's morphism to the ambient scheme,
  then states the pointwise specialization theorem and both dimension equalities.

I read the entire item, all twelve statement dependencies and their recorded signatures,
the declarations' sources (using `scompile.py --source` for published modules absent
from the older source checkout), Stacks `more-morphisms.tex` at
`lemma-associated-point-specializes` (0GSI), and `divisors.tex` at
`definition-relative-assassin` (05AT). The second paragraph of 0GSI explicitly supplies
the component-dimension equality in the node. There is no statement correction or dispute.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

1. Schemes and the morphism are `{X S : Scheme.{u}} (f : X ⟶ S)`;
   `[LocallyOfFiniteType f]` is exactly locally of finite type, without a global
   quasi-compactness assumption.
2. The module is `(F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]`.
   These are quasi-coherence and finite type, independently. No coherence, finite
   presentation, or Noetherian assumption replaces them.
3. `f.fiber s`, `f.fiberι s`, and `(Scheme.Modules.tensorPullback (f.fiberι s)).obj F`
   are precisely the scheme-theoretic fibre, its projection, and `F_s`.
4. `Scheme.Modules.associatedPoints` tests membership of
   `IsLocalRing.maximalIdeal (X.presheaf.stalk x)` in
   `RingTheory.annihilatorAssociatedPrimes` of the module stalk supplied by
   `RingedSpace.moduleStalkFunctor`. The ring is the local ring of the fibre when
   this definition is applied to the fibre. This is element-annihilator association,
   without a radical or a Noetherian restriction.
5. `Scheme.Modules.relativeAssassin f F` evaluates that predicate at `f.asFiber x`
   on `f.fiber (f x)`, with the prescribed tensor pullback. Thus
   `(y : X) (hy : y ∈ Scheme.Modules.relativeAssassin f F)` is the relative
   associated-point hypothesis; `t` is written explicitly as `f y`.
6. `f.associatedPointClosureToBase y` has domain
   `(Scheme.IdealSheafData.vanishingIdeal ⟨closure {y}, isClosed_closure⟩).subscheme`.
   This is the actual reduced induced closed structure on the closure, not an
   arbitrary integral scheme or a hypothesized substitute. Its morphism is
   `.subschemeι ≫ f`. The closure is nonempty and irreducible, and the vanishing
   ideal gives a reduced scheme, so it is the specified integral closed subscheme.
7. `(s : S)` is arbitrary and `Y_s` is `(f.associatedPointClosureToBase y).fiber s`.
   `C : Set Y_s` together with `hC : C ∈ irreducibleComponents Y_s` is an
   irreducible component, with its subspace topology.
8. `(x : Y_s) (hx : IsGenericPoint x C)` gives the component generic point in the
   fibre itself. Its ambient image is `f.associatedPointClosureFiberToAmbient y s x`,
   where the map is exactly `Y_s → Y → X`.
9. `hflat` is `Module.Flat` over the base local ring at that ambient image's image
   under `f`. The module is the stalk of `F` at the ambient image with scalars
   restricted by `ModuleCat.restrictScalars (f.stalkMap ...).hom`. This uses the
   canonical structural local-ring action. Flatness is required only at this point;
   the affine-local global predicate `F.IsFlatOver f` would be strictly stronger
   and is deliberately not substituted.
10. The first conclusion asserts that the ambient image of `x` belongs to
    `Scheme.Modules.relativeAssassin f F`.
11. `topologicalKrullDimAt x = topologicalKrullDim C` renders the first dimension
    equality, in the topology of the fibre `Y_s`.
12. `topologicalKrullDim C = topologicalKrullDim ((f.associatedPointClosureToBase y).fiber
    (f y))` renders `dim C = dim(Y_t)`. Both dimensions take values in `WithBot ℕ∞`;
    no finite dimension, nonnegative integer, or extra equidimensionality datum
    is assumed.

Dependency declarations and modules used:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `WeilConjectures.AlgebraicGeometry.Coherent`: the node's recorded coherent-module
  interface and its public Mathlib `SheafOfModules.IsQuasicoherent` and
  `SheafOfModules.IsFiniteType`. Only the latter two notions occur in this theorem.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`, `asFiber`.
- `WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes`:
  `RingTheory.annihilatorAssociatedPrimes`.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor`; for the sheaf specialization the shared
  `WeilConjectures.Algebra.Homology.ModuleStalkFunctor` declaration
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor` is used as the node instructs.
  Its owning node `def-pc-module-stalk-functor` is added to statement dependencies.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `Scheme.Modules.IsFlatOver`, read as the global affine-local notion; the theorem's
  pointwise hypothesis instead directly uses `Module.Flat`, not a duplicate definition.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`;
  the domain of the closure map is constructed, not assumed integral as new input.
- `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`.
- `WeilConjectures.AlgebraicGeometry.TensorPullback`: `Scheme.Modules.tensorPullback`.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme` and its public Mathlib
  constructions `vanishingIdeal`, `subscheme`, `subschemeι`. This existing landed node
  is added to statement dependencies to record the construction explicitly.
- The new `Sheaf.AlgebraicGeometry.RelativeAssassin` declarations listed above;
  `def-trf-relative-assassin` is added to statement dependencies.

All recorded proof-dependency modules that have statements are imported without
`public`, including the Mathlib modules for localization, component topology,
affine stalks, immersions, permanence and local Noetherianity. The four stage-1
valuative/base-change inputs without Lean records have no module to import;
they remain the already recorded proof dependencies. The theorem docstring
contains the complete ten-step natural-language proof from the node, including
its dependency references. No proof dependency is used as an axiom-like hypothesis.

Edge cases checked:

- `F = 0`: the annihilator of every stalk element is the whole ring, never a prime
  maximal ideal; the relative-assassin hypothesis has no witness.
- `X` or `S` empty: the required `y` cannot be supplied. No nonemptiness assumptions
  are inserted into definitions or the theorem.
- Empty `Y_s` or `s` outside the closure of `f y`: no component generic point can be
  supplied, so the theorem imposes no condition there. `Y_t` contains `y`.
- A field as base, the identity family, and `s = t`: these are retained, including
  zero-dimensional components. No strict specialization is assumed.
- Nonreduced ambient schemes, reducible fibres, and positive characteristic are
  retained. The closure is reduced by construction, not the entire `X` or fibre.
- A non-Noetherian valuation base is allowed. Global module flatness and flatness
  of `f` are absent. The source only needs flatness at the chosen point.
- Scheme and module universes follow the recorded `Scheme.Modules` and stalk APIs;
  all variables and universes are explicitly bound and `autoImplicit` is false.

Searches for the statement and notions:

- `msearch.py`, LeanFinder: “A relative associated point specializes at a flat fibre
  component generic point and dimension is preserved”: eight hits, including
  `Flat.generalizingMap`, going down and generic-point/stalk functoriality; no theorem
  states relative association plus these dimension equalities.
- `msearch.py`, Loogle: `AlgebraicGeometry.Flat, topologicalKrullDim`: zero hits.
- `msearch.py`, LeanSearch and LeanFinder: “Relative assassin of a quasi coherent
  module is the associated points of its fibre pullbacks”: eight hits each.
  LeanSearch returns algebraic associated primes, ordinary fibres, localization,
  and stalk restrictions; LeanFinder returns support and zero-locus constructions.
  These lack the sheaf-level associated-point/relative-assassin definition.
- `msearch.py`, grep: `relativeAssassin|relativeAssociated|IsAssociatedPoint`, over
  all Mathlib and its `AlgebraicGeometry` directory: zero hits.
- Direct `rg` of upstream `WeilConjectures` and project `lean/Sheaf` for relative
  assassin, associated points and the intended declaration names, and the prescribed
  grep of the item id in upstream sources, found no exact declaration. The project
  has `AlgebraicGeometry.associatedPoints X` for the structure sheaf only, used by
  the fibre-component lemma. That interface does not accept an arbitrary `F` and
  therefore does not give this node's notion; it is not redefined here.
- DAG searches for `relative assassin`, `associated point`, and their definition-node
  names find only the structure-sheaf associated-point node, no-embedded-points node,
  and the five trace-formula statements containing the notion inline.
  `tools/blueprint_refs.py search 'relative assassin'` and `search 'associated point'`
  both return zero blueprint nodes. The ancestor command returns
  `lem-trf-local-term-locality`.

Search digests are recorded in `searches.jsonl` and copied into the new node's
`mathlib_searches`. The new definition makes no assertion about association commuting
with base change; it only constructs the requested set. The general module-sheaf
associated-point formula is meaningful without quasi-coherence, and its specialization
to quasi-coherent modules is exactly the source's relative assassin.

Validation: both modules are compiled separately in dependency order through
`scompile.py`, including their canonical module names and the importing consumer.
The final delivery is also checked by `deliver2.py --no-push` before push.

## New nodes

`def-trf-relative-assassin` defines associated points of a module sheaf by the maximal
ideal's membership in element-annihilator associated primes of its stalk, and defines
the relative assassin by tensor pullback to the point's own scheme-theoretic fibre.
Its source is Divisors Tags 02OJ and 05AT. Its two definitions have real data and no
postponed proof. The node cites the existing fibre, tensor pullback, stalk, stalk
functor, associated-prime, module-category and quasi-coherence nodes. The three search
kinds and DAG/blueprint searches above show there was no definition accepting an
arbitrary module sheaf; the existing `associatedPoints X` only handles the structure
sheaf. The ancestry is the item's blueprint ancestor with the item prepended to `via`.

## Second reading by Q79

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
