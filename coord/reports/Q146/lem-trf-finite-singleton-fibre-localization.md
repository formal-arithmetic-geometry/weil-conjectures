## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteSingletonFibreLocalization` states
`AlgebraicGeometry.Scheme.Modules.finite_singleton_fibre_neighbourhoods_and_module_stalk`.
Its only theorem has proof `sorry`; there are no new definitions or helper theorems.
The item node changes only in `lean`.

Source read: `literature/stacks-project/more-morphisms.tex`, lines 13551–13603,
Tag 05B8, `lemma-finite-morphism-single-point-in-fibre`, assertions (1) and (4)
and their proof. The source explicitly permits the direct cofinal-neighbourhood
proof as well as the affine localization argument. The module docstring preserves
all four steps of the node's affine localization proof and their dependencies.
No statement correction or disputed statement is needed.

Hypothesis and conclusion correspondence:

- Schemes and their morphism are `{Z Y : Scheme.{u}} (π : Z ⟶ Y)`, with arbitrary
  explicitly declared universe `u`.
- Finiteness is `[IsFinite π]`. There is no finite-presentation, Noetherian,
  reducedness, separatedness, or flatness hypothesis.
- The point is `(z : Z)` and its image `y` is written directly as `π z`, avoiding
  a second point or an equality transport.
- The singleton-fibre hypothesis is
  `π ⁻¹' ({π z} : Set Y) = ({z} : Set Z)`. It concerns the full underlying point
  fibre, and does not assert a singleton geometric fibre.
- Every open neighbourhood of `z` is `∀ U : Z.Opens, z ∈ U → ...`.
  The neighbourhood in the target is `∃ V : Y.Opens, π z ∈ V ∧ ...`.
  The containment is `π ⁻¹ᵁ V ≤ U`.
- The second conjunct quantifies over every `G : Z.Modules` and assumes only
  `G.IsQuasicoherent` for that conjunct. In particular it does not require finite
  type or finite presentation, and the neighbourhood assertion does not require G.
- The map is exactly
  `TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} π.base G.presheaf z`.
  Mathlib's definition and `stalkPushforward_germ` identify it as sending a germ of
  a section on V to the germ of that same section on the inverse-image open.
  Thus it is the canonical map specified by the node, not an arbitrary isomorphism.
- `IsIso` of that map states invertibility as an additive map. The following
  universally quantified scalar identity states linearity over `Y.presheaf.stalk (π z)`:
  `c (r • m) = (π.stalkMap z).hom r • c m`.
  Together these are precisely invertibility as an O_{Y,y}-module map: the inverse
  of an additive bijection respecting scalars also respects scalars.
- The source module in that identity is explicitly
  `(RingedSpace.moduleStalkFunctor Y.toRingedSpace (π z)).obj ((pushforward π).obj G)`.
  The result is annotated by the corresponding source-space module stalk
  `(RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj G`.
  The right-hand scalar action therefore is exactly restriction along `π.stalkMap z`.
- `Scheme.Modules.pushforward π` is Mathlib's module direct image, defined by
  `SheafOfModules.pushforward π.toRingCatSheafHom`. Its sections are G on inverse-image
  opens (`pushforward_obj_obj`), and the section action is restricted along `π.app V`.
  No alternative direct image or scalar action is introduced.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`;
  also read `IsIntegralHom` in the integral-morphisms module.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the recorded definition
  `Scheme.Modules.IsQuasiCoherentFiniteType` imports Mathlib's
  `SheafOfModules.IsQuasicoherent`. The item uses precisely that quasi-coherence
  predicate, not the finite-type conjunction (which would add a hypothesis).
  The Mathlib predicate's signature and local-presentation docstring were read.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the recorded
  `Scheme.Modules.tensorPullbackSectionAdjunction` and its full signature and
  section normalization were read. Its public upstream import retains Mathlib's
  `Scheme.Modules.pushforward`, the direct image used here; no pullback construction
  is copied or replaced.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor`. The current source was read
  through `scompile.py --source`, since the older local checkout lacks this module.
  Both stalks use its existing module structures.
- `WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk` supplies the existing
  instance `Module (X.presheaf.stalk x) (M.presheaf.stalk x)` required to elaborate
  the scalar identity. Its signature and implementation were read; this is the
  standard stalk action, not an added structure or hypothesis.
- `Mathlib.Topology.Sheaves.Stalks`: `TopCat.Presheaf.stalkPushforward` and
  `stalkPushforward_germ`, read in source; these provide the map and its normalization.

The stated proof dependencies are imported non-publicly: localized modules,
tensor-product definitions, affine module germ localization, affine spectra and
stalk localization, affine pushforward base change, affine morphisms, and integral
morphisms. The current affine-germ and affine-pushforward modules were also read
with `scompile.py --source`. The only unstated proof dependency is
`lem-trf-unique-prime-localization`, so it has no module to import yet.

Edge cases checked before writing:

- An empty Z has no z, so the statement imposes no false nonempty-fibre claim.
- U = top is allowed; U = bottom cannot contain z. V may be any suitable open,
  with no affine or quasi-compact restriction added to the conclusion.
- The zero module is included and its canonical map is an isomorphism.
- Identity morphisms and closed immersions satisfy the expected special cases.
- Nilpotent thickenings and inseparable finite maps with singleton point fibres
  are included; no injectivity, residue-field isomorphism or reduced fibre is assumed.
- G need not be finitely generated or coherent. No coefficient characteristic is fixed.
- All variables and universes are explicit; there are no local definitions,
  notations, instances, `let` binders, or `show ... from` in the statement.

Searches actually run:

- `msearch.py` LeanFinder, query `finite morphism singleton fibre Zariski pushforward
  module stalk canonical germ map is isomorphism`: eight results, including finite
  fibre cardinality, structure-sheaf stalk localization, and local finite type of
  stalk maps; no result states this module comparison with the neighbourhood clause.
- `msearch.py` Loogle, query `TopCat.Presheaf.stalkPushforward`: found the exact
  canonical additive map, its germ formula, and the isomorphism theorem for inducing
  maps. A finite singleton-fibre morphism need not be inducing, so that theorem is
  not an exact match for this item.
- `msearch.py` grep, query `stalkPushforward|pushforward.*stalk|stalk.*pushforward`,
  subdirectory `Topology`: five hits in `Mathlib/Topology/Sheaves/Stalks.lean`,
  giving the canonical map and germ formula, not the desired theorem.
- `msearch.py` LeanSearch, query `finite morphism singleton fibre pushforward stalk`:
  eight results, including `stalkPushforward`, finite-preimage-singleton, and structure
  sheaf stalk maps; no exact statement.
- Direct `rg` searches in Mathlib, upstream `WeilConjectures`, project `lean/Sheaf`,
  and `dag/lean_names_upstream.json` for the node id, singleton/finite fibres,
  pushforward/stalk combinations, and the proposed declaration name found no exact
  theorem or name collision. Upstream `SixFunctors/Finite/Stalk.lean` concerns
  geometric étale stalks and cannot replace this Zariski O-module statement.
  Project `ClosedPushforwardStalks.lean` supplies the closed-embedding special case;
  `FinitePushforwardModuleFinitePresentation.lean` states finite-presentation
  equivalences with extra finite-presentation assumptions. Neither is the item.

Validation: `scompile.py Q146 lem-trf-finite-singleton-fibre-localization` compiled
both the sandbox and final library-path version successfully with no warnings.
An initial source-stalk scalar-instance elaboration failure was repaired by importing
its existing upstream instance; no new declaration or assumption was introduced.

## Second reading by Q146

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
