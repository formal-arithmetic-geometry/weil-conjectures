## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeFlatnessSourceCover` states
`AlgebraicGeometry.relative_flatness_source_cover`. Its single conclusion is the
conjunction of the pointwise equivalence and the covering-family consequence of
`lem-trf-relative-flatness-source-cover`. Its proof is exactly `sorry`; no new
notion, construction, auxiliary theorem, dependency node, or statement correction
is introduced. Only the item's `lean` field changes.

Read the current node, every statement dependency's statement and record, and the
full source signatures and docstrings used below. The mathematical source read is
`literature/stacks-project/morphisms.tex`, `definition-flat` (Tag 01U3),
`lemma-flat-module-characterize` (Tag 01U4), and `lemma-flat-permanence` (Tag 02JZ).
Tag 02JZ states the pointwise equivalence and its consequence for one surjective
flat morphism; applying that same pointwise argument to a chosen preimage under a
member of a jointly surjective family gives exactly the node's family clause.
The additional scheme-flatness consequence of Tag 02JZ is not part of this node.

Hypothesis and clause correspondence:

- Schemes and the morphism `f : Y → S`: `{Y S : Scheme.{u}} (f : Y ⟶ S)`.
- The quasi-coherent `O_Y`-module: `(G : Y.Modules) [G.IsQuasicoherent]`.
  This is the existing quasi-coherence notion, not coherence or finite type.
- The pointwise source and its morphism: the first conjunct quantifies
  `∀ (X : Scheme.{u}) (h : X ⟶ Y) (x : X)`. The point `y` is the term `h x`.
- Flatness of `h` at this point only: `(h.stalkMap x).hom.Flat → ...`.
  It does not require `Flat h`, surjectivity, or flatness of `f`.
- Flatness of `G` over `S` at `y`: `Module.Flat (S.presheaf.stalk (f (h x)))`
  applied to the result of `ModuleCat.restrictScalars (f.stalkMap (h x)).hom`
  on `(RingedSpace.moduleStalkFunctor Y.toRingedSpace (h x)).obj G`.
  The base scalar action is the actual stalk map of `f`.
- The pullback is exactly `(Scheme.Modules.tensorPullback h).obj G`, as required
  by `def-pc-module-pullback`. It is not the other `Modules.pullback` functor.
- Flatness of this pullback at `x` over `S` is the second `Module.Flat`, on its
  `RingedSpace.moduleStalkFunctor X.toRingedSpace x` stalk restricted along
  `((h ≫ f).stalkMap x).hom`; its base is `S.presheaf.stalk ((h ≫ f) x)`.
  Thus the map and base point belong to the composite specified in the node.
- The two pointwise conditions are related by `↔`, not by just one implication.
- An arbitrary family: the second conjunct quantifies `∀ (I : Type v)` with
  `X : I → Scheme.{u}` and `h : ∀ i : I, X i ⟶ Y`. The index universe `v` is
  explicit and independent, without finiteness, smallness or nonemptiness.
- Every family member is flat: `(∀ i : I, Flat (h i)) → ...`.
- Joint surjectivity is exactly
  `(∀ y : Y, ∃ (i : I) (x : X i), h i x = y) → ...`.
  It does not require any individual member to be surjective.
- Global flatness on `Y`: `G.IsFlatOver f`, the dependency's affine-section
  definition. Global flatness on every source is
  `∀ i : I, ((Scheme.Modules.tensorPullback (h i)).obj G).IsFlatOver (h i ≫ f)`.
  Again the conclusion is an equivalence.
- No quasi-compactness, finite-presentation or Noetherian hypothesis appears.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its `Hom`,
  available through `Mathlib.AlgebraicGeometry.Morphisms.Flat`.
- `WeilConjectures.AlgebraicGeometry.Coherent`: the docstring explicitly identifies
  the quasi-coherence clause of `pqf-def-coherent` with the existing
  `SheafOfModules.IsQuasicoherent`, which is the class used on `G`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, and the
  stalk interpretation `Flat.iff_flat_stalkMap`. Its public dependencies provide
  `Mathlib.RingTheory.RingHom.Flat`'s `RingHom.Flat` and `Module.Flat`, as recorded
  by `def-weil-pbc-flat-ring-map`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `AlgebraicGeometry.Scheme.Modules.IsFlatOver`.
- `WeilConjectures.AlgebraicGeometry.TensorPullback`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor`, the existing module stalk
  used by the statement and by the recorded stalkwise criteria.

Proof-plan imports are non-public: `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`
for `Module.FaithfullyFlat.of_flat_of_isLocalHom` (and the public basic descent
results); `WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk` for
`Scheme.Modules.exists_tensorPullback_stalk_iso`;
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde` for the recorded
`Scheme.Modules.isQuasicoherent_pullback`; and
`Sheaf.AlgebraicGeometry.RelativeFlatModuleStalk` /
`Sheaf.AlgebraicGeometry.RelativeFlatOfStalks` for
`AlgebraicGeometry.relative_flat_module_stalk` /
`AlgebraicGeometry.relative_flat_of_stalks`.
The helper `lem-trf-flatness-faithfully-flat-extension` has no recorded Lean
statement at the time of this delivery, so there is no module to import for that
proof dependency. It is named in the complete proof docstring, as in the DAG.
The recorded quasi-coherence lemma uses the adjoint `Modules.pullback`; stage 3
transports it across the canonical equivalence of the two left adjoints for the
tensor pullback. This does not add a quasi-coherence assumption to the theorem.

Edge cases checked before writing: a zero module gives flat zero stalks; identity
`h` gives the same relative flatness after canonical pullback identification;
empty `X` has no pointwise tests; empty `Y` has no pointwise tests and the global
affine tests have zero sections. An empty family can be jointly surjective
exactly when `Y` is empty, in which case both global sides hold. A family can
have empty members, or have no individually surjective member. No restriction
on characteristic or a nonzero base ring is present. The schemes share an
arbitrary ambient universe `u`, while `I` has its own arbitrary universe `v`.
All variables and both universes are explicitly bound; `autoImplicit` is false.
There is no node fault or statement dispute.

Searches actually run (full msearch output retained in sandbox `research/`):

- `msearch.py` LeanFinder query: `A quasi-coherent module is flat over the base at
  a point if and only if its pullback along a morphism flat at that point is flat
  over the base`. Eight hits: scheme flatness, stalk characterization and base
  change stability. None is this relative-module equivalence.
- `msearch.py` Loogle query: `"Flat", "pullback"`. Seven hits: site-functor
  exactness, reduced/integral scheme pullbacks, and faithfulness of scheme
  pullback with extra hypotheses. None states this node.
- `msearch.py` grep query: `flat.*pullback|pullback.*flat|flat.*descent`, restricted
  to `AlgebraicGeometry`. Sixteen hits in scheme-morphism and geometric-property
  files. None states the module-flatness source-cover assertion.
- `msearch.py` LeanSearch query: `Flatness of a quasi coherent module over a base
  is detected after pullback along flat source morphisms`. Eight hits, including
  `Module.Flat.of_flat_tensorProduct` and `Module.Flat.iff_flat_tensorProduct`.
  These are same-base ring-module results, not this scheme-stalk statement.
- `rg` of `WeilConjectures/AlgebraicGeometry` and `lean/Sheaf/AlgebraicGeometry`
  for `relative.flatness|flat.*source.cover|flat.*pullback|pullback.*flat` finds
  other flat-base-change and descent results, including affine-section
  `Modules/FiniteDescent.lean` assertions, not the pointwise and arbitrary-family
  conjunction. The targeted `source.?cover|relative_flatness.*(flat|pullback)|
  flat.*source.*cover` search also found no matching declaration.
- `grep -rn` of the item's exact id in upstream `WeilConjectures/` has no hit.
  `rg` of `relative_flatness_source_cover|RelativeFlatnessSourceCover` in
  `dag/lean_names_upstream.json`, upstream `WeilConjectures/`, and shared
  `lean/Sheaf` has no hit. The chosen declaration name is unused.

Validation: the prescribed `scompile.py Q25 lem-trf-relative-flatness-source-cover`
compiled the delivered file in both sandbox and library contexts, approximately
4.6 and 4.5 seconds respectively, with no errors and no warnings. Only this
single file was compiled; no global build was run. The UTC date in the Lean
record is taken from `date -u +%F` on this machine.

The dispatcher reported a previous preflight rejection concerning the existing
Q91 split. There were no saved modules or node copies in this sandbox. This
packet starts from the current reviewed shared node and adds only its Lean
record; it does not redeliver, remove, or alter any part of that split.

## Second reading by Q25

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
