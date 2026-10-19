## Worker report

States `AlgebraicGeometry.Scheme.Modules.elementary_devissage_flatness` in
`Sheaf.TraceFormula.ElementaryDevissageFlatness`. Its sole theorem has proof `sorry`;
there are no new definitions, new nodes, or dependency repairs. The existing node is
changed only in `lean`. Source read directly: `literature/stacks-project/flat.tex`,
Tag 057U (`lemma-devissage-flat`, lines 687–762), together with the elementary
devissage data in Tag 057S (`lemma-elementary-devissage`, lines 493–533).

Hypothesis and clause correspondence:

- Schemes and morphisms: `{X S : Scheme.{u}}`, `f : X ⟶ S`, and
  `[LocallyOfFiniteType f]`. There is no `LocallyOfFinitePresentation f` assumption.
- Finite-type quasi-coherent F: `_hF : F.IsQuasiCoherentFiniteType`, the recorded
  conjunction in `Sheaf.AlgebraicGeometry.CoherentFiniteType`. This does not assume
  coherence or finite presentation. The separate recorded `IsFiniteType` notion
  is exactly the second conjunct of this definition.
- The marked original point and its base image: `x : X`, with `s` represented by
  `f x`. The hypothesis `hx` says that the stalk of the actual tensor pullback
  of F along `f.fiberι (f x)` at `f.asFiber x` is not subsingleton. Thus it says
  precisely that x belongs to the support of F_s on the canonical scheme fibre.
- Local dimension: `n : ℕ` and `_hn` equate `topologicalKrullDimAt` of the point
  `⟨f.asFiber x, hx⟩` in the support subtype with `(n : WithBot ℕ∞)`. This is
  local topological dimension of the support, rather than dimension of the
  ambient fibre or of the closure of the point. It is the dependency's formula.
- The four affine schemes are explicit `X' Z' Y' S' : Scheme.{u}`, each with
  `[IsAffine ...]`; their six maps and three marked points are explicit binders.
- Elementary pointed etale neighbourhoods: `[Etale g]`, `[Etale e]`, `_hg`, `_he`,
  and the `IsIso` instances on the canonical `residueFieldMap` of g and e.
- The commuting diagram is `_hfg : g ≫ f = f' ≫ e` and
  `_hπ : i ≫ f' = π ≫ h`. The second equality is the over-S' condition in the
  elementary devissage diagram explicitly imported by the natural statement.
- The finitely presented closed immersion is `[IsClosedImmersion i]` with
  `[LocallyOfFinitePresentation i] [QuasiCompact i] [QuasiSeparated i]`.
  These are the recorded meaning of finite presentation of a morphism. The last
  two properties also follow from being a closed immersion, so impose no extra
  restriction beyond the stated finite-presentation hypothesis.
- Finite π: `[IsFinite π]`. The structure morphism on Z' is `π ≫ h`, identified
  with `i ≫ f'` by `_hπ`.
- Finite-type quasi-coherent G: `_hG : G.IsQuasiCoherentFiniteType`.
- The given module isomorphism is `_hiso : Nonempty ((pushforward i).obj G ≅
  (tensorPullback g).obj F)`. This is an existence of an isomorphism between two
  fully constructed modules, not an unspecified pullback or pushforward.
- Smooth relative dimension and geometric integrality:
  `[SmoothOfRelativeDimension n h] [GeometricallyIntegral h]`. The latter tests
  integrality after every field-valued base change, as the dependency does.
- The marked relations are `_hi : i z' = x'`, `_hs : h (π z') = s'`, and
  `_hfibre : (π ⁻¹' ({π z'} : Set Y')) = {z'}`; y' is consistently `π z'`.
  These and `_hπ` also imply `f' x' = s'`.
- Pure transcendence is `_hpure`, the recorded
  `Algebra.IsPurelyTranscendentalExtension` evaluated with the explicit canonical
  algebra structure `(h.residueFieldMap (π z')).hom.toAlgebra`. The base residue
  field is written at `h (π z')`, equal to s' by `_hs`. There is no arbitrary
  algebra structure and no `let` binder in the statement.
- Neighbourhood condition (1) is `∃ U : X.Opens, x ∈ U ∧
  ((tensorPullback U.ι).obj F).IsFlatOver (U.ι ≫ f)`.
- Condition (2) is the same expression on Z', G, z', with structure `π ≫ h`.
- Condition (3) is the same expression on Y', `(pushforward π).obj G`, `π z'`, h.
  Tensor pullback along the open immersion is restriction of the module; the
  existing relative flatness definition is applied to that restriction.
- The first two conjuncts assert `(1 ↔ 2) ∧ (2 ↔ 3)`, exactly their equivalence.
- Stalk condition (a) is `Module.Flat (S.presheaf.stalk (f x))` of the actual
  `RingedSpace.moduleStalkFunctor ... x` applied to F, with scalars restricted by
  `ModuleCat.restrictScalars (f.stalkMap x).hom`.
- Condition (b) uses the same construction on G at z' along `(π ≫ h).stalkMap z'`.
  Its base stalk is at `(π ≫ h) z' = h (π z') = s'`.
- Condition (c) uses the stalk of `(pushforward π).obj G` at `π z'`, restricted
  along `h.stalkMap (π z')` to that same base local ring.
- The last two conjuncts assert `(a ↔ b) ∧ (b ↔ c)`. No equivalence between
  neighbourhood flatness and single-stalk flatness is asserted.

Dependency declarations and source inspection:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map` (the underlying scheme and affine-spectrum conventions).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`; `Mathlib.AlgebraicGeometry.Fiber` supplies
  `Scheme.Hom.fiber`, `fiberι`, and `asFiber`, the canonical fibre specialization.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`.
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`:
  `SheafOfModules.IsFiniteType`; `...Sheaf.Quasicoherent`: `IsQuasicoherent`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; `...FinitePresentation`:
  `LocallyOfFinitePresentation`; `...Etale`: `Etale`; `...Smooth`:
  `SmoothOfRelativeDimension`; `...Finite`: `IsFinite`; `...ClosedImmersion`:
  `IsClosedImmersion`; `...Affine`: `IsAffineHom`; `...Properties`: `IsIntegral`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`; `...Geometrically.Integral`:
  `AlgebraicGeometry.GeometricallyIntegral`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`.
- `Sheaf.FieldTheory.PurelyTranscendentalExtension`:
  `Algebra.IsPurelyTranscendentalExtension`.
- `Sheaf.TraceFormula.ElementaryModuleDevissage`:
  `AlgebraicGeometry.Scheme.Modules.exists_elementary_module_devissage`.
  This is imported for its exact data interface; the hypothesis list mirrors
  its output, using the recorded conjunction for finite type and quasi-coherence.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `tensorPullbackSectionAdjunction`, publicly importing the actual upstream
  `AlgebraicGeometry.Scheme.Modules.tensorPullback` from
  `WeilConjectures.AlgebraicGeometry.TensorPullback`. This recorded dependency is
  imported directly; the statement uses its unchanged canonical tensor functor.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `AlgebraicGeometry.Scheme.Modules.IsFlatOver`.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor`; Mathlib `ModuleCat.restrictScalars`
  fixes all base actions explicitly.
- Proof-only imports: `Sheaf.AlgebraicGeometry.AffineCoverModuleTensorFlatCriterion`
  (`AlgebraicGeometry.affine_cover_module_tensor_flat_criterion`),
  `Sheaf.TraceFormula.EtaleLocalRingFlatness` (`AlgebraicGeometry.etale_local_ring_flatness`),
  `Sheaf.AlgebraicGeometry.RelativeFlatnessSourceCover`
  (`AlgebraicGeometry.relative_flatness_source_cover`),
  `WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange`
  (`Scheme.Modules.affinePushforward_baseChange`),
  `WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks`
  (`AlgebraicGeometry.closedImmersion_pushforward_stalks`),
  `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen` (`Scheme.Hom.isOpenMap`),
  and `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`
  (`Scheme.Modules.isQuasicoherent_pullback`).
  `lem-trf-finite-singleton-fibre-localization` has no recorded module at the
  inspected base, so there is no proof import to add yet; it remains cited in
  the complete six-step proof docstring. It is not needed to type this statement.
- Source modules absent from the local checkout were read with the authorized
  `scompile.py --source` interface: TensorPullback, AffinePushforwardBaseChange,
  ModuleStalkFunctor, and the current Tilde source.

Edge cases checked: n = 0 is admitted; no characteristic or Noetherian assumption
is imposed. Nonempty marked points exclude empty schemes in exactly the way the
node does. The zero F case is excluded by the node's explicit support hypothesis,
not by an extra nonzero-module hypothesis. Support dimension uses its subspace
topology. Neighbourhoods need not be affine and need not have globally flat F;
only the restricted sheaf is tested. Fibres are scheme fibres over residue fields,
not underlying set-theoretic fibres; the singleton condition on π is deliberately
a set-theoretic fibre. The empty transcendence basis is allowed by the existing
pure-transcendence definition. There is one arbitrary common scheme universe u,
with no size equality added and no bound variables inferred automatically.

Searches for an existing statement:

- `msearch.py ... leanfinder` query: "relative flatness near a point and stalk
  flatness equivalent under elementary etale module devissage and finite
  pushforward". Eight hits: `Flat.iff_flat_stalkMap`, `Flat.stalkMap`,
  `Flat.of_stalkMap`, `instFlatAtPrime`, `RingHom.Etale.propertyIsLocal`,
  `RingHom.Flat.propertyIsLocal`, `Algebra.mem_etaleLocus_iff`, `Algebra.etaleLocus`.
  None states the two module-devissage equivalences.
- `msearch.py ... loogle 'Module.Flat, AlgebraicGeometry.Etale'`: zero hits.
- `msearch.py ... grep 'devissage|flat.*finite.*pushforward' AlgebraicGeometry`:
  zero Mathlib hits.
- `rg -n 'devissage|elementary.*flatness'` in both the upstream WeilConjectures
  source and the side Sheaf library: existing elementary devissage and finite
  presentation statements, plus proof references to this item; no existing
  flatness statement. The new statement name is unused.
- Search for the exact item id in the upstream source and
  `dag/lean_names_upstream.json`: no declaration hit. In side sources only
  downstream proof docstrings reference it. No new notion required a definition.

No statement correction or disputed statement. The over-S' equality is written
out from the explicitly cited elementary-devissage data and source diagram.
Compilation: `scompile.py Q01 lem-trf-elementary-devissage-flatness
<.../ElementaryDevissageFlatness.lean>` passed both sandbox and library-path
checks, with no diagnostics (2.8 s and 3.3 s respectively).

## Second reading by Q01

The dispatcher brief explicitly prohibits spawning another agent and assigns the
independent review to the maintainer. This section records a worker cross-check,
not an independent agent review. I reopened the natural statement and compared
every hypothesis with the signature, using the sibling finite-presentation
statement only as an interface template. I checked especially the support
subtype, canonical residue-field algebra, over-S' equality, absence of finite
presentation of f, all three base actions, and the two separate equivalence
chains. No mismatch was found. The independent maintainer review remains part
of the delivery process.
