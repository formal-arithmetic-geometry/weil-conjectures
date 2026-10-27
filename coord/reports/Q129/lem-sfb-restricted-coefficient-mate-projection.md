## Worker report

Module `Sheaf.Paper.RestrictedCoefficientMateProjection` states the restricted actual
coefficient push mate's geometric transpose, its equality with the regular-coefficient
projection arrow, and naturality in every unbounded internal-module complex. The theorem
is postponed with `sorry`; the helper definitions contain actual constructions.

Hypotheses and objects, clause by clause:

- `ℓ p : ℕ`, `Fact ℓ.Prime`, `k : Type u`, `Field k`, `CharP k p`, `_hp : 0 < p`
  and `_hne : p ≠ ℓ` give the stated prime and positive-characteristic base field.
- `X Y : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))` and `f : X ⟶ Y`
  give schemes and a morphism over exactly this field. Each structure morphism has
  `LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated`, rendering separated finite type.
- `R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}`, with `MonObj` and
  `IsCommMonObj` on both, are arbitrary commutative condensed rings in the recorded
  ring-object encoding. `a : R ⟶ S` and `IsMonHom a` are the coefficient homomorphism.
- `∀ T : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a T))`
  is precisely the given exactness of scalar extension on every scheme (scalar extension
  is already additive and right exact). The coefficient maps and their compatibility
  are the recorded canonical pullbacks from the point, never input arbitrary squares.
- `Modules R T`, `D a T`, `V a T`, `B₀ a T`, `B a T` are the existing internal module,
  total scalar extension, exact scalar restriction, restricted regular module, and its
  degree-zero complex from `Sheaf.Paper.InternalDerivedScalarComparisons`.
- `CondensedRing.moduleObjectDerivedPullback/Pushforward` are the recorded total derived
  geometric functors, and `derivedUpperStarLowerStarAdjunction` is their specified
  adjunction. The section-module `HasDerivedCategory` parameter chooses localizations
  for the comparison with sheaf modules, preserving the actual site Hom universe u and
  object universe u+1. It imposes no new geometric or cohomological hypothesis.
- `eX eY : TensorNormalization` and `TensorNormalized` specify exactly the balanced
  scalar/tensor maps e_X and e_Y of the statement: their ordinary component is fixed by
  the coequalizer comparison followed by symmetry, and the derived component is fixed
  by its computation-counit equation. Existence is supplied by the recorded
  `internal_scalar_pullback_normalization`; no unnormalized isomorphism is accepted.
- `regularPullback₀` is the actual ordinary restriction/pullback comparison at the
  regular S-module followed by the strong monoidal unit isomorphism. `regularPullback`
  uses exact geometric pullback, its localization factor, and its single-degree
  comparison to construct the stated canonical rho in degree zero.
- `scalarMate` and `restrictionPushIso` are typed presentations of the existing
  `derivedPushHom` and `derivedComapLowerStarIso`, respectively: their definitions
  merely unfold the already specified functor aliases.
- `restrictedMap` defines h by the four factors in the node, in Lean composition order:
  e_Y inverse, U_Y(gamma), d at T_X K, and G_R(e_X). Thus it has exactly the domain
  G_R K tensor C and codomain G_R(K tensor B).
- The first conjunct uses `.homEquiv.symm` to state the L_R/G_R transpose equality.
  Its right side is `internalDelta` (mu in the node's direction), then identity tensor
  `regularPullback.hom`, then the specified geometric counit tensor identity.
- The second conjunct identifies the same h with the recorded
  `ModuleRingedComparison.internalProjection` followed by G_R(identity tensor rho).
  This projection is explicitly defined as the adjunct of the same internalDelta and
  counit. The recorded module/ringed comparison identifies it with the precise
  ringed projection map of `lem-weil-pbc-ringed-projection-mate-exact`.
- The last conjunct is the naturality square for every `q : K ⟶ K'`, with the source
  action G_R(q) tensor identity and target action G_R(q tensor identity).

The module's docstring gives all four DAG proof steps, including the iterated-mate
identity, the restriction/geometric Hom-transpose comparison, the balanced-square
normalization and injectivity of the specified hom bijection. The flat square theorem
currently has no recorded Lean module; it is named as the future proof input and no
replacement assumption is introduced.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField`; the setting's geometric assumptions are
  explicit binders, while this theorem concerns the ambient unbounded category.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, whose underlying
  ring-object encoding is used, without assuming a topological presentation.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`:
  `coefficientMap`, its two compatibility equations, `CondensedRing.comapUpperStarIso`,
  `derivedPushHom`, `derivedComapLowerStarIso`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `condensedPullbackHom`, `coefficientPullbackIso`, `condensedPushforwardHom`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPullback`, `moduleObjectDerivedPushforward`;
  `Derived.UpperLowerStar` supplies `derivedUpperStarLowerStarAdjunction` and the exact
  pullback comparison `leftDerivedUpperStarIsoMapDerivedCategory`.
- `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`:
  `Mod.derivedExtendMapDerivedCategoryAdjunction` (the specified scalar adjunction).
- `Sheaf.Paper.InternalScalarPullbackNormalization`:
  `QuotientChange.internal_scalar_pullback_normalization`, using its canonical
  `TensorNormalization`/`TensorNormalized` interface.
- `Sheaf.Paper.ModuleRingedToposDerivedComparison`:
  `ModuleRingedComparison.internalProjection`, `projection_comparison`; its canonical
  internal tensor-pullback comparison is `internalDelta` in `SectionDerivedRealization`.
- `Sheaf.Paper.ProjectionMateExact`: `SheafOfModules.ringedProjectionMateExact`.
- Proof imports: `Mathlib.CategoryTheory.Adjunction.Mates` provides `mateEquiv`,
  `conjugateIsoEquiv`, `iterated_mateEquiv_conjugateEquiv` (the recorded Mathlib leaves);
  `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction` provides
  `AlgebraicGeometry.Scheme.proEtaleRingSheafChangeAdjunction`.

Edge cases checked mathematically before writing: K=0 and S=0 give zero maps;
a=identity gives the unit-coefficient projection; f=identity gives balanced tensor
identity; empty X or Y introduces no Nonempty assumption. Unbounded K and arbitrary
morphisms q are allowed; no IsIso h, properness, qcqs, constructibility, stage diagram
or boundedness is assumed. All universe variables and binders are explicit.

Searches (the unedited outputs are in sandbox searches.jsonl):

- msearch leanfinder: “Restricting the derived scalar extension direct image mate is
  the projection formula map with the restricted regular coefficient module”:
  eight ordinary ModuleCat scalar-adjunction hits, including Counit.map,
  HomEquiv.toRestrictScalars, and counit_app; no derived geometric statement.
- msearch loogle: `CategoryTheory.mateEquiv, CategoryTheory.Adjunction`: twelve hits
  including mateEquiv, counit clauses, conjugate and composition identities;
  these supply the formal proof tool, not this coefficient-normalized equality.
- msearch grep: `derivedPushHom|restricted.*regular|projection.*[Mm]ate` in
  Mathlib/CategoryTheory: zero hits.
- msearch leansearch: “The flat scalar extension direct image mate is the projection
  formula map under the balanced tensor identification”: eight ordinary module/flat
  base-change hits, no exact statement.
- rg in lean/WeilConjectures and lean/Sheaf for the item ID and the proposed theorem
  names: no existing declaration of this item. Broader regular-pullback and normalized
  tensor searches found the reusable canonical constructions and the integral quotient
  specialization in `IntegralQuotientProjectionMap`, which only treats reduction at
  a positive finite quotient level. It is not the arbitrary condensed ring morphism
  and actual scalar-adjunction mate of this node.

No mathematical statement correction, disputed assertion or dependency replacement.

## Second reading by Q129

Self-audit under the dispatcher instruction prohibiting sub-agents; the maintainer's
independent review remains required. Read the node and module together. Checked the
four factors of h in order, homEquiv inverse direction, mu direction, rho on the second
tensor factor, geometric counit on the first, the actual projection arrow, and the
naturality square. The ordinary/derived coefficient comparison is constructed, not a
free isomorphism. The compile-driven repair corrected the localization comparison's
direction and made the already recorded functor aliases explicit. No mathematical
hypothesis or conclusion changed. The only theorem proof is `sorry`; all helper data are real.

Validation: the complete file compiled through scompile.py as both the sandbox module
and its library module (19.9 s and 7.5 s), with no errors or unexpected warnings.
The earlier diagnostic `#eval` commands and unscoped heartbeat setting were removed.
The ordinary and derived regular-pullback constructions and all six remaining declarations
are retained; no canonical map was replaced to obtain these timings.
