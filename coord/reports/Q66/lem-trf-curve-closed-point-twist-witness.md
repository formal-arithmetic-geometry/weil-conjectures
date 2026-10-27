## Worker report

Module: `Sheaf.AlgebraicGeometry.CurveClosedPointTwistWitness`.
The theorem `AlgebraicGeometry.Scheme.Modules.curve_closed_point_twist_witness`
states the complete node, with `sorry` as its only proof. The helper
`closedPointStructurePushforward C z` is defined with real data as
`(pushforward (C.fromSpecResidueField z)).obj
(SheafOfModules.unit (Spec (C.residueField z)).ringCatSheaf)`.
It is a name for the witness in this node, not a second pushforward construction.
No new nodes, dependency repairs, or statement corrections are needed.

Source read: `literature/stacks-project/varieties.tex`,
`lemma-degree-on-proper-curve` (Tag 0AYV), lines 9669–9693, especially the
closed-point case of condition (2); `lemma-chi-tensor-finite` (Tag 0AYT),
lines 6208–6262, especially conclusions (3)–(5) and its projection-formula proof.
The theorem docstring carries all six proof steps of the item.

Hypotheses and objects, one by one:

- A field k: `(k : Type u) [Field k]`.
- An integral scheme C: `(C : Scheme.{u}) [IsIntegral C]`.
- Proper over k: `[C.Over (Spec (.of k))]` and
  `[IsProper (C ↘ Spec (.of k))]`.
- Topological Krull dimension one: `hdim : topologicalKrullDim C = 1`.
- The named generic point: `(ξ : C)` and
  `hξ : closure ({ξ} : Set C) = Set.univ`.
- An invertible O_C-module: `(L : C.Modules) [L.IsInvertible]`.
- A closed point distinct from ξ: `(z : C)`, `hzξ : z ≠ ξ`, and
  `hz : IsClosed ({z} : Set C)`.
- Z is literally `Spec (C.residueField z)`; i is literally
  `C.fromSpecResidueField z`. There is no arbitrary immersion variable or choice
  of a point map. Its closed-immersion property follows from the closedness
  assumption and the canonical residue-point construction, so it is not imposed
  as an extra assumption. The helper uses exactly this i.
- G is the actual structure-sheaf direct image. Mathlib's
  `Scheme.Modules.pushforward_obj_obj` identifies its sections on U with the
  source sections on `i ⁻¹ᵁ U`; `pushforward` is constructed using
  `f.toRingCatSheafHom`, so the scalar action is through the structure map.

Conclusions, one by one, in their order in Lean:

- Coherence of G: `RingedSpace.IsCoherent C.toRingedSpace
  (closedPointStructurePushforward C z)`. This is the finite-type and
  finite-type-kernel predicate, not merely quasi-coherence of finite type.
- Support is exactly {z}: equality of
  `{x : C | ¬ Subsingleton (G.presheaf.stalk x)}` with `{z}`.
  `Subsingleton` expresses zero for these abelian-group stalks.
- Support has dimension zero: `topologicalKrullDim` of that same subtype is `0`.
- G_z is κ(z), O_{C,z}-linearly: the existential `e` is a `LinearEquiv` over
  `C.presheaf.stalk z`. Its source is the published
  `(RingedSpace.moduleStalkFunctor C.toRingedSpace z).obj G`.
  Its target is `ModuleCat.restrictScalars (C.residue z).hom` applied to the
  one-dimensional regular κ(z)-module. Thus the target action is explicitly
  the residue-map action, rather than an arbitrary local-ring action.
- Dimension over κ(z) is one: `@Module.finrank ...
  (e.toAddEquiv.module (C.residueField z)) = 1` uses the same stalk carrier
  and its existing additive structure. The published `AddEquiv.module`
  transports κ(z)'s scalar multiplication along e. Because e is already
  residue-linear, this action restricts to the given O_{C,z}-action.
  Surjectivity of the residue quotient makes this the unique compatible action.
  No hypothetical vector-space structure is taken as input.
- The maximal ideal annihilates G_z: the universal clause quantifies
  `a ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z)` and all elements m of
  the same bundled stalk, and concludes `a • m = 0`. This is precisely
  m_z G_z = 0, without introducing a new ideal-product notion.
- G_ξ = 0: `Subsingleton (G.presheaf.stalk ξ)`.
- Both tensor orders are coherent: separate `RingedSpace.IsCoherent`
  conjuncts for `G ⊗ L` and `L ⊗ G`, in `C.Modules`.
- The three Euler characteristics agree: the final two conjuncts say
  `(L ⊗ G).eulerChar k = (G ⊗ L).eulerChar k` and
  `(G ⊗ L).eulerChar k = G.eulerChar k`.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (commutative ring and division ring).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`:
  `AlgebraicGeometry.IsProper`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, and the scheme-module
  tensor instance, using the existing sheafification tensor.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` for the canonical closed immersion.
- `Mathlib.AlgebraicGeometry.ResidueField`:
  `AlgebraicGeometry.Scheme.residueField`, `Scheme.residue`, and
  `Scheme.fromSpecResidueField`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: public
  `AlgebraicGeometry.RingedSpace.IsCoherent` from the upstream Coherent module;
  the recorded conjunction `IsQuasiCoherentFiniteType` is not substituted for it.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor` and `stalkObj` for the presheaf-level
  module stalk interface; its recorded note directs scheme-module consumers
  to `RingedSpace.moduleStalkFunctor`.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor`, the already landed
  `def-pc-module-stalk-functor`. Its id is added to `stmt_deps` as authorized
  for an existing landed notion. Its object is the original abelian stalk,
  bundled over the actual local ring, not a copied stalk construction.
- `Mathlib.LinearAlgebra.Dimension.Finrank`: `Module.finrank`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` and its public localization tensor
  imports, the recorded tensor dependency.
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`:
  `AlgebraicGeometry.Scheme.Modules.eulerChar` (the existing alternating sum).
- `Mathlib.Algebra.Module.TransferInstance`: `AddEquiv.module`.
  `ModuleCat.restrictScalars` is the existing change-of-rings functor and
  gives exactly scalar multiplication through `(C.residue z).hom`.

Proof-only imports follow every stated proof dependency:
`Mathlib.AlgebraicGeometry.Noetherian` for `IsLocallyNoetherian` and
`LocallyOfFiniteType.isLocallyNoetherian`;
`Mathlib.AlgebraicGeometry.Morphisms.Finite` for the closed-immersion-to-finite
instance; upstream `CoherentFiniteTypeLocallyNoetherian` for
`isCoherent_iff_isQuasicoherent_and_isFiniteType`; upstream
`FinitePushforwardCoherent` for `isCoherent_pushforward_of_isFinite`;
upstream `ClosedPushforwardStalks` for
`closedImmersion_pushforward_stalks`; and
`Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport` for
`eulerChar_zero_dim_support`. Their full signatures and docstrings were read.
Statement dependencies that also occur in the proof are public imports.

Edge cases checked mathematically before writing:

- Non-rational closed points are allowed: the stalk is κ(z), not k, and the
  dimension asserted is over κ(z). Euler characteristics remain over k.
- Singular closed points are allowed: no smoothness, regularity, algebraic
  closedness, separability, or rational-point hypothesis is present.
- The empty scheme is excluded by integrality and dimension one. The generic
  point is expressly excluded as a choice of z. No additional nonemptiness
  assumption is added.
- All characteristics are allowed. Trivial and nontrivial invertible twists
  both occur. The witness is nonzero because its residue-field stalk has rank 1.
- The support dimension is exactly zero, not merely ≤ 0. Its topology is the
  subspace topology on the support predicate's subtype.
- The finrank clause uses the actual stalk action descended through the
  residue quotient, not a fibre tensor product that would lose the original stalk.

Searches actually executed (2026-10-24):

- `msearch.py ... leanfinder`: “The direct image of the residue field at a closed
  point on a proper integral curve is coherent and its Euler characteristic is
  invariant under an invertible twist”. Eight hits on residue fields,
  `fromSpecResidueField`, and their functorial identities; none states this node.
- `msearch.py ... loogle '"eulerChar", "tensor"'`: OK, zero hits.
- `msearch.py ... grep 'closedPoint.*(stalk|support)|eulerChar.*(tensor|invertible)'
  AlgebraicGeometry`: OK, eighteen hits on scheme stalks and residue morphisms;
  no matching coherent witness/twist statement.
- `msearch.py ... leansearch`: “A residue field skyscraper on a curve is coherent
  and tensoring with a line bundle preserves its Euler characteristic”. Eight
  hits: topological skyscrapers, residue fields, `Ideal.Fiber`, and related
  evaluations; no complete statement or one-line specialization.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `closedPointWitness|closed_point_twist_witness|closed_point.*witness|curve.*twist.*witness`
  and `dag/lean_names_upstream.json`: no existing declaration.
- `grep -rn` of this exact item id in `lean/WeilConjectures`: no match.
- Additional `rg` over both project Lean trees for
  `closedPointStructurePushforward|pushforward.*fromSpecResidueField|fromSpecResidueField.*pushforward`:
  only unrelated fibre-base-change pushforwards, no duplicate helper.
- Broader project searches on closed-point/stalk and residue/stalk interfaces
  found the existing `RingedSpace.moduleStalkFunctor`; its source was opened
  and used instead of introducing a module-stalk definition.

Validation: the prescribed `scompile.py Q66 ... <module>` compiled both the
sandbox name and the final library module name cleanly. An initial attempt to
write scalar actions directly on unbundled abelian stalks failed instance
synthesis. The final statement uses the published bundled local-ring stalk
and explicit scalar restriction along the residue map. `autoImplicit false`
ensures all variables and universes are bound. There are no extra hypotheses
and no statement dispute. The helper has real data; only the named theorem
is postponed.

## Second reading by Q66

I reopened the final node copy and module for a separate self-review; no other
agent was started, as the dispatch brief prohibits it. Independent review is
performed by the maintainer after delivery.

I matched all binders to the original field/integral/proper/dimension/generic/
invertible/closed/distinct hypotheses. The canonical point map fixes Z and i,
and the helper fixes G without extra input. I checked each conjunction against
coherence, singleton support, exact zero-dimensional support, the residue-linear
stalk isomorphism, dimension 1, maximal-ideal annihilation, zero generic stalk,
both tensor-coherence claims, and both equalities in the displayed Euler chain.

The essential interface correction during elaboration was to replace the
unbundled scalar-action expressions by the already published bundled stalk
and the residue-map `restrictScalars` target. I checked that `AddEquiv.module`
preserves the additive structure and that its action on the source of e is
compatible with the original local-ring action. The node statement is unchanged;
only its `lean` record and the additional landed stalk-functor `stmt_deps` entry
are changed. No clauses were dropped or strengthened. Every postponed proof
belongs to this item, and the docstring includes all six source proof steps.
