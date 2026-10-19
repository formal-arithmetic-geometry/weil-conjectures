## Worker report

The module `Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower` states
`AlgebraicGeometry.exists_deJong_geometricallyIrreducibleTower`, with one `sorry`, and
constructs the finite composite `AlgebraicGeometry.towerComposite` by recursion with real data.
No theorem is proved and no definition contains postponed data. The full eleven-step node
proof, including every cited node, is in the theorem docstring.

Source read: de Jong, *Families of curves and alterations* (1997), Situation 5.8 and
Theorem 5.9 (i)--(iii), printed pp. 615--617, and the induction proof on p. 617, at
https://www.numdam.org/item/10.5802/aif.1575.pdf. The item is the stated consequence after
forgetting the group, sections, projectivity and boundary. There is no source correction.
The absent local archival PDF is already recorded as WANTED by the node.

Hypotheses and clauses, individually:

- `S W : Scheme.{u}` are the two schemes; `[IsIntegral S] [IsIntegral W]` give integrality,
  including nonemptiness and reduced irreducibility.
- `hS : IsExcellentScheme S` and `hW : IsExcellentScheme W` mean excellence of every affine
  coordinate ring, using the existing `IsExcellent` predicate, not merely excellence of stalks.
- `[IsLocallyNoetherian S] [CompactSpace S]` and the corresponding two instances for `W`
  are exactly the node's meaning of Noetherian. No separation condition on either scheme
  is imposed.
- `hSdim` and `hWdim` each assert a finite natural upper bound on `topologicalKrullDim`.
  On these nonempty integral schemes this is precisely finite dimension.
- `g : W ⟶ S`, `[IsProper g]`, `[IsDominant g]` encode the proper dominant morphism.
- `η : S`, `hη : IsGenericPoint η Set.univ` designate the generic point of the integral base.
- `d : ℕ`, `hd : 1 ≤ d` express the positive generic relative dimension; `hηdim` states
  `topologicalKrullDim (g.fiber η) = (d : WithBot ℕ∞)`.
- `hηirr : GeometricallyIrreducible (g.fiberToSpecResidueField η)` is geometric irreducibility
  of this actual generic fibre over its actual residue field, with all field extensions
  permitted by the dependency interface.
- `P : Fin (d + 1) → Scheme.{u}` supplies the schemes `P₀,...,P_d`; the altered base `S₁`
  is `P 0`, so `P₀ = S₁` holds by designation, without any identification/cast to an
  unrelated base. `b : P 0 ⟶ S` is the base alteration.
- `q : ∀ j : Fin d, P j.succ ⟶ P j.castSucc` supplies exactly the `d` curve maps, with
  index `j` corresponding to the paper's map `q_(j+1)`.
- The first conclusion conjunction quantifies over every `i : Fin (d + 1)` and gives
  `IsIntegral`, `IsExcellentScheme`, `IsLocallyNoetherian`, `CompactSpace`, and a finite
  upper bound for dimension of `P i`. This includes the altered base at `i = 0` and
  every tower stage, including the top stage.
- `h : P ⟨d, Nat.lt_succ_self d⟩ ⟶ W` is the top alteration.
- `IsAlteration b ∧ IsAlteration h` uses the existing Orgogozo predicate. It means proper,
  surjective, and finite on the inverse image of a dense target open. Its additional
  component-dominance clause is automatic here: an integral scheme has only the whole
  space as irreducible component, and the maps are surjective onto integral targets.
  Thus this does not strengthen the node's alteration condition.
- Each `q j` is `IsProper`, `Flat`, and `LocallyOfFinitePresentation`. Properness already
  implies quasi-compactness and separatedness (hence quasi-separatedness), so this is
  precisely finite presentation, not just its local version.
- For every base point `y`, `geometricPoint (P j.castSucc) y` is exactly
  `Spec (AlgebraicClosure (residueField y)) → Spec (residueField y) → P j.castSucc`.
  `pullback.snd` is the structure morphism of the geometric fibre, as required by the
  recorded geometric-fibre and fibre-product declarations.
- `IsSemistableGeometricCurve` unfolds to `ConnectedSpace`, `IsReduced`, pure dimension
  one, and at each point either a smooth open neighbourhood over the algebraically
  closed field or `IsOrdinaryDoublePoint`. `ConnectedSpace` includes nonemptiness.
- `IsOrdinaryDoublePoint` uses the maximal-ideal adic completion of the actual fibre
  stalk and an isomorphism to `nodeRing Ω = Ω[[u,v]]/(uv)` compatible with the actual
  scalar map. Both smooth and nodal points are allowed; neither characteristic nor
  perfection of any input field is restricted.
- `towerComposite P q` recursively composes the actual `q` arrows, from top to bottom.
  Consequently `h ≫ g = towerComposite P q ≫ b` is exactly `g ∘ h = b ∘ q₁ ∘ ... ∘ q_d`.
- There is no map to the total base change asserted to be surjective. In particular,
  no conclusion about covering vertical components is encoded.

Dependency declarations read and used:

| Node/interface | Module | Declaration(s) |
| --- | --- | --- |
| proper | `Mathlib.AlgebraicGeometry.Morphisms.Proper` | `AlgebraicGeometry.IsProper` |
| flat | `Mathlib.AlgebraicGeometry.Morphisms.Flat` | `AlgebraicGeometry.Flat` |
| finite presentation | `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` | `AlgebraicGeometry.LocallyOfFinitePresentation` |
| integral scheme | `Mathlib.AlgebraicGeometry.Properties` | `AlgebraicGeometry.IsIntegral` |
| excellent ring | `Sheaf.RingTheory.ExcellentRing` | `IsExcellent` |
| geometric irreducibility | `Mathlib.AlgebraicGeometry.Geometrically.Irreducible` | `AlgebraicGeometry.GeometricallyIrreducible` |
| fibre | `Mathlib.AlgebraicGeometry.Fiber` | `Scheme.Hom.fiber`, `Scheme.Hom.fiberToSpecResidueField` |
| dimension | `Mathlib.Topology.KrullDimension` | `topologicalKrullDim` |
| locally Noetherian | `Mathlib.AlgebraicGeometry.Noetherian` | `AlgebraicGeometry.IsLocallyNoetherian` |
| quasi-compact scheme | `Mathlib.Topology.Defs.Filter` | `CompactSpace` |
| finite morphism | `Mathlib.AlgebraicGeometry.Morphisms.Finite` | `AlgebraicGeometry.IsFinite` (inside `IsAlteration`) |
| geometric fibre and fibre product | `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` | `pullback`, `pullback.snd` |
| generic point | `Mathlib.Topology.Sober` | `IsGenericPoint` |
| landed geometry definitions | `Sheaf.Paper.OrgogozoInductionData` | `IsExcellentScheme`, `IsAlteration`, `geometricPoint`, `IsSemistableGeometricCurve`, `IsOrdinaryDoublePoint`, `nodeRing`, `localScalar` |

The only added statement dependency is the already landed definition node
`def-trf-orgogozo-induction-data`, under brief-stage2 §5's permission to add landed notions.
Its full node and declaration/docstrings were read; no private copies of its definitions
are introduced. The older `IsProjectiveNodalCurve` would impose projectivity and a finite
closed nonsmooth complement not requested here, so it is not used. The recursive composite
is only a helper for this node's displayed arrows and is listed in `lean.declarations`.
All currently stated proof dependencies are imported without `public`; the statement
interfaces are publicly imported. Unstated proof prerequisites remain the named proof-plan
inputs and are not needed to state the theorem.

Edge cases checked: empty input schemes are already excluded by integrality; `d = 0` is
explicitly excluded by `hd`. At `d = 1`, the family has two objects and exactly one map;
the recursive composite reduces to that map composed with an identity. The helper itself
also defines the empty composite at zero, with no false existence assertion for `d = 0`.
Fibres cannot be empty since `ConnectedSpace` includes `Nonempty`; pure dimension alone
would not have sufficed. Reducible nodal fibres are permitted, and every tower stage is
integral without assuming all its fibres irreducible. Arbitrary characteristic, positive
and zero, and nonprojective nonaffine excellent bases are retained. No independent small
universe is used for field-extension tests: the existing universe-polymorphic geometric
interfaces use the scheme universe `u`.

Searches actually run:

- `msearch.py ... leanfinder "A proper dominant morphism of excellent integral schemes
  with geometrically irreducible generic fibre admits an alteration into a tower of
  semistable curves"`: eight hits, including dominance under composition, normalization,
  integral morphisms and universally closed maps. None gives this theorem.
- `msearch.py ... loogle '"semistable"'`: zero hits.
- `msearch.py ... grep 'plurinodal|semistable|deJong|alteration' AlgebraicGeometry`:
  zero Mathlib hits.
- `rg` of the upstream `WeilConjectures` source for de Jong, alteration, plurinodal,
  semistable and geometric irreducibility found geometric irreducibility tools and
  contextual mentions, no alteration tower over an arbitrary excellent base.
- `rg` of upstream and project sources for the item id, proposed theorem name and
  `towerComposite`: no existing declaration.
- `rg` of project sources for alteration, excellence and nodal notions found
  `OrgogozoInductionData`, `ProjectiveNodalTower`, and `PlurinodalAlteration`.
  The latter only states a trait theorem and an algebraically closed field theorem;
  its signatures were read and do not match the arbitrary-base assertion here.
- `rg` of Mathlib's `CategoryTheory/ComposableArrows` found `ComposableArrows.hom`,
  which operates on covariant functors with all composition laws supplied, rather
  than this node's backwards-indexed family of adjacent arrows. The small recursive
  helper supplies exactly the actual finite composite without extra coherent data.

No STATEMENT-DISPUTED flag and no statement correction. Compilation uses only the authorized
`scompile.py` wrapper; no global build or live-source mutation was performed.

## Second reading by Q37

Author's explicit second pass, not an independent agent review (the dispatcher forbids
starting other agents). Independent maintainer review follows delivery. I reread the node,
its proof, the final theorem, and every geometric definition used, clause by clause as
mapped above. I corrected the first draft's base endpoint typing by designating `P 0` as
`S₁`. I replaced the draft's inline nodal-ring predicate and local `let` by the existing
scalar-compatible semistable-curve and geometric-point definitions. I checked that the
component clause in `IsAlteration` is equivalent in the presence of the displayed integral
source/target clauses, and that finite presentation follows from properness plus local
finite presentation. The recursive composite includes every adjacent arrow once, in the
correct order. The complete supplied proof plan and all available proof imports were added.

Validation: `scompile.py` accepted the statement module without errors or warnings.
`deliver2.py Q37 lem-trf-de-jong-geometrically-irreducible-tower --no-push` printed
`OK (dry run): commit 02afcc5011 passes the preflight and compiles; nothing pushed`.
