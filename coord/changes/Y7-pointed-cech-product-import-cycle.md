# Profinite product definitions separated from pointed Čech existence

## Reason

The prescribed proof dependency ProfiniteSchemeProductComponents publicly imports
PointedLimitCech for its explicit product and label definitions. Importing that proved
comparison into the assembly creates an import cycle. Move the nine explicit helper
constructions verbatim into ProfiniteProductMaps; publicly re-export them from the old
module. Change the comparison module's single public import to this basic module.
All existing declaration names, signatures and terms are retained. No target or
mathematical definition changes. No file under WeilConjectures is edited.
The comparison module is currently unclaimed (its H5 proof already landed).

## Old

In lean/Sheaf/AlgebraicGeometry/FundamentalGroup/PointedLimitCech.lean:

```lean
/-- The actual scheme `T × P`, using the existing profinite test object, not a product
of underlying sets. Source: Stacks 097D
(blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
noncomputable abbrev profiniteProduct (T : Scheme.{u}) (P : Profinite.{u}) : Scheme.{u} :=
  ((ProEtale.profiniteToProEtOf T).obj P).left

/-- The first projection of the profinite product. Source: Stacks 097D
(blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
noncomputable abbrev profiniteProductBase (T : Scheme.{u}) (P : Profinite.{u}) :
    profiniteProduct T P ⟶ T :=
  ((ProEtale.profiniteToProEtOf T).obj P).hom

/-- The constant-label section as a scheme morphism, by evaluation of locally constant
integer functions. Source: Stacks 097D
(blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
noncomputable def profiniteProductSection (T : Scheme.{u}) (P : Profinite.{u}) (p : P) :
    T ⟶ profiniteProduct T P :=
  pullback.lift
    (ProEtale.toSpecZ T ≫ Spec.map (CommRingCat.ofHom
      (ULift.ringEquiv.symm.toRingHom.comp (LocallyConstant.evalRingHom p))))
    (𝟙 T) (by exact (ProEtale.comp_toSpecZ _).trans (Category.id_comp _).symm)

/-- The q-th power of a finite label set. Source: the consecutive-label construction in
§7.4 (blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
def labelPower (q : ℕ) : Type u ⥤ Type u where
  obj A := Fin q → A
  map f := ↾fun a ↦ f ∘ a

/-- The prescribed inverse system `N ↦ ∐_(G/N)^q T`, with quotient transition maps.
Source: Stacks 097D (blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
noncomputable def finiteLabelDiagram (T : Scheme.{u}) (G : ProfiniteGrp.{u}) (q : ℕ) :
    OpenNormalSubgroup G ⥤ Scheme.{u} :=
  ProfiniteGrp.toFiniteQuotientFunctor G ⋙ CategoryTheory.forget FiniteGrp ⋙ labelPower q ⋙
    (sigmaConst.obj T)

/-- Consecutive labels up to the i-th vertex, in their stated order.
Source: the cumulative-label formula in §7.4
(blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
def cumulativeLabel {G : Type u} [Group G] {q : ℕ} (g : Fin q → G) (i : ℕ) : G :=
  ((List.ofFn g).take i).prod

/-- Restrict a consecutive-label list along an arbitrary simplex map.
Source: the group-nerve construction in §7.4
(blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
def restrictedLabels {G : Type u} [Group G] {m n : ℕ}
    (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (g : Fin m → G) : Fin n → G :=
  fun i ↦ (cumulativeLabel g (φ.toOrderHom i.castSucc).val)⁻¹ *
    cumulativeLabel g (φ.toOrderHom i.succ).val

/-- The continuous map of q labels induced by a pointed scheme morphism.
Source: Stacks 0BND (3) (blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
noncomputable def labelMap (G H : ProfiniteGrp.{u}) (ρ : H →* G)
    (hρ : Continuous ρ) (q : ℕ) :
    Profinite.of (Fin q → H) ⟶ Profinite.of (Fin q → G) :=
  ConcreteCategory.ofHom (ContinuousMap.piMap (fun _ : Fin q ↦ ⟨ρ, hρ⟩))

/-- Map of profinite products over a scheme morphism, using the existing test functor.
Source: Stacks 097D and 0BND (3)
(blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
noncomputable def profiniteProductMap {T T' : Scheme.{u}} (f : T' ⟶ T)
    {P P' : Profinite.{u}} (a : P' ⟶ P) :
    profiniteProduct T' P' ⟶ profiniteProduct T P :=
  pullback.map _ _ _ _ (ProEtale.profiniteToScheme.map a) f
    (𝟙 ProEtale.specZ) (by
      change ProEtale.toSpecZ _ ≫ 𝟙 _ = _ ≫ ProEtale.toSpecZ _
      rw [Category.comp_id]
      exact (ProEtale.comp_toSpecZ _).symm)
    (by
      change ProEtale.toSpecZ T' ≫ 𝟙 _ = f ≫ ProEtale.toSpecZ T
      exact (Category.comp_id _).trans (ProEtale.comp_toSpecZ f).symm)

```

In lean/Sheaf/AlgebraicGeometry/ProfiniteSchemeProductComponents.lean:

```lean
public import Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech
```

## New

The nine declaration blocks above are verbatim in
lean/Sheaf/AlgebraicGeometry/FundamentalGroup/ProfiniteProductMaps.lean.
PointedLimitCech adds:

```lean
public import Sheaf.AlgebraicGeometry.FundamentalGroup.ProfiniteProductMaps
```

ProfiniteSchemeProductComponents replaces its old import with that same public
import. Its proved declarations, proof bodies, options and other imports are unchanged.
PointedLimitCech can now privately import the comparison without a cycle.

## Users

The complete transitive consumer inventory from tools/downstream.py is below.
For all existing consumers, the same public names and terms remain available through
the old module's public import. There is no statement-strength or semantic change.
Only the comparison's import is adapted; all other consumer source files stay identical.
The preflight and the maintainer's build check the resulting import graph.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConnectedAbelianCoverTower | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.AlgebraicGeometry.ConnectedAbelianTowerDescentHom | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.AlgebraicGeometry.ConnectedAbelianTowerDescentObject | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.AlgebraicGeometry.ConnectedAbelianTowerFiniteFrame | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.AlgebraicGeometry.ConnectedAbelianTowerNormalizedData | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.AlgebraicGeometry.ConnectedAbelianTowerNormalizedDescent | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.HenselianPointedResidualCover | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.AlgebraicGeometry.NormalizedFiniteSplittingOperations | Q6 | Public names and terms retained through the re-export; no edit. |
| Sheaf.AlgebraicGeometry.ProfiniteSchemeProductComponents | unclaimed | Replace its public import with ProfiniteProductMaps; all declarations unchanged. |
| Sheaf.AlgebraicGeometry.SNCFiniteFibreClassification | E8 | Public names and terms retained through the re-export; no edit. |
| Sheaf.AlgebraicGeometry.SNCFiniteFibreData | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.AlgebraicGeometry.SNCFiniteTameSheaves | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.AlgebraicGeometry.SNCPointedAffineCommonRefinement | Q9 | Public names and terms retained through the re-export; no edit. |
| Sheaf.AlgebraicGeometry.SNCRootStageSystem | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.AlgebraicGeometry.SNCUniversalResidualCharts | E9 | Public names and terms retained through the re-export; no edit. |
| Sheaf.AlgebraicGeometry.UniversalResidualRootSplitting | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.CompatibleKummerTowerCech | T7 | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.FullParameterRootTower | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.FullRootRotationTorsor | H7 | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerChartGeometryMaps | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerCoefficientModels | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerCoherentRoof | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerConstantNerveTerm | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerGeometricColumns | V4 | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerGlobalChart | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerInvariantScalarMap | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerLocalSource | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerNerveCoordinates | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerNerveGeometricMap | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerNerveTransport | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerNormalizedChart | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerParameterizedTerm | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerPartialNerveChart | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerPartialNerveCoordinates | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerPartialNerveMorphism | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerPartialNerveNaturality | J6 | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerPartialNerveScalarMorphism | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerRefinement | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerResolvedDescent | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerScalarInvariantSquare | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerStratumChart | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerStratumGeometry | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerStratumScalarMaps | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerStratumScalarMateDetection | F2 | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.KummerSuccessiveDescent | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.ParameterRootIntegralNilFibre | J7 | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.ResidualRootTowerLocalCharts | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.RootTowerProfiniteBaseChange | unclaimed | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.RootTowerPuncturedFaceDiagram | D5 | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.TameRootTowerExtension | B8 | Public names and terms retained through the re-export; no edit. |
| Sheaf.Paper.TameStratumKummerDescent | K1 | Public names and terms retained through the re-export; no edit. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech | Y7 | Re-export moved definitions; complete the five theorem proofs. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.ProfiniteProductMaps | Y7 (new module) | Own the nine unchanged explicit constructions. |

## Status

landed 20261025T061131-L-2400866 2026-10-25 (merge of deliver/Y7/Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech)
