# derivedPullback

## Reason

Kernel checking of the component proof repeatedly unfolded the large existential predicate
inside the fixed choice of derived pullback and exceeded 60 seconds. Profiling isolated the
cost in functor-field comparisons, including applying the two open branches. Keep exactly
the original chosen functor behind a `no_expose` data definition and retain the public
`derivedPullback` definition and signature. The proved equation `derivedPullback_eq_choose`
identifies the result with the original construction; `derivedPullback_spec` exposes its
original inverse-image, tensor-counit, triangulatedness and K-flat properties.

The component then compiles in about 21 seconds, with no additional mathematical assumptions.
This is a representation repair, not a proof split. The existence theorem, the selected
functor, all binders/universes of existing declarations and all target signatures are unchanged.
Definitions using the functor continue to denote the same fixed construction. The independent
reader should include this implementation change in the definition review of target meanings.

Callers that obtained the counit with `Classical.choose_spec (exists_derivedPullback f)`
now use `derivedPullback_spec f`. The original compiler error is an application/type mismatch
between a counit whose source is `DerivedCategory.Qh ⋙ Classical.choose ...` and one whose
source is `DerivedCategory.Qh ⋙ derivedPullback f`, with the note that `derivedPullbackData`
is not exposed. The implementation consumers are checked individually against the new
interface; their signatures and visibility stay identical. The affine tensor adapter eliminates the specification witnesses directly. The affine model
proof introduces its statement's fixed complex. The bottom-free-chain proof reuses the
public singleComplexOpenPullbackIso, introduces the statement's own fixed functors and
complexes, and transports the underived equivalence unit directly, avoiding derived adjointification. These are unclaimed
modules; no existing public signature or visibility changes. No unit route changes.

The bottom-free-chain consumer additionally uses `perfectHomComposition` from the existing
fixed-comparison interface, replacing local elimination of the full composition existence
predicate. Its proof import `DerivedPullbackComposition` is replaced by `PerfectHomTransport`.
This keeps the large witness-selection term behind its existing definition. The updated
source passes the complete axiom probe in 55.7 seconds; its public signature is unchanged.
The affine tensor module also passed the exact probe separately in 54.8 seconds after a
transient timeout in the repeated push validation. The source files all pass the 60-second
compile limit; no limit was changed and no proof was split.

## Old

```lean
noncomputable def derivedPullback {T S : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))] :
    schemeDerivedCategory S ⥤ schemeDerivedCategory T :=
  Classical.choose (exists_derivedPullback g)
```

## New

```lean
/-- The fixed chosen construction behind the derived-pullback interface. This uses exactly
its original existence theorem, with no additional choice of functor.
Source: Stacks Project, Tag 0D5S (blueprint: def-pc-derived-pullback). -/
@[no_expose] noncomputable def derivedPullbackData {T S : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))] :
    schemeDerivedCategory S ⥤ schemeDerivedCategory T :=
  Classical.choose (exists_derivedPullback g)

/-- The derived pullback `L g^* : D(𝒪_S) ⥤ D(𝒪_T)`.

For `g : T ⟶ S`, this is the composite of termwise inverse image and derived change
of rings along `g^sharp`.  If `P ⟶ E` is any K-flat resolution, its canonical
representative is `g^*P = 𝒪_T ⊗_{g⁻¹𝒪_S} g⁻¹P`; the comparison isomorphisms supplied
by derived change of rings make this independent of `P`.
Source: literature/blueprint/master/blueprint/sec-picard-framework/
  sk-thm-picard-semicon/def-pc-derived-pullback.md, node def-pc-derived-pullback
  (blueprint: def-pc-derived-pullback). -/
noncomputable def derivedPullback {T S : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))] :
    schemeDerivedCategory S ⥤ schemeDerivedCategory T :=
  derivedPullbackData g

/-- The fixed derived pullback has the original chosen construction. -/
theorem derivedPullback_eq_choose {T S : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))] :
    derivedPullback g = Classical.choose (exists_derivedPullback g) := by
  unfold derivedPullback derivedPullbackData
  rfl

/-- The defining inverse-image, tensor-counit and K-flat properties of the fixed
functor. This API avoids unfolding the construction when using its properties.
Source: Stacks Project, Tag 0D5S (blueprint: def-pc-derived-pullback). -/
theorem derivedPullback_spec {T S : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))] :
    let L := derivedPullback g
      ∃ (I : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
          SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology T)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (TopCat.Sheaf.inverseImageRing g.base S.sheaf)))
        (hI : ∀ M, I.obj M = TopCat.Sheaf.inverseImageModule g.base S.sheaf M)
        (_ : ∀ {M N} (a : M ⟶ N),
          I.map a = eqToHom (hI M) ≫
            TopCat.Sheaf.inverseImageModuleMap g.base S.sheaf M a ≫
              eqToHom (hI N).symm)
        (_ : I.Additive),
        PreservesFiniteLimits I ∧ PreservesFiniteColimits I ∧
        (∀ {P G : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ}
          (s : P ⟶ G), CochainComplex.IsKFlatResolution (R := S.sheaf) s →
            CochainComplex.IsKFlatResolution
              (R := TopCat.Sheaf.inverseImageRing g.base S.sheaf)
              ((I.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) ∧
        ∃ (E : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
            SheafOfModules.{u} (moduleRings T.toRingedSpace))
          (h : ∀ M, E.obj M = Scheme.Modules.tensorPullbackObj g M)
          (_ : ∀ {M N} (a : M ⟶ N),
            E.map a = eqToHom (h M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
              eqToHom (h N).symm)
          (_ : E.Additive)
          (ε : DerivedCategory.Qh ⋙ L ⟶
            E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
          L.IsLeftDerivedFunctor ε
              (HomotopyCategory.quasiIso
                (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (ComplexShape.up ℤ)) ∧
            (∃ (_ : L.CommShift ℤ), L.IsTriangulated) ∧
            ∀ P : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ,
              CochainComplex.IsAcyclicTensorKFlat (R := S.sheaf) P →
                IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  dsimp only
  rw [derivedPullback_eq_choose]
  exact Classical.choose_spec (exists_derivedPullback g)
```

## Users

The source-only downstream check lists 644 modules using `derivedPullback`, within 2903
import descendants. Every listed statement still uses the identical fixed functor, as
proved by the equality API. The following table also identifies each implementation caller
adapted in this delivery. All those callers were unclaimed at the time of the repair.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AffineBaseChangeCohomologyModel | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.Algebra.Homology.AffineBaseChangeGlobalSectionsFactorization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.Algebra.Homology.AffineBaseChangeIntoPullback | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.Algebra.Homology.AffineBaseChangeSourceModel | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.Algebra.Homology.AffineBaseChangeTildeCanonicalGlobalComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.Algebra.Homology.AffineBaseChangeTildeCoordinates | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.Algebra.Homology.AffineBaseChangeTildeGlobalComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.Algebra.Homology.AffineBaseChangeTildeMateFactorization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.Algebra.Homology.AffineBaseChangeTildeMateIdentityFactorization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.Algebra.Homology.AffineBaseChangeTildeOrdinaryComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.Algebra.Homology.AffineBaseChangeTildeRepresentative | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.Algebra.Homology.AffineBaseChangeTildeSourceModel | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.Algebra.Homology.AffineBaseChangeTildeStalkComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.Algebra.Homology.AffineTensorPullbackStalkCoordinates | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.Algebra.Homology.AffineTildeDerivedTensorMate | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.Algebra.Homology.AffineTildeTensorSourceComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCoreFinal | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePreBase | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonHelpers | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.Algebra.Homology.SingleComplexAffineBaseChange | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.Algebra.Homology.SingleComplexAffineBaseChangeCore | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineAlternatingCechBaseChangeFactorization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineAlternatingCechPinnedMate | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineCoordinateComparisonChartCocycle | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineCoordinateComparisonCoherence | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineCoordinateComparisonData | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineCoordinateDerivedComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineDerivedPullbackModuleModel | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.AffineDescentStageRealization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineExtensionSectionsModelFactorization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineExtensionSectionsModelMate | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineExtensionSectionsUnit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineFreeLowestMatrixLocus | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.AffineFreeResidueSectionsDerivedModel | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeFactorization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineKFlatPullbackChartComparison | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.AffineKFlatResiduePullbackModel | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineLocalSheafificationTorAmplitude | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineModelCoherentObjectComparisons | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineModelComparisonData | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineModelComparisonOfBottomModels | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineModelHomTransportAssembly | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineModelLimitHomEquationOfCoherentObjects | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineModelStageHomEquationOfCoherentObjects | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineMorphismHomOutOfPerfect | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineOpenPerfectSourceModel | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.AffinePerfectChainGeometricModels | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffinePerfectChainHomPresentation | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffinePerfectHomPresentation | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffinePerfectResidueModelNaturality | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffinePullbackModelComparisonsIsIso | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.AffinePullbackPerfectDetectsIso | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffinePullbackSectionsModelUnit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffinePullbackSectionsUnitUncancelled | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineRelativelyFlatCanonicalModuleBaseChange | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineSectionsBaseChangeMate | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineSectionsBaseChangeUnitSquare | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineSectionsSquareComparisonCoherence | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineSectionsSquareMatePathUnit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineSpecifiedModelChainComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineSpectrumBaseChangeComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineSpectrumCanonicalComparisonSquare | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineSpectrumComparisonCancellation | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineSpectrumComparisonSourceTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineSpectrumCompositionCounitSquare | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineSpectrumCompositionUnitSquare | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineSpectrumCoordinateRepresentatives | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineSpectrumCounitCompatibility | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineSpectrumCounitSquare | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineSpectrumDerivedCoordinates | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineSpectrumDirectImageCoordinates | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineSpectrumMateCompatibility | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineSpectrumPullbackSquareCoherence | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineSpectrumRepresentativeMap | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineSpectrumStalkCondition | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineSpectrumStalkConjugacy | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineSpectrumUnitNormalization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.AffineSquareKFlatModelIso | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.BaseChangeMapCech | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.BaseChangeOpenFixedCounits | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.BaseChangeOpenFixedCounitsCompatibility | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.BottomChainModelPullbackTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.BottomFreeChainDerivedSquare | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.BottomFreeChainPullbackComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.BottomFreeChainPullbackSquare | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.CanonicalModuleBaseChangeAffineChartComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.CanonicalModuleBaseChangeAffineLocality | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.CanonicalModuleBaseChangeIsoComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.CanonicalModuleBaseChangeIsoComparisonC0 | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.CanonicalModuleBaseChangeIsoComparisonCompat | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.CanonicalModuleBaseChangeOpenComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.CanonicalModuleBaseChangeOpenComparisonC0 | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.CanonicalModuleBaseChangeOpenComparisonCompat | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.CanonicalPullbackTensorMonoidalRealization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.CanonicalRelativeMVOpenSquareCoefficientCoherence | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.CanonicalSingleBaseChangeComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.CanonicalStructureMapBaseChange | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.CartesianTensorDataComparison | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.CoefficientSquareCoordinateChange | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.CoefficientSquarePasting | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.ConnectiveRankOneModelStalk | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.CounitStalkConditionFromLocalizedComparison | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.DerivedAdjoint | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeBaseCoordinates | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeCodomainIso | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeCoordinateNaturality | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeDomainIso | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeHorizontal | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeHorizontalMate | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeHorizontalPasting | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundary | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundaryData | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalData | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalPullback | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalShift | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisSquares | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeNaturality | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeOpenRestriction | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeOpenTranspose | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeOpenUnit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedBaseChangePasting | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeSourceIso | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeSourceTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeTopIso | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedCompositionCounitApex | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedDirectImageInternalHom | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedDirectImagePastedCounitNormalization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedDirectImageSquareMate | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedExactStructures | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.DerivedFiberBetti | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedFiberCohomologyBaseChange | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.DerivedFiberCohomologyFunctor | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedFiberOpenFactorization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedHomPushforwardKFlatModel | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.DerivedInternalHomPullbackAdjunction | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedInternalHomPullbackMateSections | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedOpenPullbackHomology | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.DerivedProjectionMateOpenRestrictionComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullback | unclaimed | hide the original chosen construction and expose its equality/specification API |
| Sheaf.AlgebraicGeometry.DerivedPullbackAcrossUniverses | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackAcrossUniversesLeftDerived | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.DerivedPullbackAcrossUniversesMonoidalAdjunction | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackAcrossUniversesRetraction | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackComposition | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionAssocKFlat | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionCoherence | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionCounitNormalization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionIsIso | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionLocalizedCounit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMateUnit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionTensorKFlat | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionUnitKFlat | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackConeSquareTransposition | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackEvaluationSections | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatConeCounitEquality | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatCounitAdjustmentFactor | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatCounitData | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatTensorModel | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalDescent | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalModel | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.DerivedPullbackPerfect | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackPreservesQCoh | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackRecordedComposition | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.DerivedPullbackShiftedUnitIsoData | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.DerivedPullbackSingleCohomology | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackStructureSheaf | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorAssociativity | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorProduct | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorSuccessiveNormalization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitCounit | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitNormalization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedPushforwardSquareMateUnit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedResidueUnitBetti | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedRestrictionTensorNaturality | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.DerivedSingleOpenLocus | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedSquareVerticalPasting | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DerivedTensorPrecompositionOpen | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.FieldFibreHomology | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.FilteredCartesianPerfectDescent | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.FiniteFreeResidueModelPullback | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.FlatAffineGlobalHomComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.FlatComparisonPreservesCountableCoproducts | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.FlatDerivedStructureUnit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.FlatDerivedStructureUnitProperties | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.FlatModuleCanonicalDerivedPullback | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.FlatModuleCanonicalDerivedPullbackAux | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.FlatPrecomposePus | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.FlatTelescopeNormalizationIsIso | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.FlatTelescopeNormalizationUnshiftedIsIso | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.FlatTelescopePullbackSumColimit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.FlatTelescopeSumComparisonIsIso | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.GlobalHomBaseChangeCounitTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.GlobalHomBaseChangeExchange | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.GlobalHomOriginalCounitNormalization | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackCounitHZero | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackCounitIsomorphism | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.GlobalSectionsBaseChangeMate | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.HigherDirectImageDerivedModel | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.HomotopyPullbackSquareLocalization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.HorizontalDualityMateCommutativity | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.HorizontalDualityMateComparisons | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.HorizontalDualityMatePasting | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.HorizontalOrdinaryForwardFixedPasting | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.HorizontalRectangleInverseMateFixedTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.HorizontalTransferInverseFormula | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.InternalHomBaseChangeExchange | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.IsoPullbackStalkCohomology | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.IsomorphicSingleTensorCounit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.IsomorphicSingleTensorCounitEquation | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.IsomorphicSingleTensorCounitTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.IsomorphismPullbackCounit | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.KFlatPullbackAdjunctionComparison | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.KFlatStalkResidueCohomology | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.LocalKFlatPullbackModel | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.LocalZeroBottomModelPullback | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.LocalZeroBottomTruncation | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.LocalizedCartesianFlatSingleComparison | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.LocalizedMixedDerivedPullback | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.LocalizedMixedPullbackFiniteFreeModel | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.LocalizedPullbackPerfectCounit | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.LocalizedPullbackPerfectModel | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.LocalizedResidueHomology | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.LocalizedResidueHomologyRestriction | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.LocalizedResidueHomologySheafRestriction | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.LocalizedStrictPerfectResidueHomology | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.LocallyFiniteTorDimension | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.LowestResidueModelWithinOpen | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.MixedAffineSectionsBaseChangeMate | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.MixedAffineSectionsChartModelFactorization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.MixedAffineSectionsKFlatComparisonIso | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.MixedAffineSectionsPullbackMate | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.MixedAffineSectionsPullbackUnitNormalization | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.MixedExtensionSectionsUnit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeCounitTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.MixedGlobalHomBaseChangeExchange | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.MixedGlobalSectionsBaseChangeMate | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.MixedHomDirectImageComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.MixedHomTensorPullbackIso | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.MixedInternalHomBaseChangeExchange | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.MixedPerfectInternalHomPullbackIsIso | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.MixedPullbackSectionsCounitUnit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.MixedPullbackSquareTensorCoherence | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.MixedSectionsBaseChangeUnitSquare | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.MixedSectionsSquareComparisonCoherence | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.MixedTensorPairingBaseChange | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.MixedTensorPairingBaseChangeNaturality | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.MixedTensorPairingBaseChangeTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.ModulePullbackComparisonDegreeAutomorphism | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.ModulePullbackComparisonIsoTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.ModulePullbackComparisonTargetAutomorphism | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.NewBaseOpenMateFactorization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.NoetherianApproximationData | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.NormalizedInternalHomPullbackComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenComparisonIntoPullbackTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenDerivedStalkIso | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenFlatComplexStalkCounit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenPinnedCounitHomotopyRestriction | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeSquare | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroApex | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroSource | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroTarget | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenPinnedSourceCounitTriangle | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenPinnedTargetCounitTriangle | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenPinnedTensorCounitTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenRestrictedCanonicalSquare | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenRestrictedComparisonComposition | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenRestrictedComparisonCore | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenRestrictedComparisonTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenRestrictedCounitCompatibility | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenRestrictedCounitFactorization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenRestrictedCounitFactorizationAux | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenRestrictedRepresentativeData | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenRestrictedTensorComplexIso | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenRestrictionAdjunctionHomDescent | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenRestrictionTensorCounitDescent | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OpenSingleCoefficientTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.OriginalCounitAdjunctionTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectComplexDescent | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectDegreeZeroFibreCriterion | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectDescendMorphisms | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectDescentCommonLocalModels | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectDescentOnOpen | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectDescentOpenEventualModel | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectFiniteResidueCohomologyBounded | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectGeneratorPullback | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.PerfectHomCochainCounit | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.PerfectHomComparisonTriangle | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomCompositionPrism | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomContinuity | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomContinuityAffine | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomContinuityOn | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomLocalComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisGeometricColumnsOdd | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisLocalRows | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisStageRows | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisStageRowsCore | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomMayerVietorisTriangleCocone | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomOpenComparisonMateIso | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomOpenMateResolutionNormalization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedData | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedEquivFields | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedMaps | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedPinnedEquiv | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictedPinnedMaps | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictionMap | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomOpenRestrictionTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomOpenStageData | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.PerfectHomOpenStageMaps | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomOpenStagePresentation | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomOpenTestBijective | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomOpenTransportSquare | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomPresentation | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomPushPullCocone | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomStageColimit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectHomTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectImmersionTensorAcrossUniverses | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectInternalHomPullbackIsIso | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectJumpLoci | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectLocalDegreeZeroUnit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsDescendedTransition | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsEventuallyCompatible | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsStageComparisons | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectLocalModelsStageGluing | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectLowestCohomologyLocus | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectLowestMatrixCharts | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectLowestMatrixClosedLocus | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectLowestRankBoundOpen | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOfOpenPullbacks | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.PerfectOpenGluingData | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOpenGluingDataOfGlobalModel | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.PerfectOverlapCanonicalCounitU | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapCanonicalGammaLocal | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapCanonicalLocalCubeU | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapCanonicalOpenPrismU | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapCanonicalSiteTriangle | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapCompositeCounitFactor | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapCompositeObjectPin | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapCompositeSiteComponent | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapCompositeStageMap | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapCompositeStageTail | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapCompositionCube | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapHomContinuityData | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapHomPresentation | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapLocalSiteTriangle | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapNestedOpenSquarePasting | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackNormalization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapNestedSiteCompatibility | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreBase | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreCanonicalFamily | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreOfData | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapOpenLiftCharacterization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapOpenLiftComponents | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapOpenPrismUOfData | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapOpenSquareComponents | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapOpenSquareCube | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapProjectionCompositeAbstract | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapProjectionCompositionComponent | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapProjectionPrism | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapProjectionTailAbstract | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapProjectionTriangleU | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapSquarePrismAbstract | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalenceFunctor | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapStageObjectTail | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapStageTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionComponent | D3 | prove the component using the fixed functor interface |
| Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonCore | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapTransitionComparisonDiagram | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapTransportPrism | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapTransportPrismHom | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectPseudoCoherentLocallyFiniteTor | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.PerfectRHomTensorComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectRestrictionClassesSmall | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.PerfectRightAdjointTensorHomComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectSummand | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectTensorHomDuality | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectUniversalH0BottomModel | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectUniversalH0LocalChainModel | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectUniversalH0TruncationPullback | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectUniversalLowestCohomologyPullback | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectUniversalLowestZeroModel | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.Picard.CanonicalDegreeZeroMateSquare | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComposition | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackSquare | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.Picard.CounitBaseChangeDegreeZeroComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.Picard.TensorDegreeZeroMateSquare | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.Picard.TensorSingleBaseChangeSquare | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PicardAffineProjectiveBaseChange | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PicardCoefficientTransposePasting | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PicardDerivedCoefficientMap | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PicardDerivedModelSections | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PicardDerivedUnitNormalizationComposition | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTranspose | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposeFactorization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposePasting | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposeSingle | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyNegative | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionMapBijective | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PicardDirectImageUnitMorphismPullback | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.PicardTermwiseCompositeCounit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PicardTermwiseCompositeCounitCore | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PicardTermwiseModelComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PicardTermwiseModels | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PicardTermwiseSingleMapComposition | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PicardTermwiseSourceCoherence | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PicardTermwiseTargetCoherence | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PinnedBaseChangeMateShifts | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PinnedDerivedAdjunctionShifts | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PinnedPullbackCompositionShifts | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PinnedPullbackCounitShifts | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PinnedSingleBaseChangeShift | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PinnedSingleTensorShifts | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.ProjectionFormulaLocality | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.ProjectionFormulaLocalityGlobalToLocal | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.ProjectionFormulaLocalityLocalToGlobal | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.ProjectionMateAffineChartCertificate | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.ProjectionMateAffineChartTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.ProjectionMateSchemeIsoTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.ProperDirectImageTensorLowerBound | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeHbeta | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.ProperSupportAffineTensorRestriction | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.ProperSupportDerivedProjectionFormula | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PullbackStalkTensorComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.QCohInverseBaseChangeMate | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.QCqsDerivedProjectionIsoUniverses | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.QCqsDerivedProjectionMate | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.QCqsProjectionMateAffineDescent | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.QCqsProjectionMateAffineLocus | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.QCqsProjectionMateShiftedUnit | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.QCqsSheafRHomAdjunction | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RankOneResidueStalkComponent | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RecordedPerfectHomContinuity | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RecordedPerfectHomNormalization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RecordedPerfectHomTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RectangleInverseBaseChangeMateTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RectangleOrdinaryGeometricComparisons | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RectangleOrdinaryGeometricDirect | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RectangleOrdinaryGeometricPullback | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RectangleOrdinaryPastingComparisons | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RectangleQCohComparisonLifts | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RectangleQCohOrdinaryCompatibility | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVBoundaryCompletion | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVCanonicalTriangles | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVCompositeBaseChangeCounit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVCompositeBaseChangePrefix | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVCompositeBaseChangeTargetTranspose | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVConePresentation | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVCoverChainSquare | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVCoverHomotopyData | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVCoverRows | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVDirectImageHomotopyComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowRoof | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVDirectImageRows | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsCore | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsMates | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsOverlapMate | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsPreoverlap | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVDirectImageSquareLocalization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVExactOpenComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVInverseOpenComparisons | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVInverseOpenIso | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVInverseOpenMate | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVMaps | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVNormalizedCoefficientRoof | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVOpenCoefficientTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVOpenSquareCoefficientCoherence | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVOpenSquareCounit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVPinnedTriangleComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVPinnedVertexComparisons | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVResolvedOpenRoofComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofMateComparisons | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofMiddleMateComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofOpenMateComparisons | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofVertexNormalization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVResolvedRowRoofComparisons | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVRestrictionFirst | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVRestrictionSecond | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVRestrictionSourceCounit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVRestrictionSquares | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVRestrictionTargetCounit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMVSESPresentation | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeMayerVietoris | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeTensorPullbackHomologyComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativeTensorPullbackKFlatModel | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.RelativeTorPullbackTensorLowerBound | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativelyFlatCanonicalModuleBaseChange | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChange | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.ResidueHomologyRankOneCoefficient | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.ResidueStalkHomologyMapComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RightAdjointMateNewBaseOpen | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpen | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RightAdjointMateOldBaseOpenFactorization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RightAdjointMateSchemeIsoTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RightAdjointMateSchemeIsoTransportBase | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RightAdjointMateSchemeIsoTransportMate | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RightAdjointMateSuccessiveBaseChange | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonComponents | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonNatural | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonProjection | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SchemeDerivedMateEvaluation | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SchemeIsoDerivedFunctorComparisons | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SchemeIsoInverseBaseChangeTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SchemeIsoLiftedComparisonCounit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SchemeIsoRightAdjointNormalized | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SchemeIsoSecondMateNormalizedSquare | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexAffineSpectrumCoordinates | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.SingleComplexInheritedTensorCondition | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexNestedCoefficientCoherence | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenAffine | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenAffineUnion | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenBaseChangeCalculation | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenBaseChangeComparisons | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenBaseChangeIdentity | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenCoordinateStalkEquivalence | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenCoordinateStalkTransportData | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenCoordinateTransport | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenCounitCompatibility | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenNestedComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenPinnedAdjunction | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenPinnedComposition | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenPinnedCounitUnit | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenPullbackCounitHomotopyFactorization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenPullbackCounitRepresentative | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenPullbackCube | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictedCounitCancellation | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionData | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenSquareComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenStalkCondition | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenStalkConjugacy | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenTermwiseComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenTermwiseCounitCompatibility | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenTop | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenUnion | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenUnionCompatibleChainData | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenUnionSESCore | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenUnionSESObjects | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenUnionSESPresentation | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenUnionTriangles | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenUnitNaturality | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexOpenUnitSquareFactorization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexQcqsHomologyMono | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleComplexTargetLocality | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SingleOpenTensorCoefficientCoherence | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SmoothProperDiagonalTensorFormula | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SmoothProperQCohData | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCase | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCaseCore | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCaseData | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.StalkComparisonCoordinateInvariance | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparison | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIsIso | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIso | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIsoCore | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChange | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.StandardSingleBaseChangeMap | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.StandardSingleBaseChangeTopRestriction | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.StandardSingleBaseChangeTopRestrictionAux | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitAffine | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalization | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationCompletion | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationHomology | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationPresentationData | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnionEquation | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.StandardSingleOpenDerivedArrow | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.StandardSingleOpenRelativeArrow | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.StandardSingleOpenStalkArrow | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.StandardSingleStalkFlatCounitModel | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SupportedOpenTensorDirectImageComparisons | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.SupportedOverlapRestrictionData | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.TensorCoordinateIdentifications | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.TensorCounitCoordinateEquation | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.TensorCounitOneKFlatCoordinates | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.TensorSinglePullbackComposition | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.TensorStalkChainCoordinates | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.TensorStalkComparisonSquares | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.TensorStalkFixedMapSquare | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.TorAmplitudeOpenLocal | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.TorIndependentPerfectPullbackComparison | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.TwoOpenComparisonDiagram | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.UnionBoundedAboveModel | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.UniversalLowestFiberRanks | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.ZeroBottomArrowAffineChainModel | unclaimed | use the fixed specification API in the implementation; existing signatures stay identical |
| Sheaf.AlgebraicGeometry.ZeroBottomArrowPullbackLocal | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapProjectionTwoFactors | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapStageObjectFactors | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapStageTransportComponent | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapTailNormalForm | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionAt | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |
| Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionFactors | unclaimed | same fixed functor by derivedPullback_eq_choose; existing statement unchanged |

## Status

landed 20261017T191956-L-3002698 2026-10-17 (merge of deliver/D3/Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionComponent)
