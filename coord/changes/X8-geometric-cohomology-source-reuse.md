# AlgebraicGeometry.WeilSheaf.cohomologyLinearEquivOfGeometricFiberIso_map_frobenius

## Reason

The source library already defines and proves both the canonical geometric cohomology
transport and the exact Frobenius-conjugacy theorem. The old Sheaf files duplicate the
same fully qualified names. Their only external direct user is
`WeilConjectures.WeilSheaf.PoincareDuality`; its private proof import is redirected to
`WeilConjectures.WeilSheaf.CohomologyGeometricConjugacy`.

The old construction locally defines adicΓ, adicLowerStarΓIso and cohomologyCarrierIso;
the source implementation names these comparisons globally and proves their naturality
and Frobenius compatibility. Both constructions identify the actual constant Weil
cohomology carrier with homology of derived global sections, apply pushforward along e
and its coefficient-unit comparison, then identify the target carrier. The source
implementation supplies this same canonical transport with its compatibility API.
There is no arbitrary choice of a cohomology equivalence, additional hypothesis, or
weakened conclusion. The definitions are not claimed definitionally equal: the obsolete
implementation is replaced consistently at its only external user. No target statement
or definition occurring in a target statement changes: this equivalence occurs only in
a proof of PoincareDuality. The unit route, including the geometric conjugacy step,
remains in use through the existing proved source theorem.

## Old

The withdrawn definition, verbatim:

```lean
noncomputable def cohomologyLinearEquivOfGeometricFiberIso
    (k k' : Type u) [Field k] [Finite k] [Field k'] [Finite k']
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)] [Fact (ringChar k' ≠ l)]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k'))]
    [QuasiCompact (X ↘ Spec (.of k))] [QuasiSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k'))] [QuasiSeparated (Y ↘ Spec (.of k'))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k'))]
    (e : (Y ↘ Spec (.of k')).geometricFiber ≅ (X ↘ Spec (.of k)).geometricFiber) (i : ℤ) :
    ((WeilSheaf.adicConstant k' l Y).cohomology i).carrier ≃ₗ[PadicAlgCl l]
      ((WeilSheaf.adicConstant k l X).cohomology i).carrier := by
  let adicΓ (l : ℕ) [Fact l.Prime] (Z : Scheme.{u}) :
      ProEtale.AdicSheaf l Z ⥤ WeilCoefficients.{u} l :=
    ProEtale.AdicSheaf.forget Z ⋙ Sheaf.Γ _ _
  let adicLowerStarΓIso (l : ℕ) [Fact l.Prime]
      {Z W : Scheme.{u}} (g : Z ⟶ W) :
      ProEtale.adicLowerStar l g ⋙ adicΓ l W ≅ adicΓ l Z :=
    Functor.isoWhiskerLeft (ProEtale.AdicSheaf.forget Z)
      (ProEtale.globalSectionsLowerStarIso (WeilCoefficients.{u} l) g)
  let cohomologyCarrierIso (k : Type u) [Field k] [Finite k]
      (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)]
      (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [QuasiCompact (X ↘ Spec (.of k))] [QuasiSeparated (X ↘ Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))] (i : ℤ) :
      ((adicΓ l (X ↘ Spec (.of k)).geometricFiber).rightDerivedFunctor ⋙
        _root_.DerivedCategory.homologyFunctor _ i).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (ProEtale.AdicSheaf.unit l (X ↘ Spec (.of k)).geometricFiber)) ≅
        (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
          ((WeilComplex.homologySheaf i).obj ((WeilComplex.derivedLowerStar
            (X ↘ Spec (.of k))).obj
              (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k l X)))).obj.carrier.X := by
    let a := X ↘ Spec (.of k)
    let f := Scheme.Hom.geometricFiberMap a (comp_over a (Spec (.of k)))
    let G := adicΓ l (Spec (.of k) ↘ Spec (.of k)).geometricFiber
    let F := adicΓ l a.geometricFiber
    let W := ProEtaleWeilSheaf.lowerStar k l a
    let M := (_root_.DerivedCategory.singleFunctor _ 0).obj (WeilSheaf.adicConstant k l X).obj
    let K := W.rightDerivedFunctor.obj M
    have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
      (ProEtale.AdicSheaf l a.geometricFiber) ℤ
    have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
      (ProEtale.AdicSheaf l a.geometricFiber) ℤ
    let e : (IsoAlgebra.forget _).mapDerivedCategory.obj K ≅
        (ProEtale.adicLowerStar l f).rightDerivedFunctor.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (ProEtale.AdicSheaf.unit l a.geometricFiber)) :=
      (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso _ _).app _ ≪≫
        Functor.mapIso _ (((IsoAlgebra.forget _).mapDerivedCategorySingleFunctor 0).app
          (WeilSheaf.adicConstant k l X).obj)
    have : G.Additive := by dsimp [G, adicΓ]; infer_instance
    have : PreservesFiniteLimits G := by dsimp [G, adicΓ]; infer_instance
    have : G.PreservesEpimorphisms := by dsimp [G, adicΓ]; infer_instance
    have : G.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels G
    have : PreservesFiniteColimits G := Functor.preservesFiniteColimits_of_preservesHomology G
    let e₀ := (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
      (ProEtale.adicLowerStar l f) G).symm ≪≫
        Functor.rightDerivedFunctorNatIso (adicLowerStarΓIso l f)
    let e₁ := ((IsoAlgebra.forget _).mapDerivedCategoryHomologyFunctorIso i).app K
    let e₂ := (G.mapDerivedCategoryHomologyFunctorIso i).app
      ((IsoAlgebra.forget _).mapDerivedCategory.obj K)
    exact ((G.mapIso e₁) ≪≫ e₂ ≪≫
      (_root_.DerivedCategory.homologyFunctor _ i).mapIso
        (G.mapDerivedCategory.mapIso e ≪≫ e₀.app _)).symm
  let FX := adicΓ l (X ↘ Spec (.of k)).geometricFiber
  let L := ProEtale.adicLowerStar l e.hom
  let U := ProEtale.AdicSheaf.unit l (Y ↘ Spec (.of k')).geometricFiber
  let M := (_root_.DerivedCategory.singleFunctor _ 0).obj U
  let eΓ := (Functor.rightDerivedFunctorCompIso' L FX (adicLowerStarΓIso l e.hom)).app M
  let eU := (L.singleFunctorCompRightDerivedFunctorIso).app U ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso (ProEtale.adicLowerStarUnitIso l e)
  let eD := eΓ.symm ≪≫ FX.rightDerivedFunctor.mapIso eU
  exact WeilCoefficients.linearEquivOfIso
    ((cohomologyCarrierIso k' l Y i).symm ≪≫
      (_root_.DerivedCategory.homologyFunctor _ i).mapIso eD ≪≫
        cohomologyCarrierIso k l X i)
```

The withdrawn theorem, verbatim:

```lean
theorem cohomologyLinearEquivOfGeometricFiberIso_map_frobenius
    (k k' : Type u) [Field k] [Finite k] [Field k'] [Finite k']
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)] [Fact (ringChar k' ≠ l)]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k'))]
    [QuasiCompact (X ↘ Spec (.of k))] [QuasiSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k'))] [QuasiSeparated (Y ↘ Spec (.of k'))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k'))]
    (r : ℕ) (e : (Y ↘ Spec (.of k')).geometricFiber ≅ (X ↘ Spec (.of k)).geometricFiber)
    (he : (Y ↘ Spec (.of k')).geometricGaloisFrobenius.hom ≫ e.hom =
      e.hom ≫ ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ r).hom) (i : ℤ)
    (x : ((adicConstant k' l Y).cohomology i).carrier) :
    cohomologyLinearEquivOfGeometricFiberIso k k' l X Y e i
        (((adicConstant k' l Y).cohomology i).frobenius x) =
      (((adicConstant k l X).cohomology i).frobeniusEnd ^ r)
        (cohomologyLinearEquivOfGeometricFiberIso k k' l X Y e i x) := by
  sorry
```

The consumer imported `Sheaf.WeilSheaf.CohomologyGeometricConjugacy` privately.

## New

Both Sheaf modules are withdrawn via deleted.txt. The two original DAG nodes now
attach to their existing declarations in the source modules
`WeilConjectures.WeilSheaf.CohomologyGeometricEquivalence` and
`WeilConjectures.WeilSheaf.CohomologyGeometricConjugacy`. There is one implementation
of each name. The retained explicit source definition is:

```lean
noncomputable def cohomologyLinearEquivOfGeometricFiberIso
    (k k' : Type u) [Field k] [Finite k] [Field k'] [Finite k']
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)] [Fact (ringChar k' ≠ l)]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k'))]
    [QuasiCompact (X ↘ Spec (.of k))] [QuasiSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k'))] [QuasiSeparated (Y ↘ Spec (.of k'))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k'))]
    (e : (Y ↘ Spec (.of k')).geometricFiber ≅ (X ↘ Spec (.of k)).geometricFiber) (i : ℤ) :
    ((WeilSheaf.adicConstant k' l Y).cohomology i).carrier ≃ₗ[PadicAlgCl l]
      ((WeilSheaf.adicConstant k l X).cohomology i).carrier :=
  WeilCoefficients.linearEquivOfIso
    (cohomologyCarrierIso k' l Y i ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso (ProEtale.derivedGlobalSectionsUnitIso l e) ≪≫
        (cohomologyCarrierIso k l X i).symm)
```

The theorem retains verbatim the signature shown above and its existing complete proof:
invert the geometric conjugacy, use derivedGlobalSectionsUnitIso_trans, apply homology,
and conjugate by cohomologyCarrierIso. The power comparison is proved by induction,
including exponent zero. PoincareDuality changes only this line:

```lean
import WeilConjectures.WeilSheaf.CohomologyGeometricConjugacy
```

## Users

The table includes both withdrawn files, all transitive importers returned by
`tools/downstream.py`, and the adapted module. Only PoincareDuality mentions the
withdrawn names outside the two withdrawn files. Holder status was read before delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| Sheaf.Paper.WeilOne | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | X8 | Withdrawn duplicate; its node now attaches to the existing source implementation with identical name and signature. |
| Sheaf.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | Withdrawn duplicate; its node now attaches to the existing source implementation with identical name and signature. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| TargetsCheck | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.Statement | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.WeilSheaf.CohomologyDegreeZero | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.WeilSheaf.CohomologyZero | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.WeilSheaf.DirectImageStalkMap | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Only direct external user of both names; replace one private import. The source theorem proves the same conjugacy statement for the canonical equivalence. All signatures and proof bodies unchanged. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.ZetaFunction.TraceFormula | X5 | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Transitive importer; neither name occurs here. PoincareDuality imports the replacement privately, so its public interface and this module are unchanged. |

## Status

landed 20261019T112621-L-3962193 2026-10-19 (merge of deliver/X8/Sheaf.WeilSheaf.CohomologyGeometricConjugacy)
