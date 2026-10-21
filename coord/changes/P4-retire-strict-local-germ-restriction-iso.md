# AlgebraicGeometry.Etale.isIso_strictHenselizationStalkRestriction retirement

## Reason

coord/retire-items.tsv assigns removal of the duplicate SHEAF theorem. It already has
zero holes. The adopted theorem uses strictLocalization; the two live SHEAF consumers
use the actual small coordinate-ring colimit model. Replacing their scheme by the adopted
scheme would change their definitions. Instead retain their exact restriction maps and
prove their invertibility using a general criterion for a pointed etale section cone.
The new criterion has arbitrary T, g, N and y, and assumes invertibility of the specified
identity-neighbourhood germ of the pulled-back sheaf. It constructs no strict-local model
and has a complete proof. It is not a renamed specialized strict-local theorem.

## Old

The following theorem is in namespace AlgebraicGeometry.Etale:

```lean
theorem isIso_strictHenselizationStalkRestriction
    {S : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1})
    (r : (Scheme.pointSmallEtale s).sheafFiber.obj G ⟶
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).obj
        ((upperStar AddCommGrpCat.{v + 1}
          (Scheme.strictHenselizationStructuralMap s)).obj G))
    (hr : (strictLocalSectionCone s).IsRestriction G r) : IsIso r
```

The two live consumers use `isIso_strictHenselizationStalkRestriction s G r hr` (respectively
with x in place of s). Their r is the existing Classical.choose of the unique restriction
on strictLocalSectionCone. strictLocalCohomologySourceIso is `asIso r` followed by the
same inverse-image/homology comparison as before; strictLocalCohomologySourceLegs uses
its hom. No definition or theorem statement in those consumers is removed or changed.

The original public source-isomorphism definition is:

```lean
noncomputable def strictLocalCohomologySourceIso {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    (Scheme.pointSmallEtale s).sheafFiber.obj
        ((DerivedCategory.Plus.homologyFunctor _ n).obj L) ≅
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).obj
        ((DerivedCategory.Plus.homologyFunctor _ n).obj
          ((upperStar AddCommGrpCat.{v + 1}
            (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlus.obj L)) := by
  classical
  let G := (DerivedCategory.Plus.homologyFunctor _ n).obj L
  let r := Classical.choose ((strictLocalSectionCone s).existsUnique_restriction G)
  have hr := (Classical.choose_spec ((strictLocalSectionCone s).existsUnique_restriction G)).1
  letI := isIso_strictHenselizationStalkRestriction s G r hr
  exact asIso r ≪≫
    (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}).mapIso
      ((Functor.mapDerivedCategoryPlusHomologyFunctorIso
        (upperStar AddCommGrpCat.{v + 1}
          (Scheme.strictHenselizationStructuralMap s)) n).app L)
```

## New

The twin is withdrawn with deleted.txt, and its DAG node is attached to the unchanged
adopted theorem in WeilConjectures.AlgebraicGeometry.StrictLocalGermRestrictionIso.
The model-independent replacement API is in namespace
AlgebraicGeometry.Etale.PointedEtaleSectionCone:

```lean
theorem isIso_restriction
    {S T : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    {s : Spec (.of Ω) ⟶ S} {I : Type v} [Category.{v} I]
    {N : I ⥤ (Scheme.pointSmallEtale s).fiber.Elements} {g : T ⟶ S}
    (c : PointedEtaleSectionCone g N)
    (y : Spec (.of Ω) ⟶ T) (hbase : y ≫ g = s)
    (hpoint : ∀ i : I, y ≫ (c.section_ i).left ≫
      pullback.fst (N.obj i).1.hom g = (N.obj i).2.left)
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1})
    (hγ : IsIso ((Scheme.pointSmallEtale y).toPresheafFiber
      (Scheme.Etale.mk (𝟙 T)) (Over.homMk y (Category.comp_id y))
      ((upperStar AddCommGrpCat.{v + 1} g).obj F).obj))
    (r : (Scheme.pointSmallEtale s).sheafFiber.obj F ⟶
      (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
        ((upperStar AddCommGrpCat.{v + 1} g).obj F))
    (hr : c.IsRestriction F r) : IsIso r
```

The adapted public source-isomorphism definition is:

```lean
noncomputable def strictLocalCohomologySourceIso {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    (Scheme.pointSmallEtale s).sheafFiber.obj
        ((DerivedCategory.Plus.homologyFunctor _ n).obj L) ≅
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).obj
        ((DerivedCategory.Plus.homologyFunctor _ n).obj
          ((upperStar AddCommGrpCat.{v + 1}
            (Scheme.strictHenselizationStructuralMap s)).mapDerivedCategoryPlus.obj L)) := by
  classical
  let G := (DerivedCategory.Plus.homologyFunctor _ n).obj L
  let r := Classical.choose ((strictLocalSectionCone s).existsUnique_restriction G)
  have hr := (Classical.choose_spec ((strictLocalSectionCone s).existsUnique_restriction G)).1
  letI : IsIso r := by
    let : Algebra (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω :=
      (Scheme.descResidueField (Scheme.stalkClosedPointTo s)).hom.toAlgebra
    obtain ⟨hlocal, hstrict, _, _, σ, ⟨hpoint, hbase⟩, _⟩ :=
      strictHenselizationResidue s rfl
    let := hlocal
    let y := Spec.map (CommRingCat.ofHom
      (((IntermediateField.val
        (separableClosure (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
          σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselizationRing s))))
    have hy : y default = IsLocalRing.closedPoint (Scheme.strictHenselizationRing s) := by
      rw [Subsingleton.elim (default : Spec (.of Ω)) (IsLocalRing.closedPoint Ω)]
      change PrimeSpectrum.comap
        ((((IntermediateField.val
          (separableClosure (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω)).toRingHom).comp
            σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselizationRing s)))
        (IsLocalRing.closedPoint Ω) = _
      rw [PrimeSpectrum.comap_comp]
      exact IsLocalRing.PrimeSpectrum.comap_residue _ _
    refine (strictLocalSectionCone s).isIso_restriction y hbase ?_
      G ((Scheme.strictlyHenselianSections_geometricStalk_isIso hstrict y hy).1 _) r hr
    intro i
    let n := (equivSmallModel.{v}
      (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj i
    change y ≫ (strictLocalNeighbourhoodSection s i).left ≫
      pullback.fst ((Scheme.AffineEtale.Spec S).obj n.1).hom
        (Scheme.strictHenselizationStructuralMap s) = n.2.left
    dsimp only [n]
    simp only [strictLocalNeighbourhoodSection,
      MorphismProperty.Over.homMk, Over.homMk, CostructuredArrow.homMk, pullback.lift_fst]
    simpa only [Scheme.isoSpec_Spec_inv, Category.assoc] using hpoint i
  exact asIso r ≪≫
    (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}).mapIso
      ((Functor.mapDerivedCategoryPlusHomologyFunctorIso
        (upperStar AddCommGrpCat.{v + 1}
          (Scheme.strictHenselizationStructuralMap s)) n).app L)
```

Each consumer obtains the compatible geometric closed lift of its existing small model
from strictHenselizationResidue. The residue prime-comap formula proves closedness;
strictlyHenselianSections_geometricStalk_isIso supplies the identity germ isomorphism.
The limit-leg factorization proves the hypothesis on every section. The general criterion
then supplies IsIso of the original r, with no change to the construction of r.

Only this proof of the proposition IsIso r changes in the public source-isomorphism
definition. Proof irrelevance makes the resulting `asIso r` unchanged. A temporary Lean
probe compares the new strictLocalCohomologySourceIso with the old definition verbatim
and proves equality by rfl. The source legs are consequently also unchanged. The constant
comparison is a theorem, and retains its full signature and all its coefficient maps.

No adopted source file is modified. No Challenge statement or definition used by it
changes mathematical meaning; the consumer definition change still receives the ordinary
independent definition review. No data is chosen from an unproved existence theorem.

## Users

The following list contains all 28 live downstream modules returned by downstream.py,
the four archived direct importers, and the retired item. A textual search found only
the two adapted live consumers calling the retired declaration. Other live modules use
the preserved source isomorphism and source legs. Quarantine archives are not withdrawn,
restored, or modified; all their DAG attachments and dependencies remain intact.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictLocalGermRestrictionIso | P4 | Withdraw the duplicate theorem module and retain the canonical node via the adopted theorem. |
| Sheaf.AlgebraicGeometry.EtaleInjectiveSectionsComparison | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.LocallyConstantTorsionLocalAcyclicity | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalCohomologyGerms | unclaimed | Remove the public twin import; prove IsIso of the same chosen r with the general criterion. The source isomorphism and source legs keep their types and maps. |
| Sheaf.AlgebraicGeometry.StrictLocalConstantComparison | unclaimed | Replace the private twin import; prove IsIso of the same r using the general criterion. All theorem signatures and coefficient maps remain unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalMateProjectionData | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.DerivedCohomologyGermIso | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.InjectiveExchangeRepresentative | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.InjectiveExchangeSourceTransport | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.InjectiveExchangeTargetTransport | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceCocycleExactRestriction | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceDerivedSectionsNaturality | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceDerivedSectionsNaturalityCore | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceLocalizedCocycleHomology | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.SourceStageSectionsNaturality | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalCohomologySourceColimit | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalComplexSectionsMate | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedExchangeGlobalSections | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedExchangeLeray | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalDerivedMateSectionsFactorization | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceComparison | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceDerivedRestriction | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceRestriction | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceSections | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceTransition | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalLocalizedHomGerm | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalMateProjectionFormulas | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalUnderivedSectionsMate | unclaimed | Unchanged: uses preserved source isomorphisms/legs or the constant comparison; no use of the retired theorem. |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreOrdinaryGerm | quarantined (separate rework) | Preserved archive, not an active library module. Canonical DAG dependency remains attached to the adopted theorem. Its existing small-model/restriction restoration is outside this packet. |
| Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula | quarantined (separate rework) | Preserved archive, not an active library module. Canonical DAG dependency remains attached to the adopted theorem. Its existing small-model/restriction restoration is outside this packet. |
| Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology | quarantined (separate rework) | Preserved archive, not an active library module. Canonical DAG dependency remains attached to the adopted theorem. Its existing small-model/restriction restoration is outside this packet. |
| Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk | quarantined (separate rework) | Preserved archive, not an active library module. Canonical DAG dependency remains attached to the adopted theorem. Its existing small-model/restriction restoration is outside this packet. |

The source-isomorphism rfl probe and the source-leg calculation both compile. The five
direct importer checks compile. The additional full StrictLocalSmallModel.StrictLocalLocalizedHomGerm
check times out both against the unchanged published baseline and the delivered overlay;
this existing limit issue is disclosed in report.md and is not counted as a passing check.

## Status

landed 20261021T061620-L-1800401 2026-10-21 (merge of deliver/P4/Sheaf.AlgebraicGeometry.StrictLocalGermRestrictionIso)
