# AlgebraicGeometry.Scheme.Modules.moduleCohomologyExtResolutionEquiv

## Reason

The original definition elaborates the equality of the two section complexes only
once a large chosen resolution has been substituted. Unfolding it in the coefficient
square exceeded the file limit. Construct the common-resolution square generically,
then specialize its natural isomorphism and convert its component to an additive
equivalence. The generic exact-forgetting and section-homology identifications
avoid repeated expansion of the scheme-specific functors. Marking the comparison
irreducible controls elaboration; its proof unfolds it explicitly.

This preserves the original function and inverse: resolutionSectionsObjIso uses
exactly the original chosen injective resolution, augmentation and acyclic comparison;
sectionHomologyIso is Iso.refl. siteSectionsNatIso is the already constructed
Hom-complex/section comparison, with the original siteSectionsObjIso as component.
siteExtNatIso and siteHNatIso are Iso.refl. Finally extSourceNatIso uses the original precompAddEquiv.symm directly
in each component. Its naturality is Ext.comp_assoc_of_third_deg_zero, applied to the
source inverse, coefficient class and degree-zero coefficient morphism. These
are exactly the component maps of extFunctor.map of the inverse source. Reassociation of the composites does not change
these maps. There is no arbitrary natural equivalence or existential witness.

All existing declaration signatures and visibility stay byte-for-byte unchanged.
The target statements stay unchanged. Definitions used by the targets are explicitly
reviewed here for preservation of their meaning; this record remains open for the
required definition review on landing.

AcyclicComparisonNatural is a plain proof-only import. The existing public
Ext.Basic import remains necessary: extSourceNatIso uses precompAddEquiv
in its component data. No downstream import or other adaptation is needed.

## Old

```lean
def moduleCohomologyExtResolutionEquiv (X : Scheme.{u}) (F : X.Modules) (q : ℕ) :
    ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) ≃+ H F q := by
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
  let Γ := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  let G := RingedSpace.globalSectionsFunctor X.toRingedSpace
  have : G.Additive := inferInstanceAs
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive
  let V := forget₂ (ModuleCat.{u}
    ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat.{u}
  let I := injectiveResolution
    (show SheafOfModules.{u} (moduleRings X.toRingedSpace) from F)
  let ι := (HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℕ) 0).inv.app F ≫
    (T.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
  have : QuasiIso ι := by
    dsimp only [ι]
    have : QuasiIso ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι) :=
      inferInstance
    exact quasiIso_comp _ _
  let c := Γ.rightDerivedObjIsoOfResolution ι
    (fun n ↦ ExtEdgeResolution.forgottenInjectiveAcyclic X (I.cocomplex.X n)) q
  let a : V.obj ((G.rightDerived q).obj F) ≅
      ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((T.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)).homology q :=
    V.mapIso (I.isoRightDerivedObj G q) ≪≫
      ((((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc q).mapHomologyIso
        V).symm
  let d := ExtEdgeResolution.siteSectionsObjIso (Opens.grothendieckTopology X) ⊤ (T.obj F) q
  let t := (Abelian.Ext.precompAddEquiv (ExtEdgeResolution.terminalSourceIso X) (T.obj F) q).symm
  exact ((a ≪≫ c.symm ≪≫ d.symm).addCommGroupIsoToAddEquiv).trans t

set_option backward.isDefEq.respectTransparency false in
```

## New

```lean
@[irreducible]
def moduleCohomologyExtResolutionEquiv (X : Scheme.{u}) (F : X.Modules) (q : ℕ) :
    ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F) ≃+ H F q :=
  ExtEdgeResolution.moduleComparisonEquiv (moduleCohomologyExtResolutionNatIso X q) F
```

The concrete moduleCohomologyExtResolutionNatIso composes
resolutionSectionsNatIso, the inverse siteSectionsNatIso, the two identity
identifications, and extSourceNatIso of the terminal-source isomorphism.
Its resolutionSectionsNatIso naturality field is proved from injective-resolution
lift naturality, mapHomologyIso naturality and acyclicComparison_naturality.
No new theorem hole is introduced.

## Users

The downstream named-use scan has the following four modules. Indirect users
retain the same coefficient and edge comparisons because both component maps
are preserved. No Challenge.lean statement is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality | F2 | Same concrete maps; the original coefficient naturality hole is closed. |
| Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization | D2 | Same normalization and signatures; no edit or adaptation needed. |
| Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionEdge | unclaimed in local claims | Same comparison and statement; no edit. The normalization import still reexports Ext.Basic. |
| Sheaf.AlgebraicGeometry.ModuleCohomologyExtEdgeComparison | unclaimed in local claims | Same equivalences and applications; no edit. |

## Status

landed 20261013T224508-L-1470559 2026-10-13 (merge of deliver/F2/Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality)
