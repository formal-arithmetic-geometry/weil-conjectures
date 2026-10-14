# moduleCohomologyExtResolutionNatIso and its site comparison interface

## Reason

The previous defining-composite proof exceeds the fixed 60-second single-file limit.
The expensive step compares inferred sheafification, Ext-size and injective-resolution
proof arguments after specializing to a scheme. A generic three-isomorphism constructor
and two named existing instance proofs share those arguments. The requested factorization
then compiles without evaluating the common-resolution comparison.

The unclaimed ModuleCohomologyExtResolutionNaturality module is adapted under the
2026-10-14 unclaimed-module rule. The site comparison's source is written as its fixed Ext
functor rather than its definitionally equal cohomology functor; the object source is the
same Ext group rather than Sheaf.H'. The redundant HasInjectiveResolutions binder is
removed: the existing Mathlib instance supplies this proposition from the same site.
The cached HasSheafify and HasExt theorems prove existing propositions by inferInstance.
They introduce no hypothesis, data witness or axiom. The explicit Ext subsingleton in
forgottenInjectiveAcyclic restates the already available Sheaf.H' vanishing at its
definitionally equal type.

The original comparison is a followed by whiskering b.symm, an identity, c and another
identity. The new constructor composes a, b.symm and c. Iso.trans_refl and Iso.refl_trans
identify these maps and inverses. The old site map likewise only loses an identity factor.
No mathematical object or map changes; no existing theorem signature is changed. In
particular ext_sections_factorization and all five Challenge targets remain unchanged.
As this changes definitions in the target import closure, the maintainer should include
this definitional-equality check in any reopened statement review under AGENTS.md section 4.

## Old

```lean
set_option backward.isDefEq.respectTransparency false in
def siteSectionsNatIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{u})]
    (U : C) (q : ℕ) :
    Sheaf.cohomologyPresheafFunctor J q ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U) ≅
      (sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q := by
  let e : (extFunctor q).obj (op ((presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free))) ≅
      (preadditiveCoyoneda.obj (op ((presheafToSheaf J AddCommGrpCat.{u}).obj
        (yoneda.obj U ⋙ AddCommGrpCat.free)))).rightDerived q :=
    NatIso.ofComponents (fun F ↦ extRightDerivedHomObjIso
      ((presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)) F q)
      (fun φ ↦ extRightDerivedHomObjIso_naturality
        ((presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)) φ q)
  exact (show Sheaf.cohomologyPresheafFunctor J q ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U) ≅
      (extFunctor q).obj (op ((presheafToSheaf J AddCommGrpCat.{u}).obj
        (yoneda.obj U ⋙ AddCommGrpCat.free))) from Iso.refl _) ≪≫ e ≪≫
          derivedSectionsIso J U q

def siteSectionsObjIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    (U : C) (F : Sheaf J AddCommGrpCat.{u}) (q : ℕ) :
    Sheaf.H' F q U ≅
      ((sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj F :=
  (siteSectionsNatIso J U q).app F

/-- The coefficient comparison as a natural isomorphism of additive functors.
Source: Stacks Project, Tags 03FD, 015E and 06XR; the same common resolution.
(blueprint: new-module-cohomology-ext-resolution-naturality) -/
@[irreducible]
noncomputable def moduleCohomologyExtResolutionNatIso (X : Scheme.{u}) (q : ℕ) :
    RingedSpace.moduleCohomology X.toRingedSpace q ⋙
      forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
        AddCommGrpCat.{u} ≅
      SheafOfModules.toSheaf (moduleRings X.toRingedSpace) ⋙
        Sheaf.functorH (Opens.grothendieckTopology X) q := by
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
  let Γ := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  let G := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let V := forget₂ (ModuleCat.{u}
    ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat.{u}
  change (G.rightDerived q ⋙ V) ≅ T ⋙ Sheaf.functorH (Opens.grothendieckTopology X) q
  exact ExtEdgeResolution.resolutionSectionsNatIso G V T Γ q
    (ExtEdgeResolution.sectionHomologyIso X q)
    (fun M _ ↦ ExtEdgeResolution.forgottenInjectiveAcyclic X M) ≪≫
      Functor.isoWhiskerLeft T
        ((ExtEdgeResolution.siteSectionsNatIso (Opens.grothendieckTopology X) ⊤ q).symm ≪≫
          ExtEdgeResolution.siteExtNatIso (Opens.grothendieckTopology X) ⊤ q ≪≫
            ExtEdgeResolution.extSourceNatIso (ExtEdgeResolution.terminalSourceIso X) q ≪≫
              ExtEdgeResolution.siteHNatIso (Opens.grothendieckTopology X) q)
```

## New

```lean
/-- Cache the sheafification proof used by the comparison on the Zariski site.
Source: Mathlib's sheafification theorem for abelian sheaves.
(blueprint: new-module-cohomology-ext-resolution-naturality) -/
@[instance 2000]
theorem comparisonHasSheafify (X : Scheme.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance

/-- Cache the Ext-size proof used by the comparison on the Zariski site.
Source: the Grothendieck abelian category instance for abelian sheaves.
(blueprint: new-module-cohomology-ext-resolution-naturality) -/
@[instance 2000]
theorem comparisonHasExt (X : Scheme.{u}) :
    HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance

/-- Compose section comparisons before specializing the functors and the Ext source change.
Source: Stacks Project, Tags 03FD and 06XR; the three constructed comparison maps.
(blueprint: new-module-cohomology-ext-resolution-naturality) -/
noncomputable def sectionsComparisonNatIso
    {A E : Type*} [Category A] [Category E]
    {R : Type u} [Ring R] {K : A ⥤ ModuleCat.{u} R} {T : A ⥤ E}
    {B L Q : E ⥤ AddCommGrpCat.{u}}
    (a : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ T ⋙ B)
    (b : L ≅ B) (c : L ≅ Q) : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ T ⋙ Q :=
  a ≪≫ Functor.isoWhiskerLeft T (b.symm ≪≫ c)

set_option backward.isDefEq.respectTransparency false in
def siteSectionsNatIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    (U : C) (q : ℕ) :
    (extFunctor q).obj (op ((presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free))) ≅
      (sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q := by
  let e : (extFunctor q).obj (op ((presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free))) ≅
      (preadditiveCoyoneda.obj (op ((presheafToSheaf J AddCommGrpCat.{u}).obj
        (yoneda.obj U ⋙ AddCommGrpCat.free)))).rightDerived q :=
    NatIso.ofComponents (fun F ↦ extRightDerivedHomObjIso
      ((presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)) F q)
      (fun φ ↦ extRightDerivedHomObjIso_naturality
        ((presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)) φ q)
  exact e ≪≫ derivedSectionsIso J U q

def siteSectionsObjIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    (U : C) (F : Sheaf J AddCommGrpCat.{u}) (q : ℕ) :
    AddCommGrpCat.of (Ext ((presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free)) F q) ≅
      ((sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q).obj F :=
  (siteSectionsNatIso J U q).app F

/-- The coefficient comparison as a natural isomorphism of additive functors.
Source: Stacks Project, Tags 03FD, 015E and 06XR; the same common resolution.
(blueprint: new-module-cohomology-ext-resolution-naturality) -/
@[irreducible]
noncomputable def moduleCohomologyExtResolutionNatIso (X : Scheme.{u}) (q : ℕ) :
    RingedSpace.moduleCohomology X.toRingedSpace q ⋙
      forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
        AddCommGrpCat.{u} ≅
      SheafOfModules.toSheaf (moduleRings X.toRingedSpace) ⋙
        Sheaf.functorH (Opens.grothendieckTopology X) q := by
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
  let Γ := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  let G := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let V := forget₂ (ModuleCat.{u}
    ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat.{u}
  change (G.rightDerived q ⋙ V) ≅ T ⋙ Sheaf.functorH (Opens.grothendieckTopology X) q
  exact ExtEdgeResolution.sectionsComparisonNatIso
    (ExtEdgeResolution.resolutionSectionsNatIso G V T Γ q
      (ExtEdgeResolution.sectionHomologyIso X q)
      (fun M _ ↦ ExtEdgeResolution.forgottenInjectiveAcyclic X M))
    (ExtEdgeResolution.siteSectionsNatIso (Opens.grothendieckTopology X) ⊤ q)
    (ExtEdgeResolution.extSourceNatIso (ExtEdgeResolution.terminalSourceIso X) q)
```

The requested module also adds a proved private generic component-evaluation lemma and
uses it in the unchanged public theorem. A declaration-scoped 800000-heartbeat allowance
permits its instance conversions; the 60-second deadline is unchanged. No import changes.

## Users

The table is the union of source uses reported by tools/downstream.py for siteSectionsNatIso,
siteSectionsObjIso, moduleCohomologyExtResolutionNatIso and moduleCohomologyExtResolutionEquiv,
and direct importers of the changed module. No module held by another group is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AbelianCounitCocycleCalculation | G4 | Unchanged source; comparison signatures or definitionally equal site domains remain usable. |
| Sheaf.AlgebraicGeometry.AbelianCounitResolutionCalculation | unclaimed | Unchanged source; comparison signatures or definitionally equal site domains remain usable. |
| Sheaf.AlgebraicGeometry.AbelianResolutionComparisonEvaluation | G4 | Unchanged source; comparison signatures or definitionally equal site domains remain usable. |
| Sheaf.AlgebraicGeometry.ModuleCohomologyExtEdgeComparison | unclaimed | Unchanged source; comparison signatures or definitionally equal site domains remain usable. |
| Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionEdge | unclaimed | Unchanged source; comparison signatures or definitionally equal site domains remain usable. |
| Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality | unclaimed | Definition refactor in this delivery; mathematical maps unchanged. |
| Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization | unclaimed | Unchanged source; comparison signatures or definitionally equal site domains remain usable. |
| Sheaf.AlgebraicGeometry.ModuleCohomologyExtSectionsFactorization | N1 | Requested proof; signature unchanged. |
| Sheaf.AlgebraicGeometry.ModuleCohomologyExtStandardResolutionFormula | unclaimed | Unchanged source; comparison signatures or definitionally equal site domains remain usable. |
| Sheaf.AlgebraicGeometry.ModuleCohomologyStandardSectionsFactorization | unclaimed | Unchanged source; comparison signatures or definitionally equal site domains remain usable. |

The two delivery modules and unchanged consumers are checked individually against the
sandbox artifacts. The maintainer's global build checks the transitive import closure.

## Status

landed 20261014T201710-L-2040671 2026-10-14 (merge of deliver/N1/Sheaf.AlgebraicGeometry.ModuleCohomologyExtSectionsFactorization)
