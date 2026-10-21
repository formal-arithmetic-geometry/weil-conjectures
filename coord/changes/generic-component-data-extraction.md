# AlgebraicGeometry.Scheme.ProEt.genericComponentFunctor and companion data

## Reason

The restored theorem needs separate geometric and ordinary-coefficient results whose
statements refer to its canonical component data. Extract the six existing declarations
into GenericComponentData to make those statements available without an import cycle.
The main module publicly reexports the data module and retains all the previous public
imports, directly or through this reexport. The definitions, bodies, attributes and
names are unchanged. The theorem signature is also unchanged.

## Old

The following verbatim declarations occurred in
`Sheaf.AlgebraicGeometry.GenericFiberComponentsSection`:

```lean
noncomputable def genericComponentFunctor (T : Scheme.{u}) [IsAffine T] :
    Over (componentProfinite T) ⥤ T.ProEt :=
  (affine_component_site_projection T).choose

/-- Coordinates of the canonical component functor, retained from its geometric
characterization. Source: Bhatt--Scholze Lemma 2.2.8
(blueprint: lem-zl-generic-fiber-components-section). -/
noncomputable def genericComponentCoordinates (T : Scheme.{u}) [IsAffine T] :
    ∀ E : Over (componentProfinite T),
      C(((genericComponentFunctor T).obj E).left, E.left) :=
  (affine_component_site_projection T).choose_spec.choose

/-- Continuity of the chosen, geometrically characterized component functor.
Source: Bhatt--Scholze Lemma 4.2.13(1)
(blueprint: lem-zl-generic-fiber-components-section). -/
noncomputable instance genericComponentContinuous (T : Scheme.{u}) [IsAffine T] :
    (genericComponentFunctor T).IsContinuous
      ((coherentTopology Profinite.{u}).over (componentProfinite T)) (topology T) :=
  ((affine_component_site_projection T).choose_spec.choose_spec.the project server).choose

/-- The canonical component morphism on sets, extracted from the evaluation of the
same functor. Its direct image is restriction along `genericComponentFunctor T`.
Source: Bhatt--Scholze Lemma 4.2.13(1)
(blueprint: lem-zl-generic-fiber-components-section). -/
noncomputable def genericComponentProjection (T : Scheme.{u}) [IsAffine T] :
    GeometricMorphism (Sheaf (topology T) (Type (u + 1)))
      (Sheaf ((coherentTopology Profinite.{u}).over (componentProfinite T))
        (Type (u + 1))) :=
  ((affine_component_site_projection T).choose_spec.choose_spec.the project server).choose_spec.1.choose

/-- The ring-valued inverse image induced by the very same component functor.
Its right adjoint is restriction along that functor, so its operations and
adjunction unit are those of the canonical algebraic lift.
Source: Bhatt--Scholze Lemma 4.2.13(1) and HRS Theorem 4.13, diagram (4.4)
(blueprint: lem-zl-generic-fiber-components-section). -/
noncomputable abbrev genericComponentRingPush (T : Scheme.{u}) [IsAffine T] :=
  (genericComponentFunctor T).sheafPushforwardContinuous RingCat.{u + 1}
    ((coherentTopology Profinite.{u}).over (componentProfinite T)) (topology T)

/-- The scalar-extension compatibility, characterized without any choice of a resolution.
For a ring map from a discrete ring to global coefficients, extension of constants is
left adjoint to global sections with that scalar action. Its unbounded left derived
functor is characterized by the displayed localization counit. The assertion says that
these actual scalar extensions commute with the specified component-derived equivalence.
Source: HRS Theorem 4.13, proof after (4.4)
(blueprint: lem-zl-generic-fiber-components-section). -/
def GenericComponentScalarCompatibility
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J RingCat.{u + 1}) (B : Sheaf K RingCat.{u + 1})
    (c : C) (d : D) (e : A.obj.obj (op c) ≅ B.obj.obj (op d))
    [HasDerivedCategory.{wS} (ringedSiteModules.{u + 1} A)]
    [HasDerivedCategory.{wV} (ringedSiteModules.{u + 1} B)]
    (E : DerivedCategory (ringedSiteModules.{u + 1} A) ≌
      DerivedCategory (ringedSiteModules.{u + 1} B)) : Prop :=
  (∀ (R : Type (u + 1)) [Ring R]
    [HasDerivedCategory.{wR} (ModuleCat.{u + 1} R)]
    (a : R →+* A.obj.obj (op c))
    (FS : ModuleCat.{u + 1} R ⥤ ringedSiteModules.{u + 1} A)
    (FV : ModuleCat.{u + 1} R ⥤ ringedSiteModules.{u + 1} B)
    [FS.Additive] [FV.Additive],
    Nonempty (FS ⊣ SheafOfModules.evaluation A (op c) ⋙ ModuleCat.restrictScalars a) →
    Nonempty (FV ⊣ SheafOfModules.evaluation B (op d) ⋙
      ModuleCat.restrictScalars (e.hom.hom.comp a)) →
    ∀ (LS : DerivedCategory (ModuleCat.{u + 1} R) ⥤
        DerivedCategory (ringedSiteModules.{u + 1} A))
      (LV : DerivedCategory (ModuleCat.{u + 1} R) ⥤
        DerivedCategory (ringedSiteModules.{u + 1} B))
      (εS : DerivedCategory.Qh ⋙ LS ⟶
        FS.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (εV : DerivedCategory.Qh ⋙ LV ⟶
        FV.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
      LS.IsLeftDerivedFunctor εS
        (HomotopyCategory.quasiIso (ModuleCat.{u + 1} R) (ComplexShape.up ℤ)) →
      LV.IsLeftDerivedFunctor εV
        (HomotopyCategory.quasiIso (ModuleCat.{u + 1} R) (ComplexShape.up ℤ)) →
      Nonempty (LS ⋙ E.functor ≅ LV)) ∧
  (∀ (R : Type (u + 1)) [CommRing R]
    [HasDerivedCategory.{wR} (ModuleCat.{u + 1} R)]
    [HasDerivedCategory.{wCJ} (realizationModules J R)]
    [HasDerivedCategory.{wCK} (realizationModules K R)]
    (aS : (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (realizationRing J R) ⟶ A)
    (aV : (sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (realizationRing K R) ⟶ B),
    (∀ r : R,
      e.hom.hom ((aS.hom.app (op c)).hom ((realizationRingUnit J R).app (op c) r)) =
        (aV.hom.app (op d)).hom ((realizationRingUnit K R).app (op d) r)) →
    ∀ (FS : realizationModules J R ⥤ ringedSiteModules.{u + 1} A)
      (FV : realizationModules K R ⥤ ringedSiteModules.{u + 1} B)
      [FS.Additive] [FV.Additive],
    Nonempty (FS ⊣ SheafOfModules.restrictScalars aS) →
    Nonempty (FV ⊣ SheafOfModules.restrictScalars aV) →
    ∀ (LS : DerivedCategory (realizationModules J R) ⥤
        DerivedCategory (ringedSiteModules.{u + 1} A))
      (LV : DerivedCategory (realizationModules K R) ⥤
        DerivedCategory (ringedSiteModules.{u + 1} B))
      (εS : DerivedCategory.Qh ⋙ LS ⟶
        FS.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (εV : DerivedCategory.Qh ⋙ LV ⟶
        FV.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
    LS.IsLeftDerivedFunctor εS
      (HomotopyCategory.quasiIso (realizationModules J R) (ComplexShape.up ℤ)) →
    LV.IsLeftDerivedFunctor εV
      (HomotopyCategory.quasiIso (realizationModules K R) (ComplexShape.up ℤ)) →
    Nonempty (commutativeSiteDerivedConstantModuleFunctor J R ⋙ LS ⋙ E.functor ≅
      commutativeSiteDerivedConstantModuleFunctor K R ⋙ LV))
```

## New

Exactly the declarations above, with the same signatures and bodies, occur in
`Sheaf.AlgebraicGeometry.GenericComponentData`. Only their blueprint comments now
identify `def-zl-generic-component-data`. The original module has:

```lean
public import Sheaf.AlgebraicGeometry.GenericComponentData
```

Reviewer correction (2026-10-21): the two new predicates
`GenericComponentConstantScalarCompatibility` and `GenericComponentOrdinaryScalarCompatibility`
are also defined in `Sheaf.AlgebraicGeometry.GenericComponentData` (node
`def-zl-generic-component-data`), not in the theorem module
`Sheaf.AlgebraicGeometry.GenericComponentScalarTransport`. They are new declarations, not
part of the verbatim extraction. The statement of `generic_component_coefficient_comparison`
uses the first, so its module now publicly imports the data module instead of the transport
module. The item imports the transport module directly, as a plain import.

No definition has been replaced by a witness of a new existence theorem. The component
functor still comes from the same geometrically characterized existing construction.
All new records are actual structures; no definition body contains a hole.

## Users

The item was initially read from its rework archive. During this session the shared
checkout restored the same source verbatim (checked by `diff`). A fresh
`tools/downstream.py` scan lists two downstream modules, below. None mentions any
of the six extracted names: their only occurrences in that scan are in the item.
The downstream imports and the original theorem interface are preserved. The
quarantine archive is retained.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GenericFiberComponentsSection | V1 | Public reexport preserves all six names; original theorem statement is verbatim. |
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | unclaimed | Its import of the item and theorem interface are preserved; no adaptation. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed | The transitive public interface is preserved; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericComponentSiteComparison | new, V1 | Uses the extracted canonical projection in its statement. |
| Sheaf.AlgebraicGeometry.GenericComponentCoefficientComparison | new, V1 | Uses the extracted functor and projection in its data fields. |
| Sheaf.AlgebraicGeometry.GenericComponentScalarTransport | new, V1 | Uses the unchanged scalar-compatibility predicate. |

Both original downstream files were compiled unchanged against the extracted public
interface through `lcompile.py --all`: they passed in 5.2 and 5.1 seconds respectively.
Their unchanged verification copies are excluded from the packet.

The targets and every mathematical definition they use are unchanged; this extraction
requires no semantic target change. The independent reader should check the verbatim
extraction and public reexport.

## Status

landed 20261021T061721-L-1819126 2026-10-21 (merge of deliver/V1/Sheaf.AlgebraicGeometry.GenericFiberComponentsSection)
