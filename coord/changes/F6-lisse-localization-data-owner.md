# WeilConjectures.LisseLocalization localization data

## Reason

The proper substeps of exists_lisseLocalizationRestriction need its data types without
importing the theorem that combines them. Move the existing declarations, with the
same names, universes, signatures and bodies, to Sheaf.Paper.LisseLocalizationData and
publicly re-export them from the original module. This is a definition-owner extraction,
not a mathematical change. The original public prerequisites remain available through
the new data owner's public imports. No target signature changes.

The first compile of the extracted declarations exceeded 60 seconds. Profiling completed
modelTensorSection and stalled at the following SliceLocalization structure. Disabling
generated injectivity, size-of and constructor-index auxiliaries made this definition
owner compile in 47.2 seconds, without changing any of its mathematical declarations.
No compiled file is split as a response to this timeout.

## Old

Owner: Sheaf.Paper.LisseLocalizationRestriction. The exact declarations were:

```lean
/-- The recorded completed integral ring, on every scheme, including non-finite-type charts.
Source: BS 6.8.2(1) (blueprint: lem-tw-lisse-localization-restriction). -/
abbrev integralRing (X : Scheme.{u}) := completedIntegralCommRingSheafUnrestricted l E X

/-- The constant coefficient ring map into compatible completed sections.
Source: BS 6.8.2(1), 6.8.14(2) (blueprint: lem-tw-lisse-localization-restriction). -/
def scalarMap (X : Scheme.{u}) : Padic.coefficientExtensionIntegers l E →+*
    RingCat.sectionsSubring ((integralRing l E X).obj ⋙ forget₂ CommRingCat RingCat) :=
  (RingHom.pi (fun U ↦ ((integralConstantToCompletionOfUniverses l E X).hom.app U).hom.comp
    ((((toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))))).app U).hom).comp
        (ULift.ringEquiv.symm.toRingHom)))).codRestrict _
    (fun a ↦ (completedScalarSection l E X a).property)

/-- The actual sheafification of sectionwise localization at the constant uniformizer.
Source: BS 6.8.2(2) (blueprint: lem-tw-lisse-localization-restriction). -/
abbrev rationalRing (X : Scheme.{u}) :=
  ringedLocalizationRingOfUniverses.{u + 1, u + 1, u} (integralRing l E X)
    (completedScalarSection l E X
      (Padic.coefficientExtensionUniformizer l E))

/-- Its canonical localization unit.
Source: BS 6.8.2(2) (blueprint: lem-tw-lisse-localization-restriction). -/
abbrev localizationUnit (X : Scheme.{u}) :=
  ringedLocalizationRingUnitOfUniverses.{u + 1, u + 1, u} (integralRing l E X)
    (completedScalarSection l E X
      (Padic.coefficientExtensionUniformizer l E))

/-- Ordinary module sheaves, using the recorded module category.
Source: BS 6.8.8 (blueprint: lem-tw-lisse-localization-restriction). -/
abbrev Modules (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  ringedSiteModules.{u + 1} (X.adicLisseForget.obj R)

/-- A universal cochain presentation of the specified derived scalar extension.
The ordinary functor and the K-flat counit are part of its specification.
Source: Stacks 06YY (blueprint: lem-tw-lisse-localization-restriction). -/
abbrev Model (X : Scheme.{u}) :=
  SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2}
    (localizationUnit l E X)

/-- The localized field acts through the inverse of its fraction-normalized coefficient
isomorphism and the constant-section map. This fixes the scalar action on derived Homs.
Source: BS 6.8.14(2) (blueprint: lem-tw-lisse-localization-restriction). -/
@[instance_reducible]
instance rationalLinear (X : Scheme.{u}) :
    Linear E (DerivedCategory (Modules X (rationalRing l E X))) :=
  derivedLinear.{u + 1, u, u + 1, u, u + 2} E (rationalRing l E X)
    ((coefficientMap.{u + 1, u, u + 1, u}
      (Padic.coefficientExtensionIntegers l E) (integralRing l E X) (scalarMap l E X)
      (Padic.coefficientExtensionUniformizer l E)).comp
        (sfRationalCoefficientEquiv l E).symm.toRingHom)

/-- Restriction of modules through the specified ring identification and slice equivalence.
The data are sectionwise restriction with the transported scalar action.
Source: Stacks 04IX (blueprint: lem-tw-lisse-localization-restriction). -/
def moduleRestriction {X : Scheme.{u}} (U : X.ProEt)
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology U.left) CommRingCat.{u + 1}}
    (e : (coefficientRestriction.{u, u} U).obj R ≅ S) :
    Modules X R ⥤ Modules U.left S :=
  letI : (ProEt.sliceFrom X U).IsDenseSubsite (ProEt.topology U.left)
      ((ProEt.topology X).over U) := ProEt.sliceDense X U
  SheafOfModules.overFunctor _ U ⋙
    SheafOfModules.pushforward.{u + 1} (F := ProEt.sliceFrom X U)
      (J := ProEt.topology U.left) (K := (ProEt.topology X).over U)
      (R := (X.adicLisseForget.obj R).over U)
      (S := U.left.adicLisseForget.obj S)
      ⟨Functor.whiskerRight e.inv.hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- The ordinary and derived localization, with its actual raw rational descent.
Source: BS 6.8.14(2), Stacks 015F and 010N
(blueprint: lem-tw-lisse-localization-restriction). -/
structure LocalizationData (X : Scheme.{u}) where
  model : Model l E X
  finiteLimits : PreservesFiniteLimits model.E
  finiteColimits : PreservesFiniteColimits model.E
  comparison : letI := finiteLimits; letI := finiteColimits
    model.T ≅ model.E.mapDerivedCategory
  normalization : letI := finiteLimits; letI := finiteColimits
    ∀ K : CochainComplex (Modules X (integralRing l E X)) ℤ,
      comparison.hom.app (DerivedCategory.Q.obj K) ≫
        model.E.mapDerivedCategoryFactors.hom.app K = model.ε.app K
  homology : ∀ i : ℤ,
    model.T ⋙ DerivedCategory.homologyFunctor (Modules X (rationalRing l E X)) i ≅
      DerivedCategory.homologyFunctor (Modules X (integralRing l E X)) i ⋙ model.E
  realization : sfRationalConstructibleCategory l E X ⥤
    DerivedCategory (Modules X (rationalRing l E X))
  additive : realization.Additive
  object_eq : ∀ K, realization.obj K = model.T.obj K.obj.obj
  map_tensor : ∀ (K L : sfIntegralConstructibleCategory l E X) (f : K ⟶ L)
      (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
    realization.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f) =
      eqToHom (object_eq ⟨K⟩) ≫
        (sfRationalCoefficientEquiv l E a • model.T.map f.hom) ≫
          eqToHom (object_eq ⟨L⟩).symm
  halves : ∀ (b : Bool) (n : ℤ) (K : sfRationalConstructibleCategory l E X),
    sfRationalStandardClass l E X b n K →
      ∀ i : ℤ, (if b then n < i else i < n) →
        IsZero ((DerivedCategory.homologyFunctor (Modules X (rationalRing l E X)) i).obj
          (realization.obj K))

/-- The sheafified image of an actual section fraction `b/t^n`.
Source: BS 6.8.2(2) (blueprint: lem-tw-lisse-localization-restriction). -/
def fractionSection (X : Scheme.{u}) (V : X.ProEtᵒᵖ)
    (b : (integralRing l E X).obj.obj V) (n : ℕ) :
    (rationalRing l E X).obj.obj V :=
  ((toSheafify (ProEt.topology X)
    (ringedLocalizationRingPresheafOfUniverses.{u + 1, u + 1, u}
      (integralRing l E X) (completedScalarSection l E X
        (Padic.coefficientExtensionUniformizer l E)))).app V).hom
          (Localization.mk b (Submonoid.pow _ n))

/-- The coefficient comparisons on an arbitrary pro-etale chart. Their projection,
constant-section, unit and fraction equations fix the intended identifications.
Source: BS 6.8.2; Stacks 04IX
(blueprint: lem-tw-lisse-localization-restriction). -/
structure SliceCoefficients {X : Scheme.{u}} (U : X.ProEt) where
  integral : (coefficientRestriction.{u, u} U).obj (integralRing l E X) ≅
    integralRing l E U.left
  rational : (coefficientRestriction.{u, u} U).obj (rationalRing l E X) ≅
    rationalRing l E U.left
  residue : ∀ n : ℕ, (coefficientRestriction.{u, u} U).obj
    (integralCoefficientCommRingSheaf l E X n) ≅ integralCoefficientCommRingSheaf l E U.left n
  projections : ∀ n : ℕ,
    integral.hom ≫ completedIntegralCommRingProjectionUnrestricted l E U.left n =
      (coefficientRestriction.{u, u} U).map
        (completedIntegralCommRingProjectionUnrestricted l E X n) ≫ (residue n).hom
  constants : ∀ (n : ℕ) (V : U.left.ProEt),
    (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app
        (op ((MorphismProperty.Over.map ⊤ U.prop).obj V)) ≫
          (residue n).hom.hom.app (op V) =
      (toSheafify (ProEt.topology U.left) ((Functor.const U.left.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E (n + 1)))))).app (op V)
  unit : (coefficientRestriction.{u, u} U).map (localizationUnit l E X) ≫ rational.hom =
    integral.hom ≫ localizationUnit l E U.left
  fractions : ∀ (V : U.left.ProEt)
      (b : (integralRing l E X).obj.obj
        (op ((MorphismProperty.Over.map ⊤ U.prop).obj V))) (n : ℕ),
    (rational.hom.hom.app (op V))
      (fractionSection l E X (op ((MorphismProperty.Over.map ⊤ U.prop).obj V)) b n) =
        fractionSection l E U.left (op V) ((integral.hom.hom.app (op V)) b) n

/-- Natural tensor restriction with its pure-tensor normalization.
Source: Stacks 03EL and 03DH (blueprint: lem-tw-lisse-localization-restriction). -/
def SliceTensorCompatibility {X : Scheme.{u}} (A : Sheaf (ProEt.topology X)
    CommRingCat.{u + 1}) (U : X.ProEt) : Prop :=
    ∃ e : ∀ F G : Modules X A,
        ((siteSheafTensorRight G).obj F).over U ≅
          (siteSheafTensorRight (A := A.over U) (G.over U)).obj (F.over U),
      (∀ (F F' G G' : Modules X A)
          (f : F ⟶ F') (g : G ⟶ G'),
        (((siteSheafTensorRight G).map f ≫ siteSheafTensorSecondMap F' g).over U) ≫
            (e F' G').hom =
          (e F G).hom ≫
            (siteSheafTensorRight (A := A.over U) (G.over U)).map (f.over U) ≫
              siteSheafTensorSecondMap (A := A.over U) (F'.over U) (g.over U)) ∧
      (∀ (F G : Modules X A)
          (V : Over U) (x : F.val.obj (op V.left)) (y : G.val.obj (op V.left)),
        ((e F G).hom.val.app (op V)) (siteSheafTensorTmul F G (op V.left) x y) =
          siteSheafTensorTmul (A := A.over U) (F.over U) (G.over U) (op V) x y)

/-- A sheafified pure tensor in the specified ordinary extension.
Source: Stacks 03EK (blueprint: lem-tw-lisse-localization-restriction). -/
def modelTensorSection {X : Scheme.{u}} (d : Model l E X)
    (M : Modules X (integralRing l E X)) (V : X.ProEtᵒᵖ)
    (a : (rationalRing l E X).obj.obj V) (x : M.val.obj V) :
    (d.E.obj M).val.obj V :=
  (eqToHom (d.obj_eq M).symm).val.app V
    ((toSheafify (ProEt.topology X)
      (SheafOfModules.changeOfRingsPresheaf (localizationUnit l E X) M).presheaf).app V
        (a ⊗ₜ[(integralRing l E X).obj.obj V,
          ((localizationUnit l E X).hom.app V).hom] x))

/-- Exact termwise module restriction and the natural derived scalar-extension comparison.
No finiteness condition is imposed on the chart.
Source: Stacks 03EL, 04IX and 015F
(blueprint: lem-tw-lisse-localization-restriction). -/
structure SliceLocalization {X : Scheme.{u}} (dx : LocalizationData l E X)
    (U : X.ProEt) (du : LocalizationData l E U.left) (c : SliceCoefficients l E U) where
  integralAdditive : (moduleRestriction U c.integral).Additive
  integralLimits : PreservesFiniteLimits (moduleRestriction U c.integral)
  integralColimits : PreservesFiniteColimits (moduleRestriction U c.integral)
  rationalAdditive : (moduleRestriction U c.rational).Additive
  rationalLimits : PreservesFiniteLimits (moduleRestriction U c.rational)
  rationalColimits : PreservesFiniteColimits (moduleRestriction U c.rational)
  ordinaryComparison :
    dx.model.E ⋙ moduleRestriction U c.rational ≅
      moduleRestriction U c.integral ⋙ du.model.E
  tensors : ∀ (M : Modules X (integralRing l E X)) (V : U.left.ProEt)
      (a : (rationalRing l E X).obj.obj
        (op ((MorphismProperty.Over.map ⊤ U.prop).obj V)))
      (x : M.val.obj (op ((MorphismProperty.Over.map ⊤ U.prop).obj V))),
    (ordinaryComparison.hom.app M).val.app (op V)
      (modelTensorSection l E dx.model M
        (op ((MorphismProperty.Over.map ⊤ U.prop).obj V)) a x) =
      modelTensorSection l E du.model ((moduleRestriction U c.integral).obj M)
        (op V) ((c.rational.hom.hom.app (op V)) a) x
  comparison : letI := integralAdditive; letI := integralLimits; letI := integralColimits
    letI := rationalAdditive; letI := rationalLimits; letI := rationalColimits
    dx.model.T ⋙ (moduleRestriction U c.rational).mapDerivedCategory ≅
      (moduleRestriction U c.integral).mapDerivedCategory ⋙ du.model.T
  normalization : letI := integralAdditive; letI := integralLimits; letI := integralColimits
    letI := rationalAdditive; letI := rationalLimits; letI := rationalColimits
    ∀ K : CochainComplex (Modules X (integralRing l E X)) ℤ,
      (moduleRestriction U c.rational).mapDerivedCategory.map (dx.model.ε.app K) ≫
        (moduleRestriction U c.rational).mapDerivedCategoryFactors.hom.app
          ((dx.model.E.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex ordinaryComparison.hom (.up ℤ)).app K) =
      comparison.hom.app (DerivedCategory.Q.obj K) ≫
        du.model.T.map ((moduleRestriction U c.integral).mapDerivedCategoryFactors.hom.app K) ≫
          du.model.ε.app (((moduleRestriction U c.integral).mapHomologicalComplex (.up ℤ)).obj K)
```

## New

Owner: Sheaf.Paper.LisseLocalizationData, re-exported by the original module.
The declarations above retain their signatures and bodies verbatim. The new data owner
sets genInjectivity, genSizeOf and genCtorIdx to false, avoiding unused generated
auxiliaries of the large dependent structures. No existing consumer mentions those
auxiliaries. The actual localization assertion has the exact original statement,
now with a complete assembly proof from three proper steps.

## Users

A source search and tools/downstream.py found no existing downstream module importing
Sheaf.Paper.LisseLocalizationRestriction and no external use of its LocalizationData.
The existing DAG parent remains served by the same public theorem and re-exported data.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LisseLocalizationRestriction | F6 | Publicly imports the definition owner; unchanged theorem signature and data visibility. |
| Sheaf.Paper.LisseLocalizationData | new, F6 | Owns the same declarations; no mathematical changes. |
| Sheaf.Paper.LisseLocalizationExistence | new, F6 | States the exact-localization substep using the data owner. |
| Sheaf.Paper.LisseLocalizationSlices | new, F6 | States the single-chart normalized-comparison substep. |
| Sheaf.Paper.LisseLocalizationLocalFreeness | new, F6 | States the local-freeness and unit substep with the comparison data as inputs. |

## Status

landed 20261025T122910-L-1816599 2026-10-25 (merge of deliver/F6/Sheaf.Paper.LisseLocalizationRestriction)
