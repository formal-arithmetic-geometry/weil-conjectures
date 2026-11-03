/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedSectionsCupWeilTransport.AdmissibleToLocalizingCoefficient
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntrinsicFiniteTorMixedSupportCup
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedGeometricFrobeniusTransport
public import WeilConjectures.SixFunctors.FrobeniusSquareExchange.FrobeniusSquareExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExactScalarPointCup
public import WeilConjectures.ZetaWeil.FrobeniusPointTransportDirect
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

/-! Shared native vocabulary and laws for the condensed sections transport argument.

Source: the cup/sections sub-step of `sk-thm-frobenius` in blueprint latest.
(blueprint: def-pod-condensed-sections-transport-laws). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedSectionsCupWeilTransport

/-! # Condensed sections, cup products, and Weil transport

This module states the canonical mixed-support cup, projection, point-evaluation, and
degreewise cohomology transport package from the Frobenius unit.  Every postponed fact is
kept as a theorem statement; all displayed constructions use the published native maps.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-frobenius/
sec-purity-duality-and-frobenius/sk-thm-frobenius/_section.md
(blueprint: `def-pod-condensed-sections-transport-laws`).
-/

attribute [local instance] AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj
attribute [local instance 30000] CategoryTheory.Functor.monObjObj
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian

/-- Finite type over the geometric point is preserved by base change.
Source: the cup/sections sub-step of `sk-thm-frobenius` in the nested Frobenius section.
(blueprint: def-pod-condensed-sections-transport-laws). -/
instance geometricFiberLocallyOfFiniteType
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :
    LocallyOfFiniteType (D.geometricFiber T₀).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd T₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Quasi-compactness over the geometric point is preserved by base change.
Source: the cup/sections sub-step of `sk-thm-frobenius` in the nested Frobenius section.
(blueprint: def-pod-condensed-sections-transport-laws). -/
instance geometricFiberQuasiCompact
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :
    QuasiCompact (D.geometricFiber T₀).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd T₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Separatedness over the geometric point is preserved by base change.
Source: the cup/sections sub-step of `sk-thm-frobenius` in the nested Frobenius section.
(blueprint: def-pod-condensed-sections-transport-laws). -/
instance geometricFiberSeparated
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom] :
    IsSeparated (D.geometricFiber T₀).hom :=
  inferInstanceAs (IsSeparated (pullback.snd T₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- The strict Frobenius intertwining equation for an arrow.
Source: the cup/sections sub-step of `sk-thm-frobenius` in the nested Frobenius section.
(blueprint: def-pod-condensed-sections-transport-laws). -/
def IsIntertwining {C : Type u} [Category C]
    (P : C ⥤ C) {X Y : C} (u : X ⟶ Y)
    (φX : P.obj X ≅ X) (φY : P.obj Y ≅ Y) : Prop :=
  φX.hom ≫ u = P.map u ≫ φY.hom

/-- A locally free rank-one coefficient line on the actual pro-etale site of the geometric point.

The cover is a `Scheme.Cover` for `Scheme.proetalePrecoverage`; each restriction is the
actual `upperStar.mapMod` restriction of the module object.  Thus the predicate records
pro-etale local triviality rather than a global isomorphism in one ambient category.
Source: the coefficient-line paragraph of the nested Frobenius section.
Source: the cup/sections sub-step of `sk-thm-frobenius` in the nested Frobenius section.
(blueprint: def-pod-condensed-sections-transport-laws). -/
def LocallyFreeRankOne
    {D₀ : WeilConjectures.FiniteFieldDatum.{u}}
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ]
    (L : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of D₀.k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of D₀.k)))) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage (Spec (.of D₀.k)),
    ∀ i : 𝒰.I₀, Nonempty
      (((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapMod
        (condensedRingObj Λ (Spec (.of D₀.k)))).obj L ≅
       ((ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapMod
        (condensedRingObj Λ (Spec (.of D₀.k)))).obj (𝟙_ _))

/-!
This module records the transport package from the Frobenius section statement.  The
definitions below deliberately expose the local trivializations, induced strict data,
canonical cup and projection maps, point evaluation, and degreewise cohomology line that
occur in that statement.
-/

/-- A degree-zero derived coefficient line with an actual pro-etale trivializing cover.

The degree-zero representative is a module on `s = Spec k`; its restriction to every
member of the recorded pro-etale cover is isomorphic to the regular coefficient module.
The derived object is obtained from that representative by the degree-zero single functor.
Source: the opening coefficient-line paragraph of the nested Frobenius section.
Source: the cup/sections sub-step of `sk-thm-frobenius` in the nested Frobenius section.
(blueprint: def-pod-condensed-sections-transport-laws). -/
def DegreeZeroLine
    {D₀ : WeilConjectures.FiniteFieldDatum.{u}}
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ]
    (L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of D₀.k))) Ab.{u + 1})
        (condensedRingObj Λ (Spec (.of D₀.k))))) : Prop :=
  ∃ L₀ : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of D₀.k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of D₀.k))),
    LocallyFreeRankOne L₀ ∧
      Nonempty ((DerivedCategory.singleFunctor _ 0).obj L₀ ≅ L)

/-- Strict data transported through a canonical natural transformation whose components are
known to be invertible.  The transformation itself is the native square exchange; no fresh
natural isomorphism is chosen at this interface.
Source: the cup/sections sub-step of `sk-thm-frobenius` in the nested Frobenius section.
(blueprint: def-pod-condensed-sections-transport-laws). -/
def inducedArrowData {C : Type u} {D : Type v} [Category C] [Category D]
    {PT : C ⥤ C} {PS : D ⥤ D} (H : C ⥤ D)
    (e : H ⋙ PS ⟶ PT ⋙ H) [IsIso e] {X : C} (φX : PT.obj X ≅ X) : PS.obj (H.obj X) ≅ H.obj X :=
  (asIso (e.app X)).trans (H.mapIso φX)

/-- Strict data transported by a canonical exchange whose target image functor is
separately reindexed.
Source: the cup/sections sub-step of `sk-thm-frobenius` in the nested Frobenius section.
(blueprint: def-pod-condensed-sections-transport-laws). -/
def inducedCompactData {C : Type u} {D : Type v} [Category C] [Category D]
    {PT : C ⥤ C} {PS : D ⥤ D} (F₀ F₁ : C ⥤ D)
    (e : F₀ ⋙ PS ⟶ PT ⋙ F₁) [IsIso e] {X : C} (φX : PT.obj X ≅ X) :
    PS.obj (F₀.obj X) ≅ F₁.obj X :=
  (asIso (e.app X)).trans (F₁.mapIso φX)

/-- Tensor strict data induced by the monoidal structure of a pullback action.

The tensorator is the canonical one supplied by the action functor, so this construction
does not permit an independent source or target Frobenius isomorphism.
Source: the tensor-data clause in
`literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-frobenius/
sec-purity-duality-and-frobenius/sk-thm-frobenius/_section.md`
(blueprint: `sk-thm-frobenius`).
Source: the cup/sections sub-step of `sk-thm-frobenius` in the nested Frobenius section.
(blueprint: def-pod-condensed-sections-transport-laws). -/
def inducedTensorData {C : Type u} [Category C] [MonoidalCategory C]
    (P : C ⥤ C) [P.Monoidal] {X Y : C}
    (φX : P.obj X ≅ X) (φY : P.obj Y ≅ Y) :
    P.obj (X ⊗ Y) ≅ X ⊗ Y :=
  (Functor.Monoidal.μIso P X Y).symm ≪≫ MonoidalCategory.tensorIso φX φY

/-- A module is free of rank one over its coefficient ring when it is isomorphic to the
regular module.
Source: the cup/sections sub-step of `sk-thm-frobenius` in the nested Frobenius section.
(blueprint: def-pod-condensed-sections-transport-laws). -/
def FreeRankOneModule {R : Type v} [CommRing R] (V : ModuleCat.{v} R) : Prop :=
  Nonempty (V ≅ ModuleCat.of R R)

/-- The actual coefficient-section module `L(*)` obtained from terminal point sections in
degree zero.  This is the module appearing in the cohomology line comparison, not an
unrelated existential module.
Source: [det-pe-condensed-point-coefficients] and the coefficient-section paragraph of
`literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-frobenius/
sec-purity-duality-and-frobenius/sk-thm-frobenius/_section.md`.
Source: the cup/sections sub-step of `sk-thm-frobenius` in the nested Frobenius section.
(blueprint: def-pod-condensed-sections-transport-laws). -/
def coefficientSectionLine
    {D : WeilConjectures.FiniteFieldDatum.{u}}
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1})
        (condensedRingObj Λ (Spec (.of D.k))))) :
    ModuleCat.{u + 1} (condensedScalarRing Λ) :=
  (CohomologyTransport.sections Λ (Spec (.of D.k))).obj
    ((DerivedCategory.homologyFunctor _ 0).obj L)

/-- Degreewise scalar cohomology after the canonical terminal point evaluation.

The functor is obtained from the published derived homology functor followed by the
published terminal-section/restriction-of-scalars functor; it is therefore the actual
`H^j` of the point realization rather than an existential replacement.
Source: `lem-sf-condensed-geometric-point-perfect-general` and
`det-pe-condensed-point-coefficients` in the current blueprint.
Source: the cup/sections sub-step of `sk-thm-frobenius` in the nested Frobenius section.
(blueprint: def-pod-condensed-sections-transport-laws). -/
def scalarCohomologyFunctor
    {D : WeilConjectures.FiniteFieldDatum.{u}}
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (j : ℤ) :
    DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1})
          (condensedRingObj Λ (Spec (.of D.k)))) ⥤
      ModuleCat.{u + 1} (condensedScalarRing Λ) :=
  (DerivedCategory.homologyFunctor _ j) ⋙
    CohomologyTransport.sections Λ (Spec (.of D.k))

/-- The mixed-support cup map used by the transport package is the intrinsic
construction attached to the chosen compactification, rather than an arbitrary
arrow.
Source: the cup/sections sub-step of `sk-thm-frobenius` in the nested Frobenius section.
(blueprint: def-pod-condensed-sections-transport-laws). -/
def canonicalMixedSupportCupProduct
    {D : WeilConjectures.FiniteFieldDatum.{u}}
    (C : D.CoefficientDatum)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient C.l Λ)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of D.k))
    [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (c : Compactification a)
    (K L : CondensedConstructibleFiniteTor Λ X) :
    (AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification
      Λ c).obj K.obj ⊗
        (AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward Λ a).obj L.obj ⟶
      (AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification
        Λ c).obj (K.obj ⊗ L.obj) :=
  intrinsicFiniteTorMixedSupportCupProduct (Λ := Λ) D C hΛ a c K L

/-- The canonical ordinary projection for the chosen geometric morphism.

This is the published module-object projection map, with source `G N ⊗ L` and target
`G (N ⊗ t^* L)`; it is not an arbitrary endomorphism of `G N ⊗ L`.
Source: `def-sfb-module-object-projection-map` in the current blueprint.
Source: the cup/sections sub-step of `sk-thm-frobenius` in the nested Frobenius section.
(blueprint: def-pod-condensed-sections-transport-laws). -/
def canonicalOrdinaryProjection
    {D : WeilConjectures.FiniteFieldDatum.{u}}
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}} (t : X ⟶ Spec (.of D.k))
    [LocallyOfFiniteType t] [QuasiCompact t] [IsSeparated t]
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)))
    (L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1})
        (condensedRingObj Λ (Spec (.of D.k))))) :
    (moduleObjectDerivedPushforward Λ t).obj N ⊗ L ⟶
      (moduleObjectDerivedPushforward Λ t).obj
        (N ⊗ (moduleObjectDerivedPullback Λ t).obj L) :=
    AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectProjectionMap Λ t N L

/-- The canonical compact-support projection for the selected compactification.

The source and target contain the pullback `t^* L`, and the map is the native exceptional
projection attached to `c`.
Source: `def-exchange-projection` in the current blueprint.
Source: the cup/sections sub-step of `sk-thm-frobenius` in the nested Frobenius section.
(blueprint: def-pod-condensed-sections-transport-laws). -/
def canonicalCompactProjection
    {D : WeilConjectures.FiniteFieldDatum.{u}}
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}} (t : X ⟶ Spec (.of D.k))
    [LocallyOfFiniteType t] [QuasiCompact t] [IsSeparated t]
    (c : Compactification t)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)))
    (L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1})
        (condensedRingObj Λ (Spec (.of D.k))))) :
    (AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing.F Λ c).obj M ⊗ L ⟶
      (AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing.F Λ c).obj
        (M ⊗ (moduleObjectDerivedPullback Λ t).obj L) :=
  AlgebraicGeometry.ProEtale.CondensedRing.exceptionalProjectionMorphismOfCompactification
    Λ c M L

/-- Shifted strict data are induced by the functor's canonical commutation with shifts.
Source: the cup/sections sub-step of `sk-thm-frobenius` in the nested Frobenius section.
(blueprint: def-pod-condensed-sections-transport-laws). -/
def shiftedInducedData {C : Type u} [Category C] [HasShift C ℤ]
    (P : C ⥤ C) [P.CommShift ℤ]
    {X : C} (φX : P.obj X ≅ X) (r : ℤ) :
    P.obj (X⟦r⟧) ≅ X⟦r⟧ :=
  (P.commShiftIso r).app X ≪≫ (shiftFunctor C r).mapIso φX

/-- The native trivialization of point Frobenius pullback, retaining its direction.
Its inverse is restriction along geometric Frobenius on point sections.
Source: the point-transport paragraph of `sk-thm-frobenius`.
(blueprint: def-pod-condensed-sections-transport-laws). -/
def pointPullbackIso
    {D : WeilConjectures.FiniteFieldDatum.{u}}
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    moduleObjectDerivedPullback Λ (StrictWeilCondensed.pointFrobenius D).hom ≅ 𝟭 _ :=
  AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ _ ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarIsoIdOfIsSepClosed Λ _) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The fixed geometric-point fibre of the recorded point-perfect theorem agrees
with exact terminal scalar sections through the published point-adjunction comparison.
Source: `lem-sf-condensed-geometric-point-perfect-general` and the explicit point
transport (blueprint: def-pod-condensed-sections-transport-laws). -/
def canonicalPointEvaluationIso
    {D : WeilConjectures.FiniteFieldDatum.{u}}
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    CondensedGeometricPoint.fiber Λ D.k ≅
      (CohomologyTransport.sections Λ (Spec (.of D.k))).mapDerivedCategory :=
  (CondensedGeometricPoint.heartFiberDerivedIso Λ D.k).symm ≪≫
    Functor.mapDerivedCategoryNatIso (WeilConjectures.directFrobeniusHeartSectionsIso Λ D.k)

/-- The operator on point realization is restriction along Frobenius followed by
realization of the supplied strict datum, `Γ(φ) ρ`.
Source: Step 6 of the node (blueprint: def-pod-condensed-sections-transport-laws). -/
def pointOperator {A : Type u} {B : Type v} [Category A] [Category B]
    (Γ : A ⥤ B) {P : A ⥤ A} (rho : 𝟭 A ≅ P) {X : A} (φ : P.obj X ≅ X) :
    Γ.obj X ≅ Γ.obj X :=
  Γ.mapIso ((rho.app X) ≪≫ φ)

/-- The scalar cup or projection square, including the actual sections prefactor μΓ.
The operators are induced by the supplied strict data and point restriction.
Source: Step 6 (blueprint: def-pod-condensed-sections-transport-laws). -/
def EvaluatedTensorIntertwining
    {A : Type u} {B : Type v} [Category A] [Category B]
    [MonoidalCategory A] [MonoidalCategory B]
    (Γ : A ⥤ B) {P : A ⥤ A} (rho : 𝟭 A ≅ P)
    (mu : ∀ X Y : A, Γ.obj X ⊗ Γ.obj Y ⟶ Γ.obj (X ⊗ Y))
    {X Y Z : A} (f : X ⊗ Y ⟶ Z)
    (φX : P.obj X ≅ X) (φY : P.obj Y ≅ Y) (φZ : P.obj Z ≅ Z) : Prop :=
  ((pointOperator Γ rho φX).hom ⊗ₘ (pointOperator Γ rho φY).hom) ≫
      mu X Y ≫ Γ.map f =
    (mu X Y ≫ Γ.map f) ≫ (pointOperator Γ rho φZ).hom

/-- The canonical coefficient inclusion `R → H⁰(Γ_s Λ_s)`. It is the ordinary
section unit followed by the single-complex homology identification, rather than an
identity function chosen in place of the coefficient action.
Source: the scalar-unit paragraph (blueprint: def-pod-condensed-sections-transport-laws). -/
def coefficientUnitMap
    {D : WeilConjectures.FiniteFieldDatum.{u}}
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    ModuleCat.of (condensedScalarRing Λ) (condensedScalarRing Λ) ⟶
      (scalarCohomologyFunctor (D := D) Λ 0).obj (𝟙_ _) :=
  (pairingExactScalarPointCup Λ D.k).ordinary.ε ≫
    (CohomologyTransport.sections Λ (Spec (.of D.k))).map
      (((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app (𝟙_ _)).inv ≫
        (DerivedCategory.homologyFunctor _ 0).map
          (DerivedCategory.singleFunctorObjUnitIso _).hom)

/-- The scalar operator conjugated through the actual coefficient-unit inclusion.
In the item it is `Γ_s(φ_Λ)ρ_Λ`, expressed on the regular module R itself.
Source: Step 6 (blueprint: def-pod-condensed-sections-transport-laws). -/
def coefficientUnitTransport {R : Type w} [CommRing R] {V : ModuleCat.{w} R}
    (unitMap : ModuleCat.of R R ⟶ V) [IsIso unitMap] (action : V ⟶ V) :
    ModuleCat.of R R ⟶ ModuleCat.of R R :=
  unitMap ≫ action ≫ inv unitMap

set_option maxHeartbeats 0 in
-- Elaborating the native unbounded derived functor endpoints exceeds the default limit.
/-- The native transport package. Compactification comparisons are normalized by
EVERY common refinement, and therefore determine the exchange back to the chosen
compactification. The degreewise line isomorphism is normalized for EVERY
trivialization of L, by the projection map and the section unit; this is the
basis-independent map [z]⊗v ↦ [z⊗v], with the displayed tensor Frobenius.
Source: all six node steps (blueprint: def-pod-condensed-sections-transport-laws). -/
def Laws
    {D₀ : WeilConjectures.FiniteFieldDatum.{u}}
    (C₀ : D₀.CoefficientDatum)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛloc : IsLocalizingAdmissibleCoefficient C₀.l Λ)
    (T₀ : Over (Spec (.of D₀.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
    (c : Compactification (D₀.geometricFiber T₀).hom)
    (L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of D₀.k))) Ab.{u + 1})
        (condensedRingObj Λ (Spec (.of D₀.k)))))
    (_hL : DegreeZeroLine L)
    (φL : (StrictWeilCondensed.action Λ
      (StrictWeilCondensed.pointFrobenius D₀)).obj L ≅ L) : Prop := by
  let q := CohomologyTransport.geometricFrobeniusGeometry D₀ T₀
  let PT := moduleObjectDerivedPullback Λ q.h.hom
  let PS := moduleObjectDerivedPullback Λ q.b.hom
  letI : PT.Monoidal := by dsimp [PT, moduleObjectDerivedPullback]; infer_instance
  letI : PS.Monoidal := by dsimp [PS, moduleObjectDerivedPullback]; infer_instance
  letI : PT.CommShift ℤ := by dsimp [PT, moduleObjectDerivedPullback]; infer_instance
  let c₁ := CohomologyTransport.reindex q.b.hom q.h.hom q.comm c
  let F := fun d : Compactification q.a => CompactificationReindexing.F Λ d
  let G := moduleObjectDerivedPushforward Λ q.a
  let U := moduleObjectDerivedPullback Λ q.a
  letI : (F c).CommShift ℤ := by
    dsimp [F, CompactificationReindexing.F, rightDerivedLowerShriekOfCompactification]
    infer_instance
  letI : G.CommShift ℤ := by dsimp [G, moduleObjectDerivedPushforward]; infer_instance
  let ctf := condensedConstructibleFiniteTor Λ q.X
  let eD := WeilConjectures.FrobeniusSquareExchange.direct (Mon.mk Λ) q.a (CommSq.mk q.comm)
  let eC := CompactificationReindexing.squareExchange Λ
    (CohomologyTransport.frobeniusReindexedSquare q c)
  let eU := (CohomologyTransport.square Λ q.h.hom q.a q.a q.b.hom q.comm).symm
  let φL' := (AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ
    (StrictWeilCondensed.pointFrobenius D₀).hom).app L ≪≫ φL
  let φUL := (eU.app L) ≪≫ U.mapIso φL'
  let Γ := CondensedGeometricPoint.fiber Λ D₀.k
  let eta := canonicalPointEvaluationIso (D := D₀) Λ
  let rho := (pointPullbackIso (D := D₀) Λ).symm
  let mu := fun A B =>
    ((eta.app A).hom ⊗ₘ (eta.app B).hom) ≫
      (pairingExactScalarPointCup Λ D₀.k).derived.μ A B ≫ (eta.app (A ⊗ B)).inv
  let H := fun j : ℤ => scalarCohomologyFunctor (D := D₀) Λ j
  let unitMap := coefficientUnitMap (D := D₀) Λ
  let cup := fun {M N : _} (hM : ctf M) (hN : ctf N) =>
    canonicalMixedSupportCupProduct C₀ Λ hΛloc q.a c ⟨M, hM⟩ ⟨N, hN⟩
  let piG := fun N => canonicalOrdinaryProjection Λ q.a N L
  let piF := fun M => canonicalCompactProjection Λ q.a c M L
  exact
    FreeRankOneModule (coefficientSectionLine Λ L) ∧ Nonempty (L ≅ 𝟙_ _) ∧
    IsIso eD ∧ IsIso eC ∧ IsIso unitMap ∧
    (∀ (hD : IsIso eD) (hC : IsIso eC),
      letI := hD
      letI := hC
      ∃ compare : ∀ (d e : Compactification q.a) (M : _) (_ : ctf M),
          (F d).obj M ≅ (F e).obj M,
        (∀ (d e r : Compactification q.a) (hd : r.Refinement d) (he : r.Refinement e)
          (M : _) (hM : ctf M),
          IsIso ((CompactificationReindexing.refinement Λ he).app M) ∧
          (compare d e M hM).hom ≫ (CompactificationReindexing.refinement Λ he).app M =
            (CompactificationReindexing.refinement Λ hd).app M) ∧
        (∀ (d e : Compactification q.a) {M N : _} (hM : ctf M) (hN : ctf N)
          (f : M ⟶ N),
          (F d).map f ≫ (compare d e N hN).hom =
            (compare d e M hM).hom ≫ (F e).map f) ∧
        (let φF := fun {M : _} (hM : ctf M) (φM : PT.obj M ≅ M) =>
            inducedCompactData (F c) (F c₁) eC φM ≪≫ compare c₁ c M hM
         let φG := fun {N : _} (φN : PT.obj N ≅ N) => inducedArrowData G eD φN
         (∀ {M N : _} (hM : ctf M) (hN : ctf N) (f : M ⟶ N)
           (φM : PT.obj M ≅ M) (φN : PT.obj N ≅ N),
           IsIntertwining PT f φM φN →
             IsIntertwining PS (G.map f) (φG φM) (φG φN) ∧
             IsIntertwining PS ((F c).map f) (φF hM φM) (φF hN φN)) ∧
         (∀ {M N : _} (hM : ctf M) (hN : ctf N) (hMN : ctf (M ⊗ N))
           (φM : PT.obj M ≅ M) (φN : PT.obj N ≅ N),
           IsIntertwining PS (cup hM hN)
             (inducedTensorData PS (φF hM φM) (φG φN))
             (φF hMN (inducedTensorData PT φM φN)) ∧
           EvaluatedTensorIntertwining Γ rho mu (cup hM hN)
             (φF hM φM) (φG φN) (φF hMN (inducedTensorData PT φM φN))) ∧
         (∀ {M N : _} (hM : ctf M) (hN : ctf N) (r s : ℤ)
           (hMr : ctf (M⟦r⟧)) (hNs : ctf (N⟦s⟧))
           (hTensor : ctf (M⟦r⟧ ⊗ N⟦s⟧))
           (φM : PT.obj M ≅ M) (φN : PT.obj N ≅ N),
           cup hMr hNs =
             ((((F c).commShiftIso r).app M).hom ⊗ₘ ((G.commShiftIso s).app N).hom) ≫
               (DerivedCategory.shiftTensorShiftIso _ ((F c).obj M) (G.obj N) r s).hom ≫
               (shiftFunctor _ (r+s)).map (cup hM hN) ≫
               (((F c).commShiftIso (r+s)).app (M ⊗ N)).inv ≫
               (F c).map (DerivedCategory.shiftTensorShiftIso _ M N r s).inv ∧
           IsIntertwining PS (cup hMr hNs)
             (inducedTensorData PS (φF hMr (shiftedInducedData PT φM r))
               (φG (shiftedInducedData PT φN s)))
             (φF hTensor (inducedTensorData PT (shiftedInducedData PT φM r)
               (shiftedInducedData PT φN s)))) ∧
         (∀ {N : _} (hN : ctf N) (hNL : ctf (N ⊗ U.obj L))
           (φN : PT.obj N ≅ N),
           IsIso (piG N) ∧ IsIso (piF N) ∧
           IsIntertwining PS (piG N) (inducedTensorData PS (φG φN) φL')
             (φG (inducedTensorData PT φN φUL)) ∧
           IsIntertwining PS (piF N) (inducedTensorData PS (φF hN φN) φL')
             (φF hNL (inducedTensorData PT φN φUL)) ∧
           EvaluatedTensorIntertwining Γ rho mu (piG N) (φG φN) φL'
             (φG (inducedTensorData PT φN φUL)) ∧
           EvaluatedTensorIntertwining Γ rho mu (piF N) (φF hN φN) φL'
             (φF hNL (inducedTensorData PT φN φUL)) ∧
           IsIso (mu (G.obj N) L ≫ Γ.map (piG N))) ∧
         (∀ hUnit : IsIso unitMap,
           letI := hUnit
           coefficientUnitTransport unitMap
             ((H 0).map ((rho.app (𝟙_ _)).hom ≫
               (leftDerivedUpperStarUnitIso Λ q.b.hom).hom)) = 𝟙 _) ∧
         (∀ {N : _} (_hN : ctf N) (φN : PT.obj N ≅ N) (j : ℤ),
           ∃ e : (H j).obj (G.obj (N ⊗ U.obj L)) ≅
               (H j).obj (G.obj N) ⊗ coefficientSectionLine Λ L,
             (∀ h : L ≅ 𝟙_ _,
               (𝟙 ((H j).obj (G.obj N)) ⊗ₘ
                   (unitMap ≫ (H 0).map h.inv)) ≫ e.inv =
                 (ρ_ ((H j).obj (G.obj N))).hom ≫
                   (H j).map ((ρ_ (G.obj N)).inv ≫
                     (𝟙 (G.obj N) ⊗ₘ h.inv) ≫ piG N)) ∧
             (((H j).map ((rho.app (G.obj N)).hom ≫ (φG φN).hom)) ⊗ₘ
                 ((H 0).map ((rho.app L).hom ≫ φL'.hom))) ≫ e.inv =
               e.inv ≫ (H j).map
                 ((rho.app (G.obj (N ⊗ U.obj L))).hom ≫
                   (φG (inducedTensorData PT φN φUL)).hom))))

set_option maxHeartbeats 0 in
-- The native unbounded-derived endpoints require additional elaboration heartbeats.
/-- The common-refinement, cup, shift, and line-projection clauses of the transport package.
Source: Steps 1--5 of the condensed sections transport proof.
(blueprint: def-pod-condensed-sections-transport-laws). -/
def GeometricLaws
    {D₀ : WeilConjectures.FiniteFieldDatum.{u}}
    (C₀ : D₀.CoefficientDatum)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛloc : IsLocalizingAdmissibleCoefficient C₀.l Λ)
    (T₀ : Over (Spec (.of D₀.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
    (c : Compactification (D₀.geometricFiber T₀).hom)
    (L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of D₀.k))) Ab.{u + 1})
        (condensedRingObj Λ (Spec (.of D₀.k)))))
    (_hL : DegreeZeroLine L)
    (φL : (StrictWeilCondensed.action Λ
      (StrictWeilCondensed.pointFrobenius D₀)).obj L ≅ L) : Prop := by
  let q := CohomologyTransport.geometricFrobeniusGeometry D₀ T₀
  let PT := moduleObjectDerivedPullback Λ q.h.hom
  let PS := moduleObjectDerivedPullback Λ q.b.hom
  letI : PT.Monoidal := by dsimp [PT, moduleObjectDerivedPullback]; infer_instance
  letI : PS.Monoidal := by dsimp [PS, moduleObjectDerivedPullback]; infer_instance
  letI : PT.CommShift ℤ := by dsimp [PT, moduleObjectDerivedPullback]; infer_instance
  let c₁ := CohomologyTransport.reindex q.b.hom q.h.hom q.comm c
  let F := fun d : Compactification q.a => CompactificationReindexing.F Λ d
  let G := moduleObjectDerivedPushforward Λ q.a
  let U := moduleObjectDerivedPullback Λ q.a
  letI : (F c).CommShift ℤ := by
    dsimp [F, CompactificationReindexing.F, rightDerivedLowerShriekOfCompactification]
    infer_instance
  letI : G.CommShift ℤ := by dsimp [G, moduleObjectDerivedPushforward]; infer_instance
  let ctf := condensedConstructibleFiniteTor Λ q.X
  let eD := WeilConjectures.FrobeniusSquareExchange.direct (Mon.mk Λ) q.a (CommSq.mk q.comm)
  let eC := CompactificationReindexing.squareExchange Λ
    (CohomologyTransport.frobeniusReindexedSquare q c)
  let eU := (CohomologyTransport.square Λ q.h.hom q.a q.a q.b.hom q.comm).symm
  let φL' := (AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ
    (StrictWeilCondensed.pointFrobenius D₀).hom).app L ≪≫ φL
  let φUL := (eU.app L) ≪≫ U.mapIso φL'
  let cup := fun {M N : _} (hM : ctf M) (hN : ctf N) =>
    canonicalMixedSupportCupProduct C₀ Λ hΛloc q.a c ⟨M, hM⟩ ⟨N, hN⟩
  let piG := fun N => canonicalOrdinaryProjection Λ q.a N L
  let piF := fun M => canonicalCompactProjection Λ q.a c M L
  exact
    (∀ (hD : IsIso eD) (hC : IsIso eC),
      letI := hD
      letI := hC
      ∃ compare : ∀ (d e : Compactification q.a) (M : _) (_ : ctf M),
          (F d).obj M ≅ (F e).obj M,
        (∀ (d e r : Compactification q.a) (hd : r.Refinement d) (he : r.Refinement e)
          (M : _) (hM : ctf M),
          IsIso ((CompactificationReindexing.refinement Λ he).app M) ∧
          (compare d e M hM).hom ≫ (CompactificationReindexing.refinement Λ he).app M =
            (CompactificationReindexing.refinement Λ hd).app M) ∧
        (∀ (d e : Compactification q.a) {M N : _} (hM : ctf M) (hN : ctf N)
          (f : M ⟶ N),
          (F d).map f ≫ (compare d e N hN).hom =
            (compare d e M hM).hom ≫ (F e).map f) ∧
        (let φF := fun {M : _} (hM : ctf M) (φM : PT.obj M ≅ M) =>
            inducedCompactData (F c) (F c₁) eC φM ≪≫ compare c₁ c M hM
         let φG := fun {N : _} (φN : PT.obj N ≅ N) => inducedArrowData G eD φN

         (∀ {M N : _} (hM : ctf M) (hN : ctf N) (hMN : ctf (M ⊗ N))
           (φM : PT.obj M ≅ M) (φN : PT.obj N ≅ N),
           IsIntertwining PS (cup hM hN)
             (inducedTensorData PS (φF hM φM) (φG φN))
             (φF hMN (inducedTensorData PT φM φN))) ∧
         (∀ {M N : _} (hM : ctf M) (hN : ctf N) (r s : ℤ)
           (hMr : ctf (M⟦r⟧)) (hNs : ctf (N⟦s⟧))
           (hTensor : ctf (M⟦r⟧ ⊗ N⟦s⟧))
           (φM : PT.obj M ≅ M) (φN : PT.obj N ≅ N),
           cup hMr hNs =
             ((((F c).commShiftIso r).app M).hom ⊗ₘ ((G.commShiftIso s).app N).hom) ≫
               (DerivedCategory.shiftTensorShiftIso _ ((F c).obj M) (G.obj N) r s).hom ≫
               (shiftFunctor _ (r+s)).map (cup hM hN) ≫
               (((F c).commShiftIso (r+s)).app (M ⊗ N)).inv ≫
               (F c).map (DerivedCategory.shiftTensorShiftIso _ M N r s).inv ∧
           IsIntertwining PS (cup hMr hNs)
             (inducedTensorData PS (φF hMr (shiftedInducedData PT φM r))
               (φG (shiftedInducedData PT φN s)))
             (φF hTensor (inducedTensorData PT (shiftedInducedData PT φM r)
               (shiftedInducedData PT φN s)))) ∧
         (∀ {N : _} (hN : ctf N) (hNL : ctf (N ⊗ U.obj L))
           (φN : PT.obj N ≅ N),
           IsIso (piF N) ∧
           IsIntertwining PS (piG N) (inducedTensorData PS (φG φN) φL')
             (φG (inducedTensorData PT φN φUL)) ∧
           IsIntertwining PS (piF N) (inducedTensorData PS (φF hN φN) φL')
             (φF hNL (inducedTensorData PT φN φUL)))))

set_option maxHeartbeats 0 in
-- The native unbounded-derived endpoints require additional elaboration heartbeats.
/-- The exact-point evaluation and coefficient-line clauses of the transport package.
Source: Steps 5--6 of the condensed sections transport proof.
(blueprint: def-pod-condensed-sections-transport-laws). -/
def ScalarLaws
    {D₀ : WeilConjectures.FiniteFieldDatum.{u}}
    (C₀ : D₀.CoefficientDatum)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hΛloc : IsLocalizingAdmissibleCoefficient C₀.l Λ)
    (T₀ : Over (Spec (.of D₀.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
    (_c : Compactification (D₀.geometricFiber T₀).hom)
    (L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of D₀.k))) Ab.{u + 1})
        (condensedRingObj Λ (Spec (.of D₀.k)))))
    (_hL : DegreeZeroLine L)
    (φL : (StrictWeilCondensed.action Λ
      (StrictWeilCondensed.pointFrobenius D₀)).obj L ≅ L) : Prop := by
  let q := CohomologyTransport.geometricFrobeniusGeometry D₀ T₀
  let PT := moduleObjectDerivedPullback Λ q.h.hom
  let PS := moduleObjectDerivedPullback Λ q.b.hom
  letI : PT.Monoidal := by dsimp [PT, moduleObjectDerivedPullback]; infer_instance
  letI : PS.Monoidal := by dsimp [PS, moduleObjectDerivedPullback]; infer_instance
  let G := moduleObjectDerivedPushforward Λ q.a
  let U := moduleObjectDerivedPullback Λ q.a
  let ctf := condensedConstructibleFiniteTor Λ q.X
  let eD := WeilConjectures.FrobeniusSquareExchange.direct (Mon.mk Λ) q.a (CommSq.mk q.comm)
  let eU := (CohomologyTransport.square Λ q.h.hom q.a q.a q.b.hom q.comm).symm
  let φL' := (AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ
    (StrictWeilCondensed.pointFrobenius D₀).hom).app L ≪≫ φL
  let φUL := (eU.app L) ≪≫ U.mapIso φL'
  let rho := (pointPullbackIso (D := D₀) Λ).symm
  let H := fun j : ℤ => scalarCohomologyFunctor (D := D₀) Λ j
  let unitMap := coefficientUnitMap (D := D₀) Λ
  let piG := fun N => canonicalOrdinaryProjection Λ q.a N L
  exact
    IsIso unitMap ∧
    (∀ A B, (rho.app (A ⊗ B)).hom ≫ (Functor.Monoidal.μIso PS A B).inv =
      (rho.app A).hom ⊗ₘ (rho.app B).hom) ∧
    (∀ (hD : IsIso eD),
      letI := hD
      let φG := fun {N : _} (φN : PT.obj N ≅ N) => inducedArrowData G eD φN
      (∀ {N : _} (_hN : ctf N) (φN : PT.obj N ≅ N) (j : ℤ),
           IsIntertwining PS (piG N) (inducedTensorData PS (φG φN) φL')
             (φG (inducedTensorData PT φN φUL)) →
           ∃ e : (H j).obj (G.obj (N ⊗ U.obj L)) ≅
               (H j).obj (G.obj N) ⊗ coefficientSectionLine Λ L,
             (∀ h : L ≅ 𝟙_ _,
               (𝟙 ((H j).obj (G.obj N)) ⊗ₘ
                   (unitMap ≫ (H 0).map h.inv)) ≫ e.inv =
                 (ρ_ ((H j).obj (G.obj N))).hom ≫
                   (H j).map ((ρ_ (G.obj N)).inv ≫
                     (𝟙 (G.obj N) ⊗ₘ h.inv) ≫ piG N)) ∧
             (((H j).map ((rho.app (G.obj N)).hom ≫ (φG φN).hom)) ⊗ₘ
                 ((H 0).map ((rho.app L).hom ≫ φL'.hom))) ≫ e.inv =
               e.inv ≫ (H j).map
                 ((rho.app (G.obj (N ⊗ U.obj L))).hom ≫
                   (φG (inducedTensorData PT φN φUL)).hom)))

end AlgebraicGeometry.ProEtale.CondensedSectionsCupWeilTransport
