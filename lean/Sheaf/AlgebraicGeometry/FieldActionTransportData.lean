module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import Sheaf.AlgebraicGeometry.CondensedGaloisGlobalDescent
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-! # Normalized field-action transport interfaces

Source: Bhatt--Scholze Example 4.1.10, Definition 6.8.3 and Proposition 6.8.4;
main-20261015 direct-images paragraph (3), normalized ordinary derived sections
(blueprint: def-sfb-field-action-transport-data).

## Main definitions

* `FieldData`: the existing geometric field functor with its equivalence property.
* `AdjunctionSquare`: comparison of both adjoints normalized on all Hom transposes.
* `IsNormalizedComparison`, `IsNormalizedPostComparison`: total-derived-unit equations.
* `ForgetData`, `PointAdjunctionData`: exact forgetting and the actual point adjunction.
* Scalar and derived aliases retain the existing constructions in a common universe.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FieldActionTransport

open CondensedGalois

attribute [instance] GeometricData.additive pointUnit_isMonHom

/-- A square of scalar adjunctions, including the equation for every transpose.
This equation fixes both units and counits, not only the two functor isomorphisms.
Source: field-action node, scalar-adjunction clause
(blueprint: def-sfb-field-action-transport-data). -/
structure AdjunctionSquare
    {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
    {L : C ⥤ D} {V : D ⥤ C} {L' : C' ⥤ D'} {V' : D' ⥤ C'}
    (adj : L ⊣ V) (adj' : L' ⊣ V') (E : C ⥤ C') (F : D ⥤ D') where
  /-- Scalar restriction comparison. -/
  restriction : V ⋙ E ≅ F ⋙ V'
  /-- Ordinary or derived extension comparison. -/
  extension : L ⋙ F ≅ E ⋙ L'
  /-- Transport preserves the specified adjunction bijection. -/
  transpose : ∀ (M : C) (N : D) (f : L.obj M ⟶ N),
    adj'.homEquiv (E.obj M) (F.obj N) (extension.inv.app M ≫ F.map f) =
      E.map (adj.homEquiv M N f) ≫ restriction.hom.app N

section Normalizations
variable {C A D B : Type (u + 2)}
  [Category.{u + 1} C] [Category.{u + 1} A] [Category.{u + 1} D] [Category.{u + 1} B]
  [Abelian C] [Abelian A] [Abelian D] [Abelian B]
  [HasDerivedCategory.{u + 2} C] [HasDerivedCategory.{u + 2} A]
  [HasDerivedCategory.{u + 2} D] [HasDerivedCategory.{u + 2} B]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
  (F : C ⥤ A) [addF : F.Additive] (E : A ⥤ B) [addE : E.Additive]
  [PreservesFiniteLimits E] [PreservesFiniteColimits E]
  (L : C ⥤ D) [addL : L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (P : D ⥤ B) [addP : P.Additive]

/-- The defining total-derived-unit equation for an exact-last/exact-first comparison.
Source: field-action node, normalized slice/composition comparison
(blueprint: def-sfb-field-action-transport-data). -/
def IsNormalizedComparison (o : F ⋙ E ≅ L ⋙ P)
    (δ : F.rightDerivedFunctor ⋙ E.mapDerivedCategory ≅
      L.mapDerivedCategory ⋙ P.rightDerivedFunctor) : Prop :=
  ∀ J : HomotopyCategory C (.up ℤ),
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F E).app J ≫
        δ.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory o.hom (.up ℤ)).app J) ≫
        (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit L P).app J

/-- The analogous unit equation for a direct comparison to a single right-derived functor.
Source: field-action node, normalized field comparison
(blueprint: def-sfb-field-action-transport-data). -/
def IsNormalizedPostComparison (H : C ⥤ B) [addH : H.Additive] (o : F ⋙ E ≅ H)
    (δ : F.rightDerivedFunctor ⋙ E.mapDerivedCategory ≅ H.rightDerivedFunctor) : Prop :=
  ∀ J : HomotopyCategory C (.up ℤ),
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F E).app J ≫
        δ.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory o.hom (.up ℤ)).app J) ≫
        H.rightDerivedFunctorUnit.app J

end Normalizations

variable (k ks : Type u) [Field k] [Field ks] [Algebra k ks] [IsSepClosure k ks]

/-- The normalized field equivalence: its functor is the existing geometric section
functor, with its geometric restriction and variable Galois-action formulas.
Source: Bhatt--Scholze Example 4.1.10, field-action node first paragraph
(blueprint: def-sfb-field-action-transport-data). -/
structure FieldData (R : Coefficients.{u})
    [CategoryTheory.CondensedBar.ActionAbelian R (ks ≃ₐ[k] ks)] where
  /-- The fixed section and action normalization from the dependency. -/
  geometric : GeometricData k ks (Spec (.of k)) (𝟙 _) R.toMon
  /-- Geometric sections are an equivalence, including for the trivial Galois group. -/
  equivalence : geometric.functor.IsEquivalence

attribute [instance] FieldData.equivalence

/-- The field functor, retaining the dependency's normalized sections.
Source: Bhatt--Scholze Example 4.1.10
(blueprint: def-sfb-field-action-transport-data). -/
abbrev fieldFunctor {R : Coefficients.{u}}
    [CategoryTheory.CondensedBar.ActionAbelian R (ks ≃ₐ[k] ks)] (e : FieldData k ks R) :=
  e.geometric.functor

/-- The field functor retains the additive structure of geometric sections.
Source: field-action node, exact additive equivalence
(blueprint: def-sfb-field-action-transport-data). -/
instance fieldFunctor_additive {R : Coefficients.{u}}
    [CategoryTheory.CondensedBar.ActionAbelian R (ks ≃ₐ[k] ks)] (e : FieldData k ks R) :
    (fieldFunctor k ks e).Additive := e.geometric.additive

/-- Restriction of the actual pulled-back ring map on an arbitrary scheme.
Source: field-action node, arbitrary coefficient maps
(blueprint: def-sfb-field-action-transport-data). -/
abbrev scalarMap {R R' : Coefficients.{u}} (φ : R ⟶ R') (Y : Scheme.{u}) :=
  (upperStarFromPoint Y).map φ.hom.hom

/-- Ordinary extension uses the existing balanced tensor construction.
Source: field-action node, ordinary scalar extension
(blueprint: def-sfb-field-action-transport-data). -/
abbrev extend {R R' : Coefficients.{u}} (φ : R ⟶ R') (Y : Scheme.{u}) :=
  Mod.extendScalars (scalarMap φ Y)

/-- The standard common-universe localization on the transparent pulled-back ring.
This is the same standard localization as CondensedGalois.moduleDerived, exposed at
condensedRingObj for the upstream scalar and pushforward interfaces.
Source: field-action node, compatible-universe convention
(blueprint: def-sfb-field-action-transport-data). -/
instance pulledModulesDerived
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] (Y : Scheme.{u}) :
    HasDerivedCategory.{u + 2}
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :=
  HasDerivedCategory.standard _

/-- Derived extension is the existing total K-flat left-derived functor.
Source: field-action node, derived scalar extension
(blueprint: def-sfb-field-action-transport-data). -/
abbrev derivedExtend {R R' : Coefficients.{u}} (φ : R ⟶ R') (Y : Scheme.{u}) :
    DerivedCategory.{u + 2} (Modules R.toMon Y) ⥤
      DerivedCategory.{u + 2} (Modules R'.toMon Y) :=
  (extend φ Y).leftDerivedFunctor.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}

/-- The same scalar adjunction in the common localization universe of Galois descent.
Its body is the general derived adjunction followed by exact restriction's canonical
comparison; no identification of the site object and morphism universes is imposed.
Source: field-action node, derived scalar adjunction
(blueprint: def-sfb-field-action-transport-data). -/
def scalarDerivedAdjunction {R R' : Coefficients.{u}} (φ : R ⟶ R') (Y : Scheme.{u}) :
    derivedExtend φ Y ⊣ (restrictX φ Y).mapDerivedCategory :=
  (Mod.extendRestrictAdjunction (scalarMap φ Y)).derivedAdjunction.{u + 2, u + 2, u + 1,
    u + 1, u + 2, u + 2}.ofNatIsoRight
    (restrictX φ Y).rightDerivedFunctorIsoMapDerivedCategory

/-- Canonical scalar-extension shifts are the adjoints of exact restriction's shifts.
This uses the actual derived scalar adjunction and introduces no choice of shift data.
Source: field-action node, canonical scalar shifts
(blueprint: def-sfb-field-action-transport-data). -/
instance derivedExtendCommShift {R R' : Coefficients.{u}} (φ : R ⟶ R') (Y : Scheme.{u}) :
    (derivedExtend φ Y).CommShift ℤ :=
  (scalarDerivedAdjunction φ Y).leftAdjointCommShift ℤ

/-- Condensed scalar extension in that same localization universe.
Source: field-action node, forgotten scalar adjunction
(blueprint: def-sfb-field-action-transport-data). -/
abbrev condensedDerivedExtend {R R' : Coefficients.{u}} (φ : R ⟶ R') :
    DerivedCategory.{u + 2} (Profinite.CondensedAction.Modules R.toMon) ⥤
      DerivedCategory.{u + 2} (Profinite.CondensedAction.Modules R'.toMon) :=
  (Mod.extendScalars φ.hom.hom).leftDerivedFunctor.{u + 2, u + 2, u + 1, u + 1,
    u + 2, u + 2}

/-- The condensed scalar adjunction with the canonical exact-restriction comparison.
Source: field-action node, forgotten derived scalar adjunction
(blueprint: def-sfb-field-action-transport-data). -/
def condensedScalarAdjunction {R R' : Coefficients.{u}} (φ : R ⟶ R') :
    condensedDerivedExtend φ ⊣ (restrictCondensed φ).mapDerivedCategory :=
  (Mod.extendRestrictAdjunction φ.hom.hom).derivedAdjunction.{u + 2, u + 2, u + 1, u + 1, u + 2,
    u + 2}.ofNatIsoRight
    (restrictCondensed φ).rightDerivedFunctorIsoMapDerivedCategory

/-- Exact conservative forgetting, in the ordinary and unbounded derived categories.
Source: field-action node, forgetting clause
(blueprint: def-sfb-field-action-transport-data). -/
class ForgetData (R : Coefficients.{u})
    [CategoryTheory.CondensedBar.ActionAbelian R (ks ≃ₐ[k] ks)] where
  /-- Kernels are the underlying kernels. -/
  [limits : PreservesFiniteLimits
    (CategoryTheory.CondensedBar.forgetAction (A := R) (G := ks ≃ₐ[k] ks))]
  /-- Cokernels are the underlying cokernels. -/
  [colimits : PreservesFiniteColimits
    (CategoryTheory.CondensedBar.forgetAction (A := R) (G := ks ≃ₐ[k] ks))]
  /-- Underlying invertibility detects invertibility. -/
  conservative : (CategoryTheory.CondensedBar.forgetAction
    (A := R) (G := ks ≃ₐ[k] ks)).ReflectsIsomorphisms
  /-- The same detection holds after localization at quasi-isomorphisms. -/
  derivedConservative : (CategoryTheory.CondensedBar.forgetAction
    (A := R) (G := ks ≃ₐ[k] ks)).mapDerivedCategory.ReflectsIsomorphisms

attribute [instance] ForgetData.limits ForgetData.colimits




/-- The structural map from the geometric scheme to the geometric point of Spec k.
Source: field-action node, geometric base change
(blueprint: def-sfb-field-action-transport-data). -/
def geometricToField (X : Scheme.{u}) (a : X ⟶ Spec (.of k)) :
    geometricScheme.{u} k ks X a ⟶ geometricScheme.{u} k ks (Spec (.of k)) (𝟙 _) :=
  pullback.lift (geometricProjection.{u} k ks X a ≫ a)
    (pullback.snd a (Spec.map (CommRingCat.ofHom (algebraMap k ks))))
    (by simp [geometricProjection, pullback.condition])

/-- Pullback from the condensed point on actual internal modules.
Source: field-action node, p_{X^s}^*
(blueprint: def-sfb-field-action-transport-data). -/
abbrev pointPull (R : Coefficients.{u}) (Y : Scheme.{u}) :
    Profinite.CondensedAction.Modules R.toMon ⥤ Modules R.toMon Y :=
  (upperStarFromPoint Y).mapMod R.X

/-- The point module adjunction, with unit and counit on the original abelian sheaves.
These equations fix the adjunction without a second construction of point direct image.
Source: field-action node, structural geometric morphism
(blueprint: def-sfb-field-action-transport-data). -/
class PointAdjunctionData (R : Coefficients.{u}) (Y : Scheme.{u}) where
  /-- Direct image is additive. -/
  [additive : (pointModules.{u} R.toMon Y).Additive]
  /-- Inverse image is additive and exact. -/
  [pullAdditive : (pointPull R Y).Additive]
  /-- Inverse image preserves kernels. -/
  [pullLimits : PreservesFiniteLimits (pointPull R Y)]
  /-- Inverse image preserves cokernels. -/
  [pullColimits : PreservesFiniteColimits (pointPull R Y)]
  /-- The ringed adjunction of the actual point functors. -/
  adjunction : pointPull R Y ⊣ pointModules.{u} R.toMon Y
  /-- Its underlying unit is that of the recorded point geometric morphism. -/
  unit : ∀ N : Profinite.CondensedAction.Modules R.toMon,
    (adjunction.unit.app N).hom = (pointAdjunction Y).unit.app N.X
  /-- The corresponding equality for the underlying counit. -/
  counit : ∀ N : Modules R.toMon Y,
    (adjunction.counit.app N).hom = (pointAdjunction Y).counit.app N.X

attribute [instance] PointAdjunctionData.additive PointAdjunctionData.pullAdditive
  PointAdjunctionData.pullLimits PointAdjunctionData.pullColimits

/-- The derived point adjunction uses exact inverse image and ordinary total direct image.
Source: field-action node, counit-adjoint projection
(blueprint: def-sfb-field-action-transport-data). -/
def pointDerivedAdjunction {R : Coefficients.{u}} {Y : Scheme.{u}}
    [d : PointAdjunctionData R Y] :
    (pointPull R Y).mapDerivedCategory ⊣ (pointModules.{u} R.toMon Y).rightDerivedFunctor :=
  d.adjunction.mapDerivedCategoryRightDerivedAdjunction


/-- Additivity of actual coefficient pullback, with its existing preadditive structure.
Source: field-action node, exact geometric pullback
(blueprint: def-sfb-field-action-transport-data). -/
instance coefficientPullAdditive (R : Coefficients.{u}) {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    (CondensedRing.upperStar.{u} R.X f).Additive := CondensedRing.upperStar_additive R.X f

/-- Additivity of actual direct image, using the upstream module structure.
Source: field-action node, ordinary direct image
(blueprint: def-sfb-field-action-transport-data). -/
instance coefficientPushAdditive (R : Coefficients.{u}) {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    (CondensedRing.lowerStar.{u} R.X f).Additive := CondensedRing.lowerStar_additive R.X f


section OrdinaryScalars
variable {R R' : Coefficients.{u}} (φ : R ⟶ R')
  [CategoryTheory.CondensedBar.ActionAbelian R (ks ≃ₐ[k] ks)]
  [CategoryTheory.CondensedBar.ActionAbelian R' (ks ≃ₐ[k] ks)]
  (e : FieldData k ks R) (e' : FieldData k ks R')
  [ForgetData k ks R] [ForgetData k ks R']

/-- Ordinary scalar adjunctions with their field and forgotten presentations, and the
normalized ordinary/derived restriction comparison. All ordinary tensor functors are
fixed by their scalar transposes and by their action on original geometric sections.
Source: field-action node, coefficient-adjunction paragraph
(blueprint: def-sfb-field-action-scalar-transport-data). -/
structure OrdinaryScalarTransport where
  /-- The existing normalized restriction of both scalars and actions. -/
  restriction : CategoryTheory.CondensedBar.ScalarAction φ (ks ≃ₐ[k] ks)
  /-- Restriction is exact, including for nonflat coefficient maps. -/
  [limits : PreservesFiniteLimits restriction.functor]
  /-- Exactness includes cokernels. -/
  [colimits : PreservesFiniteColimits restriction.functor]
  /-- Ordinary extension of scalars with its diagonal action. -/
  extension : CategoryTheory.CondensedBar.Equivariant R (ks ≃ₐ[k] ks) ⥤
    CategoryTheory.CondensedBar.Equivariant R' (ks ≃ₐ[k] ks)
  /-- Extension preserves addition of equivariant maps. -/
  [additive : extension.Additive]
  /-- The scalar tensor adjunction. -/
  adjunction : extension ⊣ restriction.functor
  /-- Forgetting gives the usual condensed scalar adjunction, including transposes. -/
  underlying : AdjunctionSquare adjunction (Mod.extendRestrictAdjunction φ.hom.hom)
    CategoryTheory.CondensedBar.forgetAction CategoryTheory.CondensedBar.forgetAction
  /-- The underlying restriction comparison is the specified one. -/
  underlying_restriction : underlying.restriction = restriction.underlying
  /-- Field transport preserves the ordinary scalar adjunction, units and counits. -/
  ordinary : AdjunctionSquare (Mod.extendRestrictAdjunction (scalarMap φ (Spec (.of k))))
    adjunction (fieldFunctor k ks e) (fieldFunctor k ks e')
  /-- The canonical ordinary and derived field restriction comparisons. -/
  fieldComparison : CoefficientComparison (restrictX φ (Spec (.of k)))
    restriction.functor (fieldFunctor k ks e) (fieldFunctor k ks e')
  /-- Field scalar restriction leaves every geometric section unchanged. -/
  field_sections : ∀ (M : Modules R'.toMon (Spec (.of k))) (P : Profinite.{u})
    (x : Profinite.CondensedAction.sectionModule R.toMon
      ((fieldFunctor k ks e).obj ((restrictX φ (Spec (.of k))).obj M)).module P),
    ((e'.geometric.sections.hom.app M).app (op P)).hom
      (((restriction.underlying.hom.app ((fieldFunctor k ks e').obj M)).hom.hom.app
        (op P)).hom
        ((((fieldComparison.ordinary.hom.app M).val).hom.hom.app (op P)).hom x)) =
      ((e.geometric.sections.hom.app ((restrictX φ (Spec (.of k))).obj M)).app (op P)).hom x
  /-- Ordinary restriction is the same normalized comparison. -/
  ordinary_restriction : ordinary.restriction = fieldComparison.ordinary

attribute [instance] OrdinaryScalarTransport.limits OrdinaryScalarTransport.colimits
  OrdinaryScalarTransport.additive

end OrdinaryScalars

end AlgebraicGeometry.ProEtale.FieldActionTransport
