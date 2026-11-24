/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.HomTensorTotal
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.RingedHomRestrictionComposition
import WeilConjectures.Algebra.Homology.RingedHomRestrictionOrdinary
import WeilConjectures.Algebra.Homology.RingedInternalHomContravariantExact
import WeilConjectures.Algebra.Homology.RingedInternalHomCovariantExact
import WeilConjectures.CategoryTheory.SiteRelocalizationKInjective

/-!
# Internal derived Hom calculus on small ringed sites

The tensor functor is specified by its natural total-tensor comparison on K-flat
representatives. Restriction uses Mathlib's slice functors and their induced functors
on unbounded derived categories. The opposite triangulated structure reverses shifts.

## References

* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 08JC](https://stacks.math.columbia.edu/tag/08JC)
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

private theorem ringedSite_pushforward_limits
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {G : C ⥤ D} [Functor.IsContinuous G J K]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ) := by
  let T := SheafOfModules.forget.{u} S ⋙ PresheafOfModules.toPresheaf S.obj
  have : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ ⋙ T) := by
    change PreservesFiniteLimits
      ((SheafOfModules.forget.{u} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringLeft _ _ _).obj G.op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ T

private theorem ringedSite_pushforward_colimits
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {G : C ⥤ D} [Functor.IsContinuous G J K] [G.IsCocontinuous J K]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ) := by
  let H := G.sheafPushforwardContinuous AddCommGrpCat.{u} J K
  have : PreservesColimitsOfSize.{u, u} H :=
    (G.sheafAdjunctionCocontinuous AddCommGrpCat.{u} J K).leftAdjoint_preservesColimits
  let T := SheafOfModules.toSheaf.{u} S
  have : PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ ⋙ T) := by
    change PreservesFiniteColimits (SheafOfModules.toSheaf.{u} R ⋙ H)
    infer_instance
  have : ReflectsFiniteColimits T :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact preservesFiniteColimits_of_reflects_of_preserves _ T

/-- The overFunctor slice restriction is additive. -/
@[instance]
theorem ringedSite_overFunctor_additive
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) (U :
    C) : (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R) U).Additive := by
  constructor
  intro X Y f g
  ext V x
  rfl

/-- The overFunctor slice restriction preserves finite limits. -/
@[instance]
theorem ringedSite_overFunctor_limits
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) (U :
    C) : PreservesFiniteLimits (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U) := by
  exact ringedSite_pushforward_limits (𝟙 _)

/-- The overFunctor slice restriction preserves finite colimits. -/
@[instance]
theorem ringedSite_overFunctor_colimits
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) (U :
    C) : PreservesFiniteColimits (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U) := by
  exact ringedSite_pushforward_colimits (𝟙 _)

/-- The overMap slice restriction is additive. -/
@[instance]
theorem ringedSite_overMap_additive
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) {U V
    : C} (f : V ⟶ U) : (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R) f).Additive := by
  constructor
  intro X Y f g
  ext V x
  rfl

/-- The overMap slice restriction preserves finite limits. -/
@[instance]
theorem ringedSite_overMap_limits
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) {U V
    : C} (f : V ⟶ U) : PreservesFiniteLimits (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) f) := by
  exact ringedSite_pushforward_limits (Sheaf.pushforwardOverMapIso _ f).inv

/-- The overMap slice restriction preserves finite colimits. -/
@[instance]
theorem ringedSite_overMap_colimits
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) {U V
    : C} (f : V ⟶ U) : PreservesFiniteColimits (SheafOfModules.overMap.{u} ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R) f) := by
  exact ringedSite_pushforward_colimits (Sheaf.pushforwardOverMapIso _ f).inv

attribute [local irreducible] derivedInternalHom homComplexFunctor

local instance {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [h : ∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over U))] (U : C) :
    HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U))) :=
  h U

/-- Derived internal Hom commutes naturally with slice restriction, compatibly
with successive restrictions. The comparison for V to U, followed by transport
along the canonical derived overFunctorMap, equals direct restriction to V. -/
theorem ringedInternalHom_restriction
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))] [hDCU : ∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
    (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over U))] :
    ∃ (e : ∀ U : C, (derivedInternalHom.{u, w} J R) ⋙ (SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).mapDerivedCategory ≅
    ((SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
    R) U).mapDerivedCategory.op.prod (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U).mapDerivedCategory) ⋙ (@derivedInternalHom.{u, w}
    (Over U) inferInstance (J.over U) (R.over U) (hDCU U)))
    (s : ∀ (U V : C) (f : V ⟶ U), (@derivedInternalHom.{u, w} (Over U) inferInstance (J.over U)
    (R.over U) (hDCU U)) ⋙ (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R) f).mapDerivedCategory ≅
    ((SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    f).mapDerivedCategory.op.prod (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) f).mapDerivedCategory) ⋙ (@derivedInternalHom.{u, w}
    (Over V) inferInstance (J.over V) (R.over V) (hDCU V))),
    ∀ (U V : C) (f : V ⟶ U) (L M : (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))),
    (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    f).mapDerivedCategory.map ((e U).hom.app (op L, M)) ≫
    (s U V f).hom.app (op ((SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U).mapDerivedCategory.obj L),
    (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    U).mapDerivedCategory.obj M) ≫
    (@derivedInternalHom.{u, w} (Over V) inferInstance (J.over V) (R.over V) (hDCU V)).map
    (X := (op ((SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R) f).mapDerivedCategory.obj ((SheafOfModules.overFunctor.{u} ((sheafCompose
    J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).mapDerivedCategory.obj L)),
    (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    f).mapDerivedCategory.obj ((SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U).mapDerivedCategory.obj M)))
    (Y := (op ((SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R) V).mapDerivedCategory.obj L), (SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) V).mapDerivedCategory.obj M))
    (((((Functor.mapDerivedCategoryCompIso (SheafOfModules.overFunctor.{u} ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U) (SheafOfModules.overMap.{u} ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R) f)) ≪≫ Functor.mapDerivedCategoryNatIso
    (SheafOfModules.overFunctorMap ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    f))).inv.app L).op, (((Functor.mapDerivedCategoryCompIso (SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U) (SheafOfModules.overMap.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) f)) ≪≫
    Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) f))).hom.app M) =
    (((Functor.mapDerivedCategoryCompIso (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U) (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) f)) ≪≫ Functor.mapDerivedCategoryNatIso
    (SheafOfModules.overFunctorMap ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    f))).hom.app ((derivedInternalHom.{u, w} J R).obj (op L, M)) ≫
    (e V).hom.app (op L, M) := by
  set_option backward.isDefEq.respectTransparency true in
    classical
    let F (U : C) : RingedHomRestriction.Modules R ⥤
        RingedHomRestriction.Modules (R.over U) :=
      SheafOfModules.overFunctor.{u} (RingedHomRestriction.Rings R) U
    let G (U V : C) (f : V ⟶ U) : RingedHomRestriction.Modules (R.over U) ⥤
        RingedHomRestriction.Modules (R.over V) :=
      SheafOfModules.overMap.{u} (RingedHomRestriction.Rings R) f
    let (U : C) : HasDerivedCategory.{w} (RingedHomRestriction.Modules (R.over U)) := hDCU U
    let (U : C) : (F U).Additive :=
      ringedSite_overFunctor_additive J R U
    let (U V : C) (f : V ⟶ U) :
        (G U V f).Additive :=
      ringedSite_overMap_additive J R f
    let (U : C) : PreservesFiniteLimits
        (F U) :=
      ringedSite_overFunctor_limits J R U
    let (U : C) : PreservesFiniteColimits
        (F U) :=
      ringedSite_overFunctor_colimits J R U
    let (U V : C) (f : V ⟶ U) : PreservesFiniteLimits
        (G U V f) :=
      ringedSite_overMap_limits J R f
    let (U V : C) (f : V ⟶ U) : PreservesFiniteColimits
        (G U V f) :=
      ringedSite_overMap_colimits J R f
    obtain ⟨a, b, hab⟩ := RingedHomRestriction.ordinary_comparisons J R
    have hk (U : C) (I : RingedHomRestriction.Complex R) (hI : I.IsKInjective) :
        CochainComplex.IsKInjective
          ((Functor.mapHomologicalComplex
            (F U) (.up ℤ)).obj I) := by
      exact isKInjective_restrict_localized (RingedHomRestriction.Rings R) U inferInstance I
    have hs (U V : C) (f : V ⟶ U)
        (I : RingedHomRestriction.Complex (R.over U)) (hI : I.IsKInjective) :
        CochainComplex.IsKInjective
          ((Functor.mapHomologicalComplex
            (G U V f) (.up ℤ)).obj I) := by
      let : (G U V f).PreservesKInjectiveComplexes :=
        SheafOfModules.overMap_preservesKInjectiveComplexes_ofUniverses.{u, u, u}
          (RingedHomRestriction.Rings R) f
      exact Functor.PreservesKInjectiveComplexes.isKInjective_map I
    have he (U : C) := RingedHomRestriction.comparison_exists R (R.over U)
      (F U) (hk U) (a U)
    choose e he using he
    have hs' (U V : C) (f : V ⟶ U) :=
      RingedHomRestriction.comparison_exists (R.over U) (R.over V)
        (G U V f) (hs U V f) (b U V f)
    choose s hs' using hs'
    refine ⟨e, s, ?_⟩
    intro U V f
    let c : F U ⋙ G U V f ≅ F V :=
      SheafOfModules.overFunctorMap (RingedHomRestriction.Rings R) f
    have hn := RingedHomRestriction.composite_normalized R (R.over U) (R.over V)
      (F U) (G U V f) (F V) c (hk U) (a U) (b U V f) (e U) (s U V f) (he U) (hs' U V f)
    have hc : RingedHomRestriction.composite
        (Functor.mapHomologicalComplexCompIso c (.up ℤ)) (a U) (b U V f) = a V :=
      (RingedHomRestriction.compatible_iff _ _ _ _ _ _ _ _ _ _).mp (hab U V f)
    rw [hc] at hn
    have h := RingedHomRestriction.comparison_unique R (R.over V) (F V) (a V)
      _ (e V) hn (he V)
    exact (RingedHomRestriction.compatible_iff _ _ _ _ _ _ _ _ _ _).mpr h

/-- Internal derived Hom preserves distinguished triangles in each variable
and commutes with shifts. The first variable is a functor from the opposite
triangulated category, whose shift by m is the original shift by -m. -/
theorem ringedInternalHom_exact
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))] :
    (∀ L : (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))), ∃ _ : ((Functor.curry.obj (derivedInternalHom.{u, w} J R)).obj (op
    L)).CommShift ℤ,
    ((Functor.curry.obj (derivedInternalHom.{u, w} J R)).obj (op L)).IsTriangulated) ∧
    (∀ M : (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))), ∃ _ : ((Functor.curry.obj (derivedInternalHom.{u, w} J R)).flip.obj
    M).CommShift ℤ,
    ((Functor.curry.obj (derivedInternalHom.{u, w} J R)).flip.obj M).IsTriangulated) := by
  exact ⟨ringedInternalHom_covariant_exact J R, ringedInternalHom_contravariant_exact J R⟩

end CategoryTheory
