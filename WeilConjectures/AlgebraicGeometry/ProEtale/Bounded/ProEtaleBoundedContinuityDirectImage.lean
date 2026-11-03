/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedComplexDirectImagePresheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedContinuitySections
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Constructions.Filtered

/-!
# Bounded-below filtered-colimit continuity of pro-etale direct images

Source: Weil conjectures blueprint, snapshot main-20261015,
sec-proetale-coefficients/sk-cor-pe-bounded-continuity,
`det-pe-bounded-continuity-direct-image.md` (blueprint:
`det-pe-bounded-continuity-direct-image`).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- The module direct image over the direct-image coefficient sheaf.
Source: the Weil conjectures blueprint, `det-pe-bounded-continuity-direct-image`
(blueprint: det-pe-bounded-continuity-direct-image). -/
noncomputable def ringModuleDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    SheafOfModules.{u + 1} R ⥤
      SheafOfModules.{u + 1} ((proEtaleSheafDirectImage f RingCat.{u + 1}).obj R) :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := topology Y) (K := topology X)
    (S := (proEtaleSheafDirectImage f RingCat.{u + 1}).obj R)
    (R := R) (𝟙 _)

/-- K-injective resolutions exist for sheaves of modules over the pro-etale ringed site.
Source: Stacks Project, Section 07A5 and Theorem 079P
(blueprint: det-pe-bounded-continuity-direct-image).
Proof: transport the site to `proEtaleSiteModel X`, which only enlarges the Hom universe.
There `SheafOfModules.isGrothendieckAbelian` applies to the transported ring sheaf, so
`CochainComplex.kInjectiveResolutionFunctor` gives K-injective quasi-isomorphic
resolutions. Transport back along the inverse sectionwise equivalence, which preserves
acyclicity, homotopies and quasi-isomorphisms. No commutativity, boundedness or
finiteness condition is imposed. -/
theorem ringModuleDirectImage_hasKInjectiveResolutions {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    ∀ L : CochainComplex (SheafOfModules.{u + 1} R) ℤ,
      ∃ (I : CochainComplex (SheafOfModules.{u + 1} R) ℤ) (s : L ⟶ I),
        I.IsKInjective ∧ QuasiIso s := by
  exact boundedRingModuleDirectImage_hasKInjectiveResolutions R

/-- Modules over the tensor unit are abelian sheaves, with their original sections. -/
private theorem abelianSheaf_module_presentation (X : Scheme.{u}) :
    ∃ R : Sheaf (topology X) RingCat.{u + 1},
      (SheafOfModules.toSheaf.{u + 1} R).IsEquivalence := by
  classical
  let A := Sheaf (topology X) AddCommGrpCat.{u + 1}
  let T := (𝟙_ A)
  have ha (M : Mod A T) : @Mod.act A _ _ T _ M.X M.mod =
      (CategoryTheory.MonoidalCategory.leftUnitor M.X).hom := by
    have h := @Mod.one_act A _ _ T _ M.X M.mod
    change (𝟙 T) ▷ M.X ≫ @Mod.act A _ _ T _ M.X M.mod =
      (CategoryTheory.MonoidalCategory.leftUnitor M.X).hom at h
    simpa only [CategoryTheory.MonoidalCategory.id_whiskerRight,
      Category.id_comp] using h
  let Q : Mod A T ⥤ A := Mod.forget T
  let ff : Q.FullyFaithful :=
    { preimage := fun {M N} f ↦ by
        change M.X ⟶ N.X at f
        exact Mod.homMk (M := M) (N := N) f (by
          exact (congrArg (fun k ↦ k ≫ f) (ha M)).trans
            ((CategoryTheory.MonoidalCategory.leftUnitor_naturality f).symm.trans
              (congrArg (fun k ↦ T ◁ f ≫ k) (ha N).symm)))
      map_preimage := fun _ ↦ rfl
      preimage_map := fun _ ↦ rfl }
  let : Q.Full := ff.full
  let : Q.Faithful := ff.faithful
  let : Q.EssSurj := ⟨fun M ↦ ⟨(Mod.free T).obj M,
    ⟨CategoryTheory.MonoidalCategory.leftUnitor M⟩⟩⟩
  let : Q.IsEquivalence := {}
  let E := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (topology X) T
  let R : Sheaf (topology X) RingCat.{u + 1} :=
    (sheafCompose (topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (topology X) T)
  refine ⟨R, ?_⟩
  have : (E.functor ⋙ SheafOfModules.toSheaf.{u + 1} R).IsEquivalence := by
    change Q.IsEquivalence
    infer_instance
  exact Functor.isEquivalence_of_comp_left E.functor _

private noncomputable def ordinaryDerivedComparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s) :
    F.rightDerivedFunctorOfQuasiIsoResolutions h ≅ F.rightDerivedFunctor := by
  exact Exists.choose (ExistsUnique.exists
    (F.rightDerivedFunctorOfQuasiIsoResolutions_unique h
      F.rightDerivedFunctor F.rightDerivedFunctorUnit (by
        intro H
        constructor
        · intro a b hab
          exact Functor.rightDerived_ext _ _
            (HomotopyCategory.quasiIso C (.up ℤ)) H a b hab
        · intro β
          exact ⟨Functor.rightDerivedDesc _ _
            (HomotopyCategory.quasiIso C (.up ℤ)) H β,
            Functor.rightDerived_fac _ _ _ _ _⟩)))

private noncomputable def ordinaryDerivedSingleComparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    [Abelian.HasKInjectiveResolutions C] (F : C ⥤ D) [F.Additive] (q : ℕ) :
    DerivedCategory.singleFunctor C 0 ⋙ F.rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor D (q : ℤ) ≅ F.rightDerived q :=
  Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0)
    (Functor.isoWhiskerRight F.rightDerivedFunctorPlusCompatibility.symm
      (DerivedCategory.homologyFunctor D (q : ℤ))) ≪≫
    F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q

end AlgebraicGeometry.Scheme.ProEt
