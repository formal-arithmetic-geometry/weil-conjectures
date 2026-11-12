/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.AlgebraicGeometry.AffineExtensionModelUnit
import WeilConjectures.AlgebraicGeometry.AffinePullbackSectionsModelUnit

/-! # Localization of the affine model comparison

Source: Stacks Project, perfect.tex, Tags 06Z0, 08DV, 08DW and 0AA7.
(blueprint: new-affine-extension-sections-model-factorization).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]

set_option maxHeartbeats 500000 in
set_option profiler true in
-- Affine functor identifications need to unfold the scheme module carrier.
/-- Localization of the normalized underived model comparison computes the derived mate.
Source: Stacks Project, perfect.tex, Tags 06Z0, 08DV, 08DW and 0AA7.
(blueprint: new-affine-extension-sections-model-factorization).
Proof: Tilde is exact and preserves K-flatness. The K-flat M computes derived
extension of scalars, and tilde M computes derived tensor pullback. The ordinary
sections/derived sections comparison is invertible on complexes of associated
sheaves, even when unbounded, by affine acyclicity and truncation. These three
comparison maps give a and b, with the displayed source and target complexes.
More explicitly, write K = tilde M, X = Gamma_R K, and N = P K. Let
s_R : Q(X) -> RGamma_R(Q(K)) and s_B : Q(Gamma_B N) -> RGamma_B(Q(N))
be the invertible sections comparisons, and let e_E and e_P be the left-derived
counits on X and K. After identifying the fixed extension adjoint with the standard
left derived extension by the unit-compatible uniqueness isomorphism, take
 a = (LE(s_R))^{-1} followed by e_E,
 b = RGamma_B(e_P) followed by s_B^{-1}.
Here X is K-flat because the ordinary tilde unit identifies X with M. For the
comparison over B, transport g to Spec of its coordinate ring map using full
faithfulness of Spec, then use the termwise tensor-pullback/tilde isomorphism.
Apply the underived equation hc termwise and pass to the homotopy categories.
The derived extension adjunction is transported from extension/restriction, so its
unit factors through the extension counit on M. The canonical pullback adjunction
has the analogous factorization through its K-flat counit on tilde M. Substitute
these two unit factorizations in the localized equation hc. The equation hr replaces
the localized sections/direct-image comparison by r; naturality of the derived
units moves this comparison past the resolution maps. Cancel the invertible
sections and K-flat comparison maps. This gives precisely the displayed equation.
The zero complex and identity map recover the ordinary adjunction identities;
no boundedness or flatness assumption on g occurs. -/
theorem exists_affineExtensionSections_model_factorization
    {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R)
    (v : RingedSpace.moduleDirectImage g.toLRSHom.toShHom ⋙
        affineGlobalSections (𝟙 (Spec R)) ≅
      affineGlobalSections (𝟙 (Spec B)) ⋙
        ModuleCat.restrictScalars.{u} (affineBaseRingMap g))
    (r : schemeDerivedDirectImage g ⋙ affineDerivedGlobalSections (𝟙 (Spec R)) ≅
      affineDerivedGlobalSections (𝟙 (Spec B)) ⋙
        (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory)
    (hr : ∀ J : HomotopyCategory
        (SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace)) (ComplexShape.up ℤ),
      (Functor.rightDerivedFunctorCompUnit
          (RingedSpace.moduleDirectImage g.toLRSHom.toShHom)
          (affineGlobalSections (𝟙 (Spec R)))).app J ≫
        (affineGlobalSectionsDerivedIso (𝟙 (Spec R))).hom.app
          ((schemeDerivedDirectImage g).obj (DerivedCategory.Qh.obj J)) ≫
        r.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((v.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
        (affineGlobalSections (𝟙 (Spec B)) ⋙
          ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).rightDerivedFunctorUnit.app J ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
            (affineGlobalSections (𝟙 (Spec B)))
            (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)) ≪≫
          Functor.isoWhiskerRight (affineGlobalSectionsDerivedIso (𝟙 (Spec B)))
            (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory).hom.app
          (DerivedCategory.Qh.obj J))
    (c : (@id (ModuleCat.{u} R ⥤
        SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))
        (tilde.functor R)) ⋙ affineGlobalSections (𝟙 (Spec R)) ⋙
        ModuleCat.extendScalars.{u, u, u} (affineBaseRingMap g) ⟶
      (@id (ModuleCat.{u} R ⥤
        SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))
        (tilde.functor R)) ⋙ (@id (SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace))
        (Scheme.Modules.tensorPullback g)) ⋙
        affineGlobalSections (𝟙 (Spec B)))
    (hc : ∀ N : ModuleCat.{u} R,
      (ModuleCat.extendRestrictScalarsAdj (affineBaseRingMap g)).unit.app
          ((affineGlobalSections (𝟙 (Spec R))).obj ((tilde.functor R).obj N)) ≫
        (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).map (c.app N) =
      (affineGlobalSections (𝟙 (Spec R))).map
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app
            ((tilde.functor R).obj N)) ≫
        v.hom.app ((Scheme.Modules.tensorPullback g).obj ((tilde.functor R).obj N)))
    [(@id (ModuleCat.{u} R ⥤
      SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))
        (tilde.functor R)).Additive]
    [(ModuleCat.extendScalars.{u, u, u} (affineBaseRingMap g)).Additive]
    [(@id (SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace))
        (Scheme.Modules.tensorPullback g)).Additive]
    (M : CochainComplex (ModuleCat.{u} R) ℤ)
    (hM : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat M) :
    let T := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} R ⥤
        SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))
        (tilde.functor R)) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
    let Q := DerivedCategory.Q.obj (T.obj M)
    ∃ (a : (affineDerivedExtension g).obj
          ((affineDerivedGlobalSections (𝟙 (Spec R))).obj Q) ≅
        DerivedCategory.Q.obj ((((@id (ModuleCat.{u} R ⥤
        SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))
        (tilde.functor R)) ⋙ affineGlobalSections (𝟙 (Spec R)) ⋙
          ModuleCat.extendScalars.{u, u, u} (affineBaseRingMap g)).mapHomologicalComplex
            (.up ℤ)).obj M))
      (b : (affineDerivedGlobalSections (𝟙 (Spec B))).obj ((derivedPullback g).obj Q) ≅
        DerivedCategory.Q.obj ((((@id (ModuleCat.{u} R ⥤
        SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))
        (tilde.functor R)) ⋙ (@id (SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace))
        (Scheme.Modules.tensorPullback g)) ⋙
          affineGlobalSections (𝟙 (Spec B))).mapHomologicalComplex (.up ℤ)).obj M)),
      (((affineDerivedExtensionAdjunction g).homEquiv _ _).symm
        ((affineDerivedGlobalSections (𝟙 (Spec R))).map
            ((canonicalPullbackAdjunction g).unit.app Q) ≫
          r.hom.app ((derivedPullback g).obj Q))) ≫ b.hom =
        a.hom ≫ DerivedCategory.Q.map ((c.mapHomologicalComplex (.up ℤ)).app M) := by
  dsimp only
  obtain ⟨s, a, hs, ha⟩ := exists_affineExtension_model_unit g M hM
  obtain ⟨b, hb⟩ := exists_affinePullbackSections_model_unit g v r hr M hM s hs
  refine ⟨a, b, ?_⟩
  let T := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (@id (ModuleCat.{u} R ⥤
      SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))
      (tilde.functor R)) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
  let K := T.obj M
  let S := affineGlobalSections (𝟙 (Spec R))
  let E := ModuleCat.extendScalars.{u, u, u} (affineBaseRingMap g)
  let U := ModuleCat.restrictScalars.{u} (affineBaseRingMap g)
  let P : SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace) :=
      Scheme.Modules.tensorPullback g
  have : P.Additive := inferInstanceAs
    ((@id (SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace))
      (Scheme.Modules.tensorPullback g)).Additive)
  let adjP : P ⊣ RingedSpace.moduleDirectImage g.toLRSHom.toShHom :=
    Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  let X := (S.mapHomologicalComplex (.up ℤ)).obj K
  let f := (c.mapHomologicalComplex (.up ℤ)).app M
  have hchain :
      ((ModuleCat.extendRestrictScalarsAdj (affineBaseRingMap g)).mapHomologicalComplex
          (.up ℤ)).unit.app X ≫ (U.mapHomologicalComplex (.up ℤ)).map f =
        (S.mapHomologicalComplex (.up ℤ)).map
            ((adjP.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
          (v.hom.mapHomologicalComplex (.up ℤ)).app
            ((P.mapHomologicalComplex (.up ℤ)).obj K) := by
    ext i : 1
    exact hc (M.X i)
  let Y := ((affineGlobalSections (𝟙 (Spec B))).mapHomologicalComplex (.up ℤ)).obj
    ((P.mapHomologicalComplex (.up ℤ)).obj K)
  let η := ((ModuleCat.extendRestrictScalarsAdj (affineBaseRingMap g)).mapHomologicalComplex
    (.up ℤ)).unit.app X
  have hnat : U.mapDerivedCategoryFactors.inv.app
        ((E.mapHomologicalComplex (.up ℤ)).obj X) ≫
      U.mapDerivedCategory.map (DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((U.mapHomologicalComplex (.up ℤ)).map f) ≫
        U.mapDerivedCategoryFactors.inv.app Y := by
    exact (U.mapDerivedCategoryFactors.inv.naturality f).symm
  have hright : (affineDerivedExtensionAdjunction g).unit.app
      ((affineDerivedGlobalSections (𝟙 (Spec R))).obj (DerivedCategory.Q.obj K)) ≫
      U.mapDerivedCategory.map (a.hom ≫ DerivedCategory.Q.map f) =
      s.hom ≫ DerivedCategory.Q.map
        ((S.mapHomologicalComplex (.up ℤ)).map
            ((adjP.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
          (v.hom.mapHomologicalComplex (.up ℤ)).app
            ((P.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        U.mapDerivedCategoryFactors.inv.app Y := by
    calc
      _ = ((affineDerivedExtensionAdjunction g).unit.app
            ((affineDerivedGlobalSections (𝟙 (Spec R))).obj (DerivedCategory.Q.obj K)) ≫
          U.mapDerivedCategory.map a.hom) ≫
            U.mapDerivedCategory.map (DerivedCategory.Q.map f) := by
        rw [Functor.map_comp, Category.assoc]
      _ = (s.hom ≫ DerivedCategory.Q.map η ≫
          U.mapDerivedCategoryFactors.inv.app
            ((E.mapHomologicalComplex (.up ℤ)).obj X)) ≫
            U.mapDerivedCategory.map (DerivedCategory.Q.map f) :=
        congrArg (fun z ↦ z ≫ U.mapDerivedCategory.map (DerivedCategory.Q.map f)) ha
      _ = s.hom ≫ DerivedCategory.Q.map η ≫
          DerivedCategory.Q.map ((U.mapHomologicalComplex (.up ℤ)).map f) ≫
            U.mapDerivedCategoryFactors.inv.app Y := by
        simp only [Category.assoc]
        exact congrArg (fun z ↦ s.hom ≫ DerivedCategory.Q.map η ≫ z) hnat
      _ = _ := by
        rw [← DerivedCategory.Q.map_comp_assoc]
        exact congrArg (fun z ↦ s.hom ≫ DerivedCategory.Q.map z ≫
          U.mapDerivedCategoryFactors.inv.app Y) hchain
  apply ((affineDerivedExtensionAdjunction g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Adjunction.homEquiv_unit]
  change ((affineDerivedGlobalSections (𝟙 (Spec R))).map
      ((canonicalPullbackAdjunction g).unit.app (DerivedCategory.Q.obj K)) ≫
    r.hom.app ((derivedPullback g).obj (DerivedCategory.Q.obj K))) ≫
    U.mapDerivedCategory.map b.hom =
    (affineDerivedExtensionAdjunction g).unit.app
      ((affineDerivedGlobalSections (𝟙 (Spec R))).obj (DerivedCategory.Q.obj K)) ≫
    U.mapDerivedCategory.map (a.hom ≫ DerivedCategory.Q.map f)
  exact (Category.assoc _ _ _).trans (hb.trans hright.symm)

end AlgebraicGeometry
