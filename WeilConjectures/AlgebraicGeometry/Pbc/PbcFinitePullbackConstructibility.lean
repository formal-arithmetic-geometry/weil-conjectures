/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import all WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
/-! # Constructible finite-coefficient module pullback
Source: preservation proof, step 5; Stacks Tags 09AI and 09AL
(blueprint: lem-weil-pbc-finite-pullback-constructibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry.ProEtale

@[irreducible] private def constantCoefficients {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (adicLisseConstantRing X A) ≅
      adicLisseConstantRing Y A := by
  letI : IsIso (proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
      (CommRingCat.of A)) := proEtaleConstantComparison_isIso g (CommRingCat.of A)
  exact asIso (proEtaleConstantInverseImageMap g CommRingCat.{u + 1} (CommRingCat.of A))

@[irreducible] private def directImageEncoding {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :
    proEtaleRingModuleDirectImage g (adicLisseConstantRing X A) (adicLisseConstantRing Y A)
        (constantCoefficients g A) ⋙ scalarRestriction X A ≅
      scalarRestriction Y A ⋙ ProEtale.lowerStar (ModuleCat.{u + 1} A) g := by
  have adjunct : proEtaleRingDirectImageMap g (adicLisseConstantRing X A)
      (adicLisseConstantRing Y A) (constantCoefficients g A) =
      proEtaleConstantDirectImageMap g CommRingCat.{u + 1} (CommRingCat.of A) := by
    simp only [constantCoefficients, asIso_hom, proEtaleRingDirectImageMap]
    change (proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _
      ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _ |>.symm
        (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} (CommRingCat.of A))) = _
    exact (proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _ |>.apply_symm_apply _
  have sections : toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A)) ≫
      (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} (CommRingCat.of A)).hom =
    Functor.whiskerLeft (proEtaleBaseChange g).op
      (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of A))) :=
    ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
      _ _).apply_symm_apply _
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ?_) ?_)) ?_
  · let P := (((proEtaleRingModuleDirectImage g (adicLisseConstantRing X A)
      (adicLisseConstantRing Y A) (constantCoefficients g A) ⋙
        scalarRestriction X A).obj M).obj.obj U)
    let Q := (((scalarRestriction Y A ⋙
      ProEtale.lowerStar (ModuleCat.{u + 1} A) g).obj M).obj.obj U)
    change P ≅ Q
    refine (show (P : Type (u + 1)) ≃ₗ[A] Q from
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun a m ↦ ?_ }).toModuleIso
    change ((proEtaleRingDirectImageMap g (adicLisseConstantRing X A)
      (adicLisseConstantRing Y A) (constantCoefficients g A)).hom.app U).hom
      (((adicLisseConstantUnit X A).app U).hom a) •
        (show M.val.obj ((proEtaleBaseChange g).op.obj U) from m) =
      (((adicLisseConstantUnit Y A).app ((proEtaleBaseChange g).op.obj U)).hom a) •
        (show M.val.obj ((proEtaleBaseChange g).op.obj U) from m)
    rw [adjunct]
    exact congrArg (fun r ↦ r •
      (show M.val.obj ((proEtaleBaseChange g).op.obj U) from m))
      (ConcreteCategory.congr_hom (congr_app sections U) a)
  · intro U V a
    ext m
    rfl
  · intro M N a
    ext U m
    rfl

@[irreducible] private def pullbackEncoding {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :
    proEtaleRingModulePullback g (adicLisseConstantRing X A) (adicLisseConstantRing Y A)
        (constantCoefficients g A) ⋙ scalarRestriction Y A ≅
      scalarRestriction X A ⋙ ProEtale.upperStar (ModuleCat.{u + 1} A) g := by
  let EX := (scalarRestriction X A).asEquivalence
  let EY := (scalarRestriction Y A).asEquivalence
  let L := ProEtale.upperStar (ModuleCat.{u + 1} A) g
  let R := ProEtale.lowerStar (ModuleCat.{u + 1} A) g
  let adj := EX.toAdjunction.comp
    ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
      EY.symm.toAdjunction)
  let eR : EY.functor ⋙ R ⋙ EX.inverse ≅
      proEtaleRingModuleDirectImage g (adicLisseConstantRing X A) (adicLisseConstantRing Y A)
        (constantCoefficients g A) :=
    (Functor.isoWhiskerRight (directImageEncoding g A).symm EX.inverse) ≪≫
      Functor.isoWhiskerLeft _ EX.unitIso.symm
  let e := (proEtaleRingModuleAdjunction g (adicLisseConstantRing X A)
    (adicLisseConstantRing Y A) (constantCoefficients g A)).leftAdjointUniq
      (adj.ofNatIsoRight eR)
  exact Functor.isoWhiskerRight e EY.functor ≪≫
    Functor.associator EX.functor (L ⋙ EY.inverse) EY.functor ≪≫
    Functor.isoWhiskerLeft EX.functor
      (Functor.associator L EY.inverse EY.functor ≪≫
        Functor.isoWhiskerLeft L EY.counitIso ≪≫ Functor.rightUnitor L)

@[irreducible] private def relativeEncoding {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] :
    proEtaleModuleInverseImage g (adicLisseConstantRing X A) ⋙ relativeRestriction g A ≅
      scalarRestriction X A ⋙ ProEtale.upperStar (ModuleCat.{u + 1} A) g := by
  let c := constantCoefficients g A
  let E := proEtaleScalarEquivalence Y ((adicLisseForget Y).mapIso c)
  let e := (proEtaleRingExtensionAdjunction g (adicLisseConstantRing X A)
    (adicLisseConstantRing Y A) c).leftAdjointUniq E.symm.toAdjunction
  let er : relativeRestriction g A ≅ E.inverse ⋙ scalarRestriction Y A := Iso.refl _
  let ep : proEtaleModuleInverseImage g (adicLisseConstantRing X A) ⋙ E.inverse ≅
      proEtaleRingModulePullback g (adicLisseConstantRing X A)
        (adicLisseConstantRing Y A) c :=
    Functor.isoWhiskerLeft _ e.symm
  exact Functor.isoWhiskerLeft _ er ≪≫
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ep _ ≪≫ pullbackEncoding g A

@[irreducible] private def scalarConstant (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (M : ModuleCat.{u + 1} A) :
    (scalarRestriction X A).obj ((adicLisseConstantModules X A).obj M) ≅
      (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} A)).obj M :=
  letI := ConstantScalarComparison.constantComparisonHom_isIso (ProEt.topology X) A
    (adicLisseRing X A) (adicLisseConstantUnit X A) M
  (asIso (ConstantScalarComparison.constantComparisonHom (ProEt.topology X) A
    (adicLisseRing X A) (adicLisseConstantUnit X A) M)).symm

@[irreducible] private def relativeConstant {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A : Type (u + 1)) [CommRing A] (M : ModuleCat.{u + 1} A) :
    (relativeRestriction g A).obj
      ((proEtaleModuleInverseImage g (adicLisseConstantRing X A)).obj
        ((adicLisseConstantModules X A).obj M)) ≅
      (constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)).obj M :=
  (relativeEncoding g A).app _ ≪≫
    (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapIso (scalarConstant X A M) ≪≫
      ((((constantSheafΓAdj _ (ModuleCat.{u + 1} A)).comp
        (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)).ofNatIsoRight
          (ProEtale.globalSectionsLowerStarIso (ModuleCat.{u + 1} A) g)).leftAdjointUniq
            (constantSheafΓAdj _ (ModuleCat.{u + 1} A))).app M

@[irreducible] private def scalarOverIso (Y : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (R : Sheaf (ProEt.topology Y) RingCat.{u + 1})
    (a : (Functor.const Y.ProEtᵒᵖ).obj (RingCat.of A) ⟶ R.obj)
    (V : Y.ProEt) (F : SheafOfModules.{u + 1} R) :
    ((ConstantScalarComparison.restriction (ProEt.topology Y) A R a).obj F).over V ≅
      (ConstantScalarComparison.restriction ((ProEt.topology Y).over V) A (R.over V)
        (Functor.whiskerLeft (Over.forget V).op a)).obj (F.over V) := Iso.refl _

@[irreducible] private def levelPullbackEncoding {S T : Scheme.{u}} (g : S ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    pbcRestrict (pbcLevelConstantComparison T d n).hom ⋙
      proEtaleRingModulePullback g (adicLisseConstantRing T (A ⧸ d.ideal ^ (n + 1)))
        (adicLisseConstantRing S (A ⧸ d.ideal ^ (n + 1)))
        (constantCoefficients g (A ⧸ d.ideal ^ (n + 1))) ≅
      proEtaleRingModulePullback g ((pbcAdicRings T d).obj (op n))
        ((pbcAdicRings S d).obj (op n)) (asIso (completedFiniteCoefficientMap g d n)) ⋙
          pbcRestrict (pbcLevelConstantComparison S d n).hom := by
  have hc : (constantCoefficients g (A ⧸ d.ideal ^ (n + 1))).hom ≫
      (pbcLevelConstantComparison S d n).hom =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (pbcLevelConstantComparison T d n).hom ≫ completedFiniteCoefficientMap g d n := by
    simp only [constantCoefficients, asIso_hom, completedFiniteCoefficientMap,
      ← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
    have hmap : ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (𝟙 (adicLisseConstantRing T (A ⧸ d.ideal ^ (n + 1))))) =
        𝟙 _ := (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map_id _
    rw [hmap, Category.id_comp]
  have := proEtaleRingRestrictionPullbackInv_isIso g _ _ _ _
    (pbcLevelConstantComparison T d n).hom (pbcLevelConstantComparison S d n).hom
      (constantCoefficients g (A ⧸ d.ideal ^ (n + 1)))
      (asIso (completedFiniteCoefficientMap g d n)) hc
  exact asIso (proEtaleRingRestrictionPullbackInv g _ _ _ _
    (pbcLevelConstantComparison T d n).hom (pbcLevelConstantComparison S d n).hom
      (constantCoefficients g (A ⧸ d.ideal ^ (n + 1)))
      (asIso (completedFiniteCoefficientMap g d n)) hc)

end AlgebraicGeometry.Scheme
