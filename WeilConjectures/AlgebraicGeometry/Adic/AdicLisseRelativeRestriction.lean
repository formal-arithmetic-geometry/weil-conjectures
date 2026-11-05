/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicLisseModuleSupplement

import all WeilConjectures.AlgebraicGeometry.Pbc.PbcFinitePullbackConstructibility
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement

/-! # Restriction of adic-lisse modules to inverse-image coefficients

Source: Stacks Project, proetale.tex, Tag 09BT, clause (3), and
sites.tex, Tag 00YV (functoriality of algebraic structures in topoi).
(blueprint: lem-weil-pbc-adic-lisse-relative-restriction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

@[irreducible] private noncomputable def constantEncodingNatIso (Z : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] :
    constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} A) ≅
      adicLisseConstantModules Z A ⋙ scalarRestriction Z A := by
  let J := ProEt.topology Z
  let R := adicLisseRing Z A
  let a := adicLisseConstantUnit Z A
  let f (M : ModuleCat.{u + 1} A) :=
    ConstantScalarComparison.constantComparisonHom J A R a M
  have hf (M : ModuleCat.{u + 1} A) : IsIso (f M) :=
    ConstantScalarComparison.constantComparisonHom_isIso J A R a M
  refine NatIso.ofComponents (fun M ↦ asIso (f M)) ?_
  intro M N g
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ ((scalarRestriction Z A).obj
    ((adicLisseConstantModules Z A).obj N)).property
  have hfac (M : ModuleCat.{u + 1} A) :
      toSheafify J ((Functor.const Z.ProEtᵒᵖ).obj M) ≫ (f M).hom =
        { app := fun U ↦ ((PresheafOfModules.sheafificationAdjunction a).unit.app
            (ConstantScalarComparison.constantPresheaf A M)).app U
          naturality := by
            intro U V b
            ext x
            exact ConcreteCategory.congr_hom
              (((PresheafOfModules.sheafificationAdjunction a).unit.app
                (ConstantScalarComparison.constantPresheaf A M)).naturality b) x } :=
    ((sheafificationAdjunction J (ModuleCat.{u + 1} A)).homEquiv _ _).apply_symm_apply _
  change toSheafify J _ ≫ (sheafifyMap J ((Functor.const Z.ProEtᵒᵖ).map g) ≫
      (f N).hom) = toSheafify J _ ≫ ((f M).hom ≫ _)
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc, hfac,
    ← Category.assoc, hfac]
  ext U x
  let φ : ConstantScalarComparison.constantPresheaf (C := Z.ProEt) A M ⟶
      ConstantScalarComparison.constantPresheaf (C := Z.ProEt) A N :=
    { app := fun _ ↦ g
      naturality := by intros; ext x; rfl }
  exact ConcreteCategory.congr_hom
    (congrArg (fun t ↦ t.app U)
      ((PresheafOfModules.sheafificationAdjunction a).unit.naturality φ)) x

@[irreducible] private noncomputable def concreteConstantModuleComparison
    {X Y : Scheme.{u}} (h : Y ⟶ X) (A : Type (u + 1)) [CommRing A] :
    adicLisseConstantModules X A ⋙
        proEtaleModuleInverseImage h (adicLisseConstantRing X A) ≅
      adicLisseConstantModules Y A ⋙ SheafOfModules.restrictScalars
        ((adicLisseForget Y).map (constantCoefficients h A).hom) := by
  let c := constantCoefficients h A
  let E := proEtaleScalarEquivalence Y ((adicLisseForget Y).mapIso c)
  let CX := adicLisseConstantModules X A
  let CY := adicLisseConstantModules Y A
  let L := proEtaleModuleInverseImage h (adicLisseConstantRing X A)
  let EY := scalarRestriction Y A
  let B := ProEtale.upperStar (ModuleCat.{u + 1} A) h
  let k : constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} A) ⋙ B ≅
      constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} A) :=
    (((constantSheafΓAdj _ (ModuleCat.{u + 1} A)).comp
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h)).ofNatIsoRight
        (ProEtale.globalSectionsLowerStarIso (ModuleCat.{u + 1} A) h)).leftAdjointUniq
          (constantSheafΓAdj _ (ModuleCat.{u + 1} A))
  let q : CX ⋙ L ⋙ E.inverse ⋙ EY ≅ CY ⋙ EY :=
    Functor.isoWhiskerLeft CX (relativeEncoding h A) ≪≫
      Functor.isoWhiskerRight (constantEncodingNatIso X A).symm B ≪≫
      k ≪≫ constantEncodingNatIso Y A
  let q' : CX ⋙ L ⋙ E.inverse ≅ CY := Functor.fullyFaithfulCancelRight EY q
  exact Functor.isoWhiskerLeft (CX ⋙ L) E.counitIso.symm ≪≫
    Functor.isoWhiskerRight q' E.functor

@[irreducible] private noncomputable def concreteModuleSystemComparison
    {X Y : Scheme.{u}} (h : Y ⟶ X) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (N : ModuleCat.{u + 1} A) :
    adicLisseModuleSystem X I N ⋙
        proEtaleModuleInverseImage h (adicLisseConstantRing X A) ≅
      adicLisseModuleSystem Y I N ⋙ SheafOfModules.restrictScalars
        ((adicLisseForget Y).map (constantCoefficients h A).hom) := by
  let e := concreteConstantModuleComparison h A
  let η : adicLisseModuleSystem X I N ⋙
        proEtaleModuleInverseImage h (adicLisseConstantRing X A) ⟶
      adicLisseModuleSystem Y I N ⋙ SheafOfModules.restrictScalars
        ((adicLisseForget Y).map (constantCoefficients h A).hom) :=
    NatTrans.ofOpSequence (fun n ↦ e.hom.app
      (ModuleCat.of A (N ⧸ (I ^ (n + 1) • ⊤ : Submodule A N)))) (by
        intro n
        simpa only [Functor.comp_map, adicLisseModuleSystem,
          Functor.ofOpSequence_map_homOfLE_succ] using
          e.hom.naturality (ModuleCat.ofHom (Submodule.factorPowSucc I N (n + 1))))
  have (n : ℕᵒᵖ) : IsIso (η.app n) :=
    inferInstanceAs (IsIso (e.hom.app
      (ModuleCat.of A (N ⧸ (I ^ (n.unop + 1) • ⊤ : Submodule A N)))))
  have : IsIso η := NatIso.isIso_of_isIso_app η
  exact asIso η

end AlgebraicGeometry.Scheme
