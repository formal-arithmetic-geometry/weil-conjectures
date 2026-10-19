/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.AlgebraicGeometry.FiniteSheafHomAffine
import Sheaf.Algebra.Homology.DerivedInternalHomSingleComparison
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Adjunction.Additive
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-! # The affine derived sheaf-Hom adjunction

Source: Stacks Project, Duality for Schemes, Tags 0BV0, 0BUZ and 0AX3
(blueprint: lem-sc-finite-sheafhom-affine-adjoint).
-/

@[expose] public section

universe u w wA

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
-- The localization comparisons require unfolding several sheaf carrier encodings.
/-- Restriction along `O_X → A = f_* O_Y` (the ring sheaf of the landed
`directImageAlgebraSpace f`) has right adjoint the derived sheaf-Hom out of `A`:
there are an underived right adjoint `H` of restriction, valued in `A`-modules, whose
underlying `O_X`-module functor is `homObj A (-)` and whose counit is evaluation at
`1 ∈ A`; a right derived functor `R : D(O_X) ⥤ D(A)` of `H` (with its comparison `β`);
the derived restriction `L` (with its comparison `t`); and an adjunction `L ⊣ R` whose
`O_X`-module right adjoint `R ⋙ L` is `RHom_{O_X}(A, -)` and whose counit is the
morphism induced by the underived evaluation counit (`Adjunction.derivedε_fac_app`).

Source: Stacks Project, Duality for Schemes, Tags 0BV0, 0BUZ and 0AX3
(blueprint: lem-sc-finite-sheafhom-affine-adjoint).

Proof:
1. Use the underived affine sheaf-Hom adjunction of lem-sc-finite-sheafhom-affine.
   Its underlying O_X-module is homObj(A,F), with A acting by precomposition with
   multiplication. The underived counit evaluates a local homomorphism at one.
2. Restriction of scalars is exact, hence its termwise functor descends through Q to an
   absolute left derived functor `L`. The right derived functor `R` of `H` is computed on
   K-injective resolutions; it is absolute, and `R ⋙ L` computes `RHom_{O_X}(A, -)`
   (def-pur-derived-internal-hom). Apply lem-sc-derived-adjunction-from-underived.
3. The counit clause of lem-sc-derived-adjunction-from-underived (Mathlib
   `Adjunction.derivedε_fac_app`) identifies the derived counit with the morphism induced
   by the underived counit, i.e. by evaluation at one. -/
theorem exists_affine_derivedSheafHom_adjunction
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA}
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))] :
    ∃ (H : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))
      (_ : H.Additive)
      (iH : H ⋙ SheafOfModules.restrictScalars
          (R := moduleRings X.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩ ≅
        (SheafOfModules.homFunctor X.sheaf).obj
          (op ((SheafOfModules.restrictScalars
            (R := moduleRings X.toRingedSpace)
            (R' := moduleRings (directImageAlgebraSpace f))
            ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).obj
              (SheafOfModules.unit (moduleRings (directImageAlgebraSpace f))))))
      (adj₀ : SheafOfModules.restrictScalars
          (R := moduleRings X.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩ ⊣ H),
      (∀ (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (U : X.Opens)
          (φ : (H.obj F).val.obj (op U)),
        ((adj₀.counit.app F).val.app (op U)).hom φ =
          ((((iH.hom.app F).val.app (op U)).hom φ).app (op (Over.mk (𝟙 U)))).hom
            (1 : (moduleRings (directImageAlgebraSpace f)).obj.obj (op U))) ∧
      ∃ (R : schemeDerivedCategory X ⥤
          DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))))
        (β : H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
        (L : DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))) ⥤
          schemeDerivedCategory X)
        (t : DerivedCategory.Q ⋙ L ≅
          (SheafOfModules.restrictScalars
            (R := moduleRings X.toRingedSpace)
            (R' := moduleRings (directImageAlgebraSpace f))
            ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).mapHomologicalComplex
              (.up ℤ) ⋙ DerivedCategory.Q)
        (adj : L ⊣ R),
        R.IsRightDerivedFunctor β (HomologicalComplex.quasiIso _ (.up ℤ)) ∧
        (R ⋙ L).IsRightDerivedFunctor (Functor.whiskerRight β L ≫ (Functor.associator _ _ _).hom)
          (HomologicalComplex.quasiIso _ (.up ℤ)) ∧
        Nonempty (R ⋙ L ≅ (Functor.curry.obj
          (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf)).obj
            (op ((DerivedCategory.singleFunctor _ 0).obj
              ((SheafOfModules.restrictScalars
                (R := moduleRings X.toRingedSpace)
                (R' := moduleRings (directImageAlgebraSpace f))
                ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).obj
                  (SheafOfModules.unit (moduleRings (directImageAlgebraSpace f))))))) ∧
        ∀ K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
          L.map (β.app K) ≫ adj.counit.app (DerivedCategory.Q.obj K) =
            t.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) ≫
              DerivedCategory.Q.map
                ((NatTrans.mapHomologicalComplex adj₀.counit (.up ℤ)).app K) := by
  classical
  obtain ⟨H, iH, adj₀, haction, hc, hlocal⟩ :=
    sheafHom_affine_rightAdjoint (f := f)
  change (SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
    SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))) at H
  have hH : H.Additive := adj₀.right_adjoint_additive
  let _ := hH
  let T := SheafOfModules.restrictScalars.{u}
    (R := moduleRings X.toRingedSpace)
    (R' := moduleRings (directImageAlgebraSpace f))
    ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩
  obtain ⟨E, _, adjE, _⟩ := SheafOfModules.exists_changeOfRingsAdjunction
    X.toTopCat X.sheaf (directImageAlgebraSpace f).sheaf ⟨f.c⟩
  change E ⊣ T at adjE
  have : T.IsRightAdjoint := adjE.isRightAdjoint
  have : T.IsLeftAdjoint := adj₀.isLeftAdjoint
  have : Limits.PreservesFiniteLimits T := by infer_instance
  have : Limits.PreservesFiniteColimits T := by infer_instance
  change T ⊣ H at adj₀
  let L := T.mapDerivedCategory
  let t := T.mapDerivedCategoryFactors
  let F := H.mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))
  let W := HomologicalComplex.quasiIso
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)
  have : IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian _
  have : Abelian.HasKInjectiveResolutions
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := by infer_instance
  have hder : (CochainComplex.KInjectives.localizerMorphism
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))).Derives F := by
    intro K K' a ha
    have : K.obj.IsKInjective := K.property
    have : K'.obj.IsKInjective := K'.property
    have : QuasiIso a.hom := ha
    obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff a.hom).mp inferInstance
    have : QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map a.hom) := by
      rw [← he]
      exact (H.mapHomotopyEquiv e).quasiIso_hom
    change IsIso (DerivedCategory.Q.map
      ((H.mapHomologicalComplex (.up ℤ)).map a.hom))
    infer_instance
  have := hder.hasPointwiseRightDerivedFunctor
  let R := F.totalRightDerived DerivedCategory.Q W
  let β := F.totalRightDerivedUnit DerivedCategory.Q W
  have : R.IsRightDerivedFunctor β W := by dsimp [R, β]; infer_instance
  have : (R ⋙ L).IsRightDerivedFunctor
      (Functor.whiskerRight β L ≫ (Functor.associator _ _ _).hom) W :=
    LocalizerMorphism.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure
      (CochainComplex.KInjectives.localizerMorphism _) β
      (fun I ↦ hder.isIso_of_isRightDerivedFunctor β I) L
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso _ (.up ℤ)) L t
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso _ (.up ℤ)) (L ⋙ R)
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight t R)
  let adj := (adj₀.mapHomologicalComplex (.up ℤ)).derived
    (HomologicalComplex.quasiIso _ (.up ℤ)) W t.hom β
  refine ⟨H, hH, iH, adj₀, hc, R, β, L, t, adj, inferInstance, inferInstance, ?_, ?_⟩
  · let M := T.obj (SheafOfModules.unit (moduleRings (directImageAlgebraSpace f)))
    let K := (SheafOfModules.homFunctor X.sheaf).obj (op M)
    change H ⋙ T ≅ K at iH
    have : K.Additive := (H ⋙ T).additive_of_iso iH
    let e₁ := (Functor.associator (H.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q L) ≪≫
      Functor.isoWhiskerLeft (H.mapHomologicalComplex (.up ℤ)) t
    let e₂ := (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso iH (.up ℤ))
        DerivedCategory.Q
    let e := e₁ ≪≫ e₂
    let δ := e.inv ≫ Functor.whiskerRight β L ≫ (Functor.associator _ _ _).hom
    have hδ : (R ⋙ L).IsRightDerivedFunctor δ W := by
      rw [Functor.isRightDerivedFunctor_iff_isLeftKanExtension]
      apply (Functor.isLeftKanExtension_iff_of_iso₂
        (Functor.whiskerRight β L ≫ (Functor.associator _ _ _).hom) δ e
        (Iso.refl (R ⋙ L)) ?_).mp
      · exact Functor.IsRightDerivedFunctor.isLeftKanExtension _ _ W
      · dsimp [δ]
        simp only [Iso.hom_inv_id_assoc]
        change _ ≫ 𝟙 _ = _
        exact Category.comp_id _
    exact derivedInternalHom_single_comparison X M (R ⋙ L) δ hδ
  · intro K
    have hε : (adj₀.mapHomologicalComplex (.up ℤ)).counit.app K =
        (NatTrans.mapHomologicalComplex adj₀.counit (.up ℤ)).app K := by
      ext n
      rfl
    have he := (adj₀.mapHomologicalComplex (.up ℤ)).derivedε_fac_app W t.hom β K
    rw [hε] at he
    exact he

end AlgebraicGeometry
