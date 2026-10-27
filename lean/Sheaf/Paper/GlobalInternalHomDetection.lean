/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Sheaf.Paper.FiniteModelTopologyComparisonMaps
import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Shift.Adjunction

/-! # Detection of shifted morphisms by derived global internal Hom

Source: Stacks Project, Tag 08JA, with Tags 0A95 and 0A96
(blueprint: lem-sfb-global-internal-hom-detection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Sheaf.monoidalCategory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteModelTopologyHom

private instance (priority := 100000) smallSheafColimits (X : Scheme.{u}) :
    HasColimitsOfSize.{0, 0} (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) := by
  let J := Scheme.ProEt.topology X
  refine ⟨fun I _ ↦ ⟨fun F ↦ ?_⟩⟩
  exact ⟨⟨Sheaf.sheafifyCocone
    (colimit.cocone (F ⋙ sheafToPresheaf J Ab.{u + 1})),
      Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩

private instance (priority := 100000) countableSheafCoproducts (X : Scheme.{u}) :
    HasCountableCoproducts (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) where
  out I _ := (smallSheafColimits X).has_colimits_of_shape (Discrete I)

private theorem hom_bijective_of_sections_internalHom_isIso
    {C D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ] [MonoidalCategory D] [MonoidalClosed D]
    (L : C ⥤ D) (S : D ⥤ C) (a : L ⊣ S) [L.CommShift ℤ]
    (P : C) (e : L.obj P ≅ 𝟙_ D) (K : D) [(tensorLeft K).CommShift ℤ]
    {N N' : D} (f : N ⟶ N') (h : IsIso (S.map ((ihom K).map f))) (n : ℤ) :
    Function.Bijective (fun g : K ⟶ N⟦n⟧ ↦ g ≫ f⟦n⟧') := by
  let B := P⟦-n⟧
  let ee : (tensorLeft K).obj (L.obj B) ≅ K⟦-n⟧ :=
    (tensorLeft K).mapIso ((L.commShiftIso (-n)).app P ≪≫
      (shiftFunctor D (-n)).mapIso e) ≪≫
      ((tensorLeft K).commShiftIso (-n)).app (𝟙_ D) ≪≫
      (shiftFunctor D (-n)).mapIso (ρ_ K)
  let b := a.comp (ihom.adjunction K)
  let sh : shiftFunctor D (-n) ⊣ shiftFunctor D n :=
    (shiftEquiv' D (-n) n (neg_add_cancel n)).toAdjunction
  let u (Y : D) : (K ⟶ Y⟦n⟧) ≃ (B ⟶ S.obj ((ihom K).obj Y)) :=
    (sh.homEquiv K Y).symm.trans
      ((ee.symm.homCongr (Iso.refl Y)).trans (b.homEquiv B Y))
  have hu (g : K ⟶ N⟦n⟧) :
      u N' (g ≫ f⟦n⟧') = u N g ≫ S.map ((ihom K).map f) := by
    simp only [u, Equiv.coe_trans, Function.comp_apply, Iso.homCongr_apply,
      Iso.symm_inv, Iso.refl_hom, Category.comp_id]
    rw [sh.homEquiv_naturality_right_symm, ← Category.assoc]
    exact b.homEquiv_naturality_right _ f
  letI := h
  have hb : Function.Bijective (fun g : B ⟶ S.obj ((ihom K).obj N) ↦
      g ≫ S.map ((ihom K).map f)) := (asIso (S.map ((ihom K).map f))).homToEquiv.bijective
  constructor
  · intro g g' hgg'
    apply (u N).injective
    exact hb.injective ((hu g).symm.trans
      ((congrArg (u N') hgg').trans (hu g')))
  · intro g
    obtain ⟨v, hv⟩ := hb.surjective (u N' g)
    refine ⟨(u N).symm v, (u N').injective ?_⟩
    rw [hu, Equiv.apply_symm_apply]
    exact hv

private instance free_additive (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    (Mod.free R).Additive := (Mod.freeForgetAdjunction R).left_adjoint_additive

private theorem free_preservesKFlatQuasiIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    (Mod.free R).PreservesKFlatQuasiIso := by
  have : (Mod.free R).Additive := (Mod.freeForgetAdjunction R).left_adjoint_additive
  refine Functor.PreservesKFlatQuasiIso.mk' _ ?_
  intro K hK hKa
  have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa R
  have hl := ht.of_iso
    ((NatIso.mapHomologicalComplex
      (BraidedCategory.tensorLeftIsoTensorRight R) _).app K).symm
  have he : (((Mod.free R ⋙ Mod.forget R).mapHomologicalComplex _).obj K).Acyclic := hl
  intro n
  exact (ShortComplex.exact_map_iff_of_faithful _ (Mod.forget R)).1 (he n)

private instance free_kflat (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    (Mod.free R).PreservesKFlatQuasiIso := free_preservesKFlatQuasiIso X R

private noncomputable def freeUnitIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    (Mod.free R).obj (𝟙_ _) ≅ Mod.regular R :=
  Mod.isoMk (ρ_ R) (by
    change (α_ R R (𝟙_ _)).inv ≫ MonObj.mul ▷ (𝟙_ _) ≫ (ρ_ R).hom =
      R ◁ (ρ_ R).hom ≫ MonObj.mul
    monoidal)

private noncomputable def derivedFreeUnitIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (Mod.free R).leftDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _)) ≅
        𝟙_ (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)) := by
  let F := Mod.free R
  let A := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  let D := Mod A R
  let P := (CochainComplex.singleFunctor A 0).obj (𝟙_ A)
  have hP : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P :=
    (CochainComplex.kFlat_single_obj_iff_flat _ 0).2
      (CategoryTheory.ObjectProperty.prop_unit CategoryTheory.ObjectProperty.flat)
  haveI := F.isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
  exact F.leftDerivedFunctor.mapIso ((DerivedCategory.singleFunctorIsoCompQ A 0).app _) ≪≫
    F.leftDerivedFunctor.mapIso ((DerivedCategory.quotientCompQhIso A).symm.app P) ≪≫
    asIso (F.leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient A (.up ℤ)).obj P)) ≪≫
    (DerivedCategory.quotientCompQhIso D).app
      ((F.mapHomologicalComplex (.up ℤ)).obj P) ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex F
      (.up ℤ) 0).app (𝟙_ A)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ D 0).app (F.obj (𝟙_ A))).symm ≪≫
    (DerivedCategory.singleFunctor D 0).mapIso (freeUnitIso X R) ≪≫
    DerivedCategory.singleFunctorObjUnitIso D

/-- If derived global internal Hom from K inverts f, then composition with every
shift of f is bijective. There is no scalar change, boundedness or constructibility
hypothesis: this is the natural derived global Hom calculation.

Source: Stacks Project, Tag 08JA, global statement, and Tags 0A95 and 0A96
(blueprint: lem-sfb-global-internal-hom-detection).

Proof: The ordinary free-module functor R tensor - preserves quasi-isomorphisms
between K-flat abelian-sheaf complexes: an acyclic K-flat complex remains acyclic
when tensored with R, and the faithful exact forgetful functor detects acyclicity.
Thus the free/forgetful adjunction derives, with the exact right adjoint given by
termwise forgetting. Compose it with the derived constant-sheaf/global-sections
adjunction. The resulting right adjoint is precisely the specified sections functor.
The left adjoint sends the integer group in degree zero to the regular module in
degree zero: the constant-sheaf functor is strong monoidal, and its image is K-flat,
so the derived free counit computes this object by ordinary free extension.
This regular module is the monoidal unit of the native derived category.
Now shift that integer test object by -n. The left adjoint commutes with shifts
(by the mate of the right adjoint's shift structure), and tensoring K with its
image gives K[-n] by the tensor shift isomorphism and right unitor. The composite
of the shift adjunction, this isomorphism, and the two adjunctions identifies
Hom(K,N[n]) naturally with Hom(Z[-n], RΓ_ab RHom(K,N)). Naturality identifies
postcomposition by f[n] with postcomposition by RΓ_ab RHom(K,f). The latter is
bijective by the assumed isomorphism; transport its inverse through the displayed
bijections. This uses no boundedness, support, scalar-flatness or nonzero-ring
hypothesis and includes the empty scheme and negative shifts. -/
theorem shiftedHom_bijective_of_globalInternalHom_isIso
    (X : Scheme.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    {N N' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (f : N ⟶ N')
    (h : IsIso ((sections X (condensedRingObj Λ X)).map
      (((CondensedRing.derivedHom Λ X).obj (op K)).map f))) (n : ℤ) :
    Function.Bijective (fun g : K ⟶ N⟦n⟧ ↦ g ≫ f⟦n⟧') := by
  let A := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  let R := condensedRingObj Λ X
  let F := Mod.free R
  let T := constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  let Γ := Sheaf.Γ (Scheme.ProEt.topology X) Ab.{u + 1}
  haveI : Γ.IsRightAdjoint := (constantSheafΓAdj _ _).isRightAdjoint
  haveI : Γ.Additive := Functor.additive_of_preserves_binary_products _
  haveI : T.Additive := (constantSheafΓAdj _ _).left_adjoint_additive
  let a : T.mapDerivedCategory ⊣ Γ.rightDerivedFunctor :=
    (constantSheafΓAdj (Scheme.ProEt.topology X) Ab.{u + 1}).derivedAdjunction.ofNatIsoLeft
      T.leftDerivedFunctorIsoMapDerivedCategory
  let b : F.leftDerivedFunctor ⊣ (Mod.forget R).mapDerivedCategory :=
    (Mod.freeForgetAdjunction R).derivedAdjunction.ofNatIsoRight
      (Mod.forget R).rightDerivedFunctorIsoMapDerivedCategory
  let d := a.comp b
  letI : (T.mapDerivedCategory ⋙ F.leftDerivedFunctor).CommShift ℤ :=
    d.leftAdjointCommShift ℤ
  let P := (DerivedCategory.singleFunctor Ab.{u + 1} 0).obj (𝟙_ Ab.{u + 1})
  let e : (T.mapDerivedCategory ⋙ F.leftDerivedFunctor).obj P ≅
      𝟙_ (DerivedCategory (Mod A R)) :=
    F.leftDerivedFunctor.mapIso ((T.mapDerivedCategorySingleFunctor 0).app _) ≪≫
    F.leftDerivedFunctor.mapIso ((DerivedCategory.singleFunctor A 0).mapIso
      (Functor.Monoidal.εIso T).symm) ≪≫ derivedFreeUnitIso X R
  letI : (tensorLeft K).CommShift ℤ := DerivedCategory.commShiftTensorLeft (Mod A R) K
  exact hom_bijective_of_sections_internalHom_isIso
    (T.mapDerivedCategory ⋙ F.leftDerivedFunctor)
    ((Mod.forget R).mapDerivedCategory ⋙ Γ.rightDerivedFunctor) d P e K f h n

end AlgebraicGeometry.ProEtale.FiniteModelTopologyHom
