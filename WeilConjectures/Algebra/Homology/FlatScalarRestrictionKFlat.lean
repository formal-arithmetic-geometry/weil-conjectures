/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Flat scalar restriction preserves K-flat complexes

## References

* Stacks Project, Tag 06YN
* Stacks Project, Tag 06YY (scalar-change context)
* Stacks Project, Tag 03EK
* Stacks Project, Tag 03ER
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

attribute [local irreducible] monoidalCategory symmetricCategory

private theorem restriction_exact
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {A B : Sheaf J RingCat.{w}} (α : A ⟶ B) :
    PreservesFiniteLimits (restrictScalars.{w} α) ∧
      PreservesFiniteColimits (restrictScalars.{w} α) := by
  let U := restrictScalars.{w} α
  have : PreservesFiniteLimits (U ⋙ toSheaf A) :=
    inferInstanceAs (PreservesFiniteLimits (toSheaf B))
  have : PreservesFiniteColimits (U ⋙ toSheaf A) :=
    inferInstanceAs (PreservesFiniteColimits (toSheaf B))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves U (toSheaf A),
    preservesFiniteColimits_of_reflects_of_preserves U (toSheaf A)⟩

/-- Restriction along a flat map of commutative ring sheaves preserves K-flatness of
possibly unbounded complexes, and preserves flatness of their terms. -/
theorem isKFlat_restrictScalars_of_flat
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {R B : Sheaf J CommRingCat.{w}} (φ : R ⟶ B)
    (hB : IsFlatOnSite (J := J) (R := R)
      ((restrictScalars.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)).obj
          (unit (J := J) ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B))))
    (P : CochainComplex
      (ringedSiteModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := B) P) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R)
      (((restrictScalars.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ∧
    ((∀ q : ℤ, IsFlatOnSite (J := J) (R := B) (P.X q)) →
      ∀ q : ℤ, IsFlatOnSite (J := J) (R := R)
        ((restrictScalars.{w}
          ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)).obj (P.X q))) := by
  classical
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  set_option synthInstance.maxSize 512 in
  let : J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) := inferInstance
  let : HasSheafify J AddCommGrpCat.{w} := inferInstance
  let : J.WEqualsLocallyBijective AddCommGrpCat.{w} := inferInstance
  let := isMonoidal_W_independentCoefficients R
  let := isMonoidal_W_independentCoefficients B
  let := monoidalCategory R
  let := monoidalCategory B
  let := symmetricCategory R
  let := symmetricCategory B
  let α := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ
  let U := restrictScalars.{w} α
  have hU := restriction_exact α
  have : PreservesFiniteLimits U := hU.1
  have : PreservesFiniteColimits U := hU.2
  let E₀ : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⥤
      PresheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B).obj :=
    { obj := changeOfRingsPresheaf.{v, u, w} φ
      map := fun a ↦
        { app := fun V ↦ (ModuleCat.extendScalars (φ.hom.app V).hom).map (a.val.app V)
          naturality := changeOfRingsHom_naturality.{v, u, w} φ _ a }
      map_id := by
        intro M
        apply PresheafOfModules.hom_ext
        intro V
        simp
        rfl
      map_comp := by
        intro M N P a b
        apply PresheafOfModules.hom_ext
        intro V
        simp }
  let E := E₀ ⋙ PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B).obj)
  have (V : Cᵒᵖ) : (ModuleCat.extendScalars (φ.hom.app V).hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (φ.hom.app V).hom).left_adjoint_additive
  have : E₀.Additive := by
    constructor
    intro M N a b
    apply PresheafOfModules.hom_ext
    intro V
    simpa only [E₀, SheafOfModules.add_val, PresheafOfModules.add_app] using
      (ModuleCat.extendScalars (φ.hom.app V).hom).map_add
        (f := a.val.app V) (g := b.val.app V)
  have : E.Additive := by
    have : (PresheafOfModules.sheafification
        (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B).obj)).Additive :=
      (PresheafOfModules.sheafificationAdjunction (𝟙 _)).left_adjoint_additive
    infer_instance
  obtain ⟨e₀, he₀⟩ := exists_changeOfRings_tensorCancellation_independentCoefficients φ
  let e (M : SheafOfModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
      (N : SheafOfModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj B)) :
      U.obj (E.obj M ⊗ N) ≅ M ⊗ U.obj N :=
    U.mapIso (β_ (E.obj M) N) ≪≫ e₀ N M ≪≫ β_ (U.obj N) M
  have he {M M' : SheafOfModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)}
      {N N' : SheafOfModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj B)} (f : M ⟶ M') (g : N ⟶ N') :
      U.map (tensorHom (E.map f) g) ≫ (e M' N').hom =
        (e M N).hom ≫ tensorHom f (U.map g) := by
    have hh : U.map (tensorHom g (E.map f)) ≫ (e₀ N' M').hom =
        (e₀ N M).hom ≫ tensorHom (U.map g) f := he₀ g f
    dsimp only [e, Iso.trans_hom, Functor.mapIso_hom]
    rw [← U.map_comp_assoc, BraidedCategory.braiding_naturality, U.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% hh]
    rw [BraidedCategory.braiding_naturality (U.map g) f]
  let S := U.obj (𝟙_ (SheafOfModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B)))
  -- The regular module in tensor cancellation identifies restricted scalar extension.
  let q : E ⋙ U ≅ tensorRight S :=
    NatIso.ofComponents (fun M ↦ U.mapIso (ρ_ (E.obj M)).symm ≪≫ e M (𝟙_ _)) (by
      intro M N f
      change U.map (E.map f) ≫ _ = _ ≫ (f ▷ S)
      dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv]
      rw [← U.map_comp_assoc, rightUnitor_inv_naturality, U.map_comp, Category.assoc]
      have hh := he f (𝟙 (𝟙_ _))
      simpa only [U.map_id, tensorHom_id, Category.assoc] using congrArg
        (fun t ↦ U.map (ρ_ (E.obj M)).inv ≫ t) hh)
  have hS0 : IsFlatOnSite (R := R) S := by
    with_unfolding_all exact hB
  have hS : exactFunctor _ _ (tensorRight S) :=
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R S) hS0
  have : PreservesFiniteLimits (tensorRight S) := hS.1
  have : PreservesFiniteColimits (tensorRight S) := hS.2
  have : PreservesFiniteLimits (E ⋙ U) := preservesFiniteLimits_of_natIso q.symm
  have : PreservesFiniteColimits (E ⋙ U) := preservesFiniteColimits_of_natIso q.symm
  have : U.ReflectsIsomorphisms := by
    have : (U ⋙ toSheaf
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)).ReflectsIsomorphisms :=
      inferInstanceAs ((toSheaf
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B)).ReflectsIsomorphisms)
    exact reflectsIsomorphisms_of_comp U (toSheaf _)
  have : PreservesFiniteLimits E := preservesFiniteLimits_of_reflects_of_preserves E U
  have : PreservesFiniteColimits E := preservesFiniteColimits_of_reflects_of_preserves E U
  constructor
  · intro F hF
    let T := (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      ((E.mapHomologicalComplex (.up ℤ)).obj F)).obj P
    have hcolim (D : Type) [Category.{0} D] : PreservesColimitsOfShape D U := by
      have : PreservesColimitsOfShape D (U ⋙ toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :=
        inferInstanceAs (PreservesColimitsOfShape D (toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B)))
      have : ReflectsColimitsOfShape D (toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :=
        reflectsColimitsOfShape_of_reflectsIsomorphisms
      exact preservesColimitsOfShape_of_reflects_of_preserves U (toSheaf _)
    have : PreservesColimitsOfSize.{0, 0} U := ⟨fun {D} instD ↦ @hcolim D instD⟩
    have : U.PreservesTotalComplex T (.up ℤ) := fun _ ↦ inferInstance
    -- Functorial totalization handles the direct sums and both signed differentials.
    let t := (HomologicalComplex₂.mapTotalIso U T (.up ℤ)).symm
    let f :
        (((U.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj T) ≅
        (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj F).obj
          ((U.mapHomologicalComplex (.up ℤ)).obj P) :=
      HomologicalComplex.Hom.isoOfComponents
        (fun i ↦ HomologicalComplex.Hom.isoOfComponents
          (fun j ↦ e (F.X i) (P.X j)) (by
            intro j j' hj
            change (e (F.X i) (P.X j)).hom ≫ whiskerLeft (F.X i) (U.map (P.d j j')) =
              U.map (whiskerLeft (E.obj (F.X i)) (P.d j j')) ≫
                (e (F.X i) (P.X j')).hom
            simpa only [E.map_id, id_tensorHom] using (he (𝟙 (F.X i)) (P.d j j')).symm))
        (by
          intro i i' hi
          apply HomologicalComplex.Hom.ext
          funext j
          change (e (F.X i) (P.X j)).hom ≫ whiskerRight (F.d i i') (U.obj (P.X j)) =
            U.map (whiskerRight (E.map (F.d i i')) (P.X j)) ≫
              (e (F.X i') (P.X j)).hom
          simpa only [U.map_id, tensorHom_id] using (he (F.d i i') (𝟙 (P.X j))).symm)
    have hEF : ((E.mapHomologicalComplex (.up ℤ)).obj F).Acyclic :=
      fun i ↦ (hF i).map E
    have h := hP ((E.mapHomologicalComplex (.up ℤ)).obj F) hEF
    have hUT : ((U.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor
          ((E.mapHomologicalComplex (.up ℤ)).obj F) P (curriedTensor _))).Acyclic :=
      fun i ↦ (h i).map U
    intro i
    exact (hUT i).of_iso (t ≪≫ HomologicalComplex₂.total.mapIso f (.up ℤ))
  · intro hflat i
    -- Termwise flatness follows separately, from a composite of three exact functors.
    have hPi : exactFunctor _ _ (tensorRight (P.X i)) :=
      (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso B (P.X i)) (hflat i)
    have : PreservesFiniteLimits (tensorRight (P.X i)) := hPi.1
    have : PreservesFiniteColimits (tensorRight (P.X i)) := hPi.2
    let q' : E ⋙ tensorRight (P.X i) ⋙ U ≅ tensorRight (U.obj (P.X i)) :=
      NatIso.ofComponents (fun M ↦ e M (P.X i)) (by
        intro M N g
        change U.map (E.map g ▷ P.X i) ≫ (e N (P.X i)).hom =
          (e M (P.X i)).hom ≫ (g ▷ U.obj (P.X i))
        simpa only [U.map_id, tensorHom_id] using he g (𝟙 (P.X i)))
    have : PreservesFiniteLimits (tensorRight (P.X i) ⋙ U) :=
      comp_preservesFiniteLimits _ _
    have : PreservesFiniteColimits (tensorRight (P.X i) ⋙ U) :=
      comp_preservesFiniteColimits _ _
    have : PreservesFiniteLimits (E ⋙ tensorRight (P.X i) ⋙ U) :=
      comp_preservesFiniteLimits _ _
    have : PreservesFiniteColimits (E ⋙ tensorRight (P.X i) ⋙ U) :=
      comp_preservesFiniteColimits _ _
    have hh : exactFunctor _ _ (tensorRight (U.obj (P.X i))) :=
      ⟨preservesFiniteLimits_of_natIso q', preservesFiniteColimits_of_natIso q'⟩
    exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R _).symm hh

end SheafOfModules
