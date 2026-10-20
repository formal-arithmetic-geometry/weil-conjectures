/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.AlgebraicGeometry.DerivedAdjoint
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Pullback of the source coproduct in a flat telescope

Source: Stacks Tags 06YS and 06YJ, sum step of the telescope normalization plan.
(blueprint: lem-sc-flat-telescope-pullback-sum-colimit). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

private lemma coproduct_homotopy
    {C : Type*} [Category C] [Preadditive C] {I : Type*}
    [HasColimitsOfShape (Discrete I) C]
    (K : I → CochainComplex C ℤ) {L : CochainComplex C ℤ}
    (f g : ∐ K ⟶ L) (h : ∀ i, Homotopy (Sigma.ι K i ≫ f) (Sigma.ι K i ≫ g)) :
    Nonempty (Homotopy f g) := by
  let hc (n : ℤ) := isColimitOfPreserves
    (HomologicalComplex.eval C (ComplexShape.up ℤ) n) (coproductIsCoproduct K)
  let t (n m : ℤ) : Cocone
      (Discrete.functor K ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) n) :=
    { pt := L.X m
      ι := { app := fun i ↦ (h i.as).hom n m
             naturality := by
               rintro ⟨i⟩ ⟨j⟩ f
               obtain rfl := Discrete.eq_of_hom f
               simp } }
  let a (n m : ℤ) : (∐ K).X n ⟶ L.X m :=
    (hc n).desc (t n m)
  have ha (i : I) (n m : ℤ) : (Sigma.ι K i).f n ≫ a n m = (h i).hom n m := by
    exact (hc n).fac (t n m) ⟨i⟩
  refine ⟨{ hom := a, zero := ?_, comm := ?_ }⟩
  · intro n m hnm
    apply (hc n).hom_ext
    rintro ⟨i⟩
    simpa only [Functor.mapCocone_ι_app, Cofan.mk_ι_app, HomologicalComplex.eval_map,
      ha, comp_zero] using (h i).zero n m hnm
  · intro n
    apply (hc n).hom_ext
    rintro ⟨i⟩
    change (Sigma.ι K i).f n ≫ f.f n = _
    simp only [Functor.mapCocone_ι_app, Cofan.mk_ι_app, HomologicalComplex.eval_map,
      Preadditive.comp_add, dNext, prevD, AddMonoidHom.mk'_apply]
    rw [(Sigma.ι K i).comm_assoc, ha, ← Category.assoc, ha]
    exact (h i).comm n

private lemma derived_map_surjective
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K L : CochainComplex C ℤ) [L.IsKInjective] :
    Function.Surjective (DerivedCategory.Q.map : (K ⟶ L) → _) := by
  intro f
  let e := DerivedCategory.quotientCompQhIso C
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj K) L).surjective
    (e.hom.app K ≫ f ≫ e.inv.app L)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨g, ?_⟩
  apply (cancel_mono (e.inv.app L)).1
  rw [DerivedCategory.quotientCompQhIso_inv_naturality, hg]
  simp [e]

private lemma derived_map_homotopy
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {K L : CochainComplex C ℤ} [L.IsKInjective] (f g : K ⟶ L)
    (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    Nonempty (Homotopy f g) := by
  refine ⟨HomotopyCategory.homotopyOfEq f g ?_⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj K) L).injective
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app L)).1
  simp only [DerivedCategory.quotientCompQhIso_hom_naturality, h]


private theorem derived_coproduct
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions C] {I : Type*}
    [HasColimitsOfShape (Discrete I) C] (K : I → CochainComplex C ℤ) :
    Nonempty (IsColimit (Cofan.mk (DerivedCategory.Q.obj (∐ K))
      (fun i ↦ DerivedCategory.Q.map (Sigma.ι K i)))) := by
  classical
  have hu (X : DerivedCategory C)
      (a : ∀ i, DerivedCategory.Q.obj (K i) ⟶ X) :
      ∃! d : DerivedCategory.Q.obj (∐ K) ⟶ X,
        ∀ i, DerivedCategory.Q.map (Sigma.ι K i) ≫ d = a i := by
    obtain ⟨L, _, r, _, _⟩ :=
      Abelian.HasKInjectiveResolutions.exists_isKInjective
        (DerivedCategory.Q.objPreimage X)
    let e : X ≅ DerivedCategory.Q.obj L :=
      (DerivedCategory.Q.objObjPreimageIso X).symm ≪≫ asIso (DerivedCategory.Q.map r)
    choose f hf using fun i ↦ derived_map_surjective (K i) L (a i ≫ e.hom)
    let d := DerivedCategory.Q.map (Sigma.desc f) ≫ e.inv
    have hd (i : I) : DerivedCategory.Q.map (Sigma.ι K i) ≫ d = a i := by
      dsimp [d]
      rw [← Category.assoc, ← Functor.map_comp, Sigma.ι_desc, hf]
      simp
    refine ⟨d, hd, ?_⟩
    intro m hm
    apply (cancel_mono e.hom).1
    obtain ⟨g, hg⟩ := derived_map_surjective (∐ K) L (m ≫ e.hom)
    have he (i : I) :
        DerivedCategory.Q.map (Sigma.ι K i ≫ g) = DerivedCategory.Q.map (f i) := by
      rw [Functor.map_comp, hg, ← Category.assoc, hm, hf]
    have hhom := coproduct_homotopy K g (Sigma.desc f) (fun i ↦
      (derived_map_homotopy (Sigma.ι K i ≫ g) (Sigma.ι K i ≫ Sigma.desc f)
        (by simpa only [Sigma.ι_desc] using he i)).some)
    rw [← hg, DerivedCategory.Q_map_eq_of_homotopy _ hhom.some]
    simp [d]
  refine ⟨Cofan.IsColimit.mk _ (fun t ↦ (hu t.pt t.inj).choose) ?_ ?_⟩
  · intro t i
    exact (hu t.pt t.inj).choose_spec.1 i
  · intro t m hm
    exact (hu t.pt t.inj).choose_spec.2 m hm


/-- Derived pullback of a complex sum, and of its translate, gives the coproduct
of the corresponding stage images. No flatness or boundedness is required.

Source: Stacks Tag 07D9, Injectives, direct sums in derived categories, and Tag 079W,
Cohomology, derived pullback adjunction. Sum step of
lem-sc-flat-telescope-normalization-morphisms.

Proof. Sheaf modules have K-injective resolutions. Represent any target by a
K-injective complex. Each derived map from a stage lifts to a chain map into this
representative, by bijectivity of Qh on maps into K-injectives and surjectivity of
the homotopy quotient. The coproduct of complexes assembles these chain maps.
Two factorizations equal on all stages have homotopies on each stage; the degreewise
coproduct universal property assembles these into a homotopy on the sum. Thus Q of
the sum has the coproduct universal property, with the prescribed inclusions.
Derived pullback is left adjoint to derived direct image and preserves the cofan.
Transport along quotientCompQhIso to the homotopy-localization formulation.
For the translated cofan use the Qh shift comparison, preservation of coproducts
by the derived shift equivalence, and preservation by derived pullback again.
Zero stages and the zero category on an empty scheme are included.
(blueprint: lem-sc-flat-telescope-pullback-sum-colimit). -/
theorem flat_telescope_pullback_sum_colimit
    {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    let q := HomotopyCategory.quotient
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)
    let L := DerivedCategory.Qh ⋙ derivedPullback f
    Nonempty (IsColimit (Cofan.mk (L.obj (q.obj (∐ E)))
      (fun n ↦ L.map (q.map (Sigma.ι E n))))) ∧
    Nonempty (IsColimit (Cofan.mk (L.obj ((q.obj (∐ E))⟦(1 : ℤ)⟧))
      (fun n ↦ L.map ((q.map (Sigma.ι E n))⟦(1 : ℤ)⟧')))) := by
  classical
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let F := derivedPullback f
  have : Abelian.HasKInjectiveResolutions A :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
  have hQ := (derived_coproduct E).some
  have : PreservesColimit (Discrete.functor E) (DerivedCategory.Q : _ ⥤
      schemeDerivedCategory Y) :=
    preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct E)
      ((Cofan.isColimitMapCoconeEquiv DerivedCategory.Q E _).symm hQ)
  have : PreservesColimit (Discrete.functor E) (q ⋙ DerivedCategory.Qh) :=
    preservesColimit_of_natIso _ (DerivedCategory.quotientCompQhIso A).symm
  have : F.IsLeftAdjoint := (nonempty_derivedPullbackAdjunction f).some.isLeftAdjoint
  have hc := isColimitOfPreserves ((q ⋙ DerivedCategory.Qh) ⋙ F)
    (coproductIsCoproduct E)
  have hc₀ : IsColimit (Cofan.mk (F.obj (DerivedCategory.Qh.obj (q.obj (∐ E))))
      (fun n ↦ F.map (DerivedCategory.Qh.map (q.map (Sigma.ι E n))))) :=
    Cofan.isColimitMapCoconeEquiv _ E _ hc
  let S := shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) (1 : ℤ)
  have : PreservesColimit (Discrete.functor E) (q ⋙ S ⋙ DerivedCategory.Qh) := by
    let S' := shiftFunctor (schemeDerivedCategory Y) (1 : ℤ)
    have : PreservesColimit (Discrete.functor E) ((q ⋙ DerivedCategory.Qh) ⋙ S') :=
      inferInstance
    exact preservesColimit_of_natIso _
      ((Functor.associator q S DerivedCategory.Qh) ≪≫
        Functor.isoWhiskerLeft q (DerivedCategory.Qh.commShiftIso (1 : ℤ)) ≪≫
        (Functor.associator q DerivedCategory.Qh S').symm).symm
  have hc' := isColimitOfPreserves ((q ⋙ S ⋙ DerivedCategory.Qh) ⋙ F)
    (coproductIsCoproduct E)
  refine ⟨⟨hc₀⟩, ⟨?_⟩⟩
  exact Cofan.isColimitMapCoconeEquiv _ E _ hc'

end AlgebraicGeometry
