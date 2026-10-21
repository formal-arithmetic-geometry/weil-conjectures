/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.Paper.LocalizingClosureExistence
public import WeilConjectures.CategoryTheory.CompactObject
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.Paper.AmbientIndDerivedTriangulated
import Sheaf.Paper.ConstructibleCompactnessBounded
import WeilConjectures.CategoryTheory.CompactObjectsThick
import Sheaf.Paper.AmbientIndDerivedSums
import Sheaf.Paper.FiniteWindow
import Sheaf.Paper.UniformConstructibleExt

import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.Algebra.DirectSum.Module
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import Mathlib.Algebra.CharP.CharAndCard

/-!
# Compactness with rational coefficients

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-constructible-compactness, statement and proof; Stacks Project, Tag 09QH
(blueprint: sk-thm-constructible-compactness).

The two coefficient choices are the continuous-function condensed ring of a finite
subextension and the finite-subextension-valued condensed algebraic closure. The
ambient category is the ordinary unbounded derived category of internal left modules.
Cons and Dbc use finite constant scalar models, rather than arbitrary local finite
presentations. IndCons and Dic are expressed inline using Mathlib's filtered-colimit
property and the ambient cohomology functors.
-/

@[expose] public section

set_option autoImplicit false

universe t w v u

open CategoryTheory CategoryTheory.Limits DirectSum

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Classical in
private theorem compact_iff_ambient
    {A : Type u} [Category.{v} A] [Preadditive A] [HasCoproducts.{w} A]
    (P : ObjectProperty A)
    [∀ I : Type w, P.IsClosedUnderColimitsOfShape (Discrete I)]
    (C : P.FullSubcategory) :
    IsCompactObject.{w} C ↔
      ∀ (I : Type w) (K : I → A), (∀ i, P (K i)) →
      ∀ (c : Cofan K), IsColimit c →
      Function.Bijective
        (DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp C.obj (c.inj i))) := by
  classical
  let e (Y : P.FullSubcategory) : (C ⟶ Y) ≃+ (C.obj ⟶ Y.obj) :=
    { toFun := fun f ↦ f.hom
      invFun := ObjectProperty.homMk
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  constructor
  · intro h I K hK c hc
    let L : I → P.FullSubcategory := fun i ↦ ⟨K i, hK i⟩
    let d : Cofan (fun i ↦ (L i).obj) :=
      Cofan.mk _ (fun i ↦ (Sigma.ι L i).hom)
    have hd : IsColimit d :=
      (Cofan.isColimitMapCoconeEquiv P.ι L (Cofan.mk _ (Sigma.ι L))).toFun
        (isColimitOfPreserves P.ι (coproductIsCoproduct L))
    let f : d.pt ≅ c.pt := hd.coconePointUniqueUpToIso hc
    let a := DirectSum.map (fun i ↦ (e (L i)).toAddMonoidHom)
    have ha : Function.Bijective a :=
      ⟨(DirectSum.map_injective _).2 (fun i ↦ (e (L i)).injective),
        (DirectSum.map_surjective _).2 (fun i ↦ (e (L i)).surjective)⟩
    let b : (C ⟶ ∐ L) ≃+ (C.obj ⟶ c.pt) :=
      { toFun := fun g ↦ g.hom ≫ f.hom
        invFun := fun g ↦ ObjectProperty.homMk (g ≫ f.inv)
        left_inv := by
          intro g
          apply ObjectProperty.hom_ext
          simp
        right_inv := by intro g; simp
        map_add' := by
          intro g h
          change (g.hom + h.hom) ≫ f.hom = g.hom ≫ f.hom + h.hom ≫ f.hom
          simp only [Preadditive.add_comp] }
    have heq : (DirectSum.toAddMonoid (fun i ↦
        Preadditive.rightComp C.obj (c.inj i))).comp a =
        b.toAddMonoidHom.comp
          (DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp C (Sigma.ι L i))) := by
      ext i g
      simp only [a, AddMonoidHom.comp_apply,
        DirectSum.toAddMonoid_of]
      rw [DirectSum.map_of, DirectSum.toAddMonoid_of]
      change g.hom ≫ c.inj i = (g ≫ Sigma.ι L i).hom ≫ f.hom
      rw [ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
      congr 1
      exact (hd.comp_coconePointUniqueUpToIso_hom hc ⟨i⟩).symm
    have hb := b.bijective.comp (h I L)
    have hab : Function.Bijective
        ((DirectSum.toAddMonoid (fun i ↦
          Preadditive.rightComp C.obj (c.inj i))).comp a) := by
      rw [heq]
      exact hb
    constructor
    · intro x y hxy
      obtain ⟨x', rfl⟩ := ha.2 x
      obtain ⟨y', rfl⟩ := ha.2 y
      exact congrArg a (hab.1 hxy)
    · intro g
      obtain ⟨x, hx⟩ := hab.2 g
      exact ⟨a x, hx⟩
  · intro h I L
    let d : Cofan (fun i ↦ (L i).obj) :=
      Cofan.mk _ (fun i ↦ (Sigma.ι L i).hom)
    have hd : IsColimit d :=
      (Cofan.isColimitMapCoconeEquiv P.ι L (Cofan.mk _ (Sigma.ι L))).toFun
        (isColimitOfPreserves P.ι (coproductIsCoproduct L))
    have hb := h I (fun i ↦ (L i).obj) (fun i ↦ (L i).property) d hd
    let a := DirectSum.map (fun i ↦ (e (L i)).toAddMonoidHom)
    have ha : Function.Bijective a :=
      ⟨(DirectSum.map_injective _).2 (fun i ↦ (e (L i)).injective),
        (DirectSum.map_surjective _).2 (fun i ↦ (e (L i)).surjective)⟩
    have heq : (e (∐ L)).toAddMonoidHom.comp
        (DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp C (Sigma.ι L i))) =
        (DirectSum.toAddMonoid (fun i ↦
          Preadditive.rightComp C.obj (d.inj i))).comp a := by
      apply DirectSum.addHom_ext
      intro i g
      change (e (∐ L))
          ((DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp C (Sigma.ι L i)))
            (DirectSum.of _ i g)) =
        (DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp C.obj (d.inj i)))
          (DirectSum.map (fun i ↦ (e (L i)).toAddMonoidHom) (DirectSum.of _ i g))
      rw [DirectSum.toAddMonoid_of, DirectSum.map_of, DirectSum.toAddMonoid_of]
      rfl
    have hab : Function.Bijective ((e (∐ L)).toAddMonoidHom.comp
        (DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp C (Sigma.ι L i)))) := by
      rw [heq]
      exact hb.comp ha
    constructor
    · intro x y hxy
      exact hab.1 (congrArg (e (∐ L)) hxy)
    · intro f
      obtain ⟨x, hx⟩ := hab.2 (e (∐ L) f)
      exact ⟨x, (e (∐ L)).injective hx⟩

private theorem closed_under_coproducts
    {A : Type u} [Category.{v} A] (P : ObjectProperty A)
    [P.IsClosedUnderIsomorphisms]
    (hsum : ∀ (I : Type w) (K : I → A) (c : Cofan K), IsColimit c →
      (∀ i, P (K i)) → P c.pt) (I : Type w) :
    P.IsClosedUnderColimitsOfShape (Discrete I) := by
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  let c := (Cocone.precompose (Discrete.natIsoFunctor (F := F)).inv).obj
    (colimit.cocone F)
  have hc : IsColimit c :=
    (IsColimit.precomposeInvEquiv Discrete.natIsoFunctor (colimit.cocone F)).symm
      (colimit.isColimit F)
  exact hsum I (fun i ↦ F.obj ⟨i⟩) c hc (fun i ↦ hF ⟨i⟩)

private theorem compact_devissage
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms]
    (T : ObjectProperty (DerivedCategory A))
    [T.IsTriangulated] [T.IsClosedUnderIsomorphisms]
    [HasCoproducts.{w} T.FullSubcategory]
    (hP : ∀ M, P M → ∃ h : T ((DerivedCategory.singleFunctor A 0).obj M),
      IsCompactObject.{w} (ObjectProperty.FullSubcategory.mk _ h))
    (C : DerivedCategory A) (hb : DerivedCategory.TStructure.t.bounded C)
    (hC : ∀ n, P ((DerivedCategory.homologyFunctor A n).obj C)) :
    ∃ h : T C, IsCompactObject.{w} (ObjectProperty.FullSubcategory.mk C h) := by
  let R : ObjectProperty T.FullSubcategory := fun M ↦ IsCompactObject.{w} M
  let : R.IsTriangulated := (compactObjects_isThick (C := T.FullSubcategory)).1
  let : R.IsStableUnderRetracts := (compactObjects_isThick (C := T.FullSubcategory)).2
  have hsingle (M : A) (hM : P M) :
      R.map T.ι ((DerivedCategory.singleFunctor A 0).obj M) := by
    obtain ⟨h, hc⟩ := hP M hM
    exact ⟨⟨_, h⟩, hc, ⟨Iso.refl _⟩⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := DerivedCategory.prop_of_bounded
    (R.map T.ι) P hsingle C hb hC
  have hTC : T C := T.prop_of_iso e M.property
  let f : M ≅ ObjectProperty.FullSubcategory.mk C hTC := T.ι.preimageIso e
  exact ⟨hTC, R.prop_of_iso f hM⟩

private theorem constant_model_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  have hfinite (Y : Scheme.{u})
      {M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
      (e : M ≅ N) (h : HasFiniteConstantLocalModel Λ Y M) :
      HasFiniteConstantLocalModel Λ Y N := by
    obtain ⟨𝒰, h𝒰⟩ := h
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 i
    exact ⟨P, hP, ⟨((CondensedRing.upperStar Λ (𝒰.f i)).mapIso e).symm ≪≫ eP⟩⟩
  have hstrat (Y : Scheme.{u})
      {M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
      (e : M ≅ N) (h : IsFiniteConstantStratified Λ Y M) :
      IsFiniteConstantStratified Λ Y N := by
    obtain ⟨S, hS⟩ := h
    exact ⟨S, fun a ↦ hfinite (S.domain a)
      ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩
  unfold IsConstantModelConstructible at hM ⊢
  by_cases h : CompactSpace X ∧ QuasiSeparatedSpace X
  · rw [if_pos h] at hM ⊢
    exact hstrat X e hM
  · rw [if_neg h] at hM ⊢
    intro U hU
    exact hstrat U.toScheme ((CondensedRing.upperStar Λ U.ι).mapIso e) (hM U hU)

private theorem coproduct_isGE
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {I : Type*} [HasColimitsOfShape (Discrete I) (DerivedCategory A)]
    [HasColimitsOfShape (Discrete I) A]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    (K : I → DerivedCategory A) (a : ℤ)
    (hK : ∀ i, (K i).IsGE a) : (∐ K).IsGE a := by
  apply (DerivedCategory.isGE_iff (∐ K) a).2
  intro q hq
  exact (isColimitOfPreserves (DerivedCategory.homologyFunctor A q)
    (coproductIsCoproduct K)).isZero_pt
    (Functor.isZero _ fun i ↦ (DerivedCategory.isGE_iff (K i.as) a).1 (hK i.as) q hq)

private theorem truncGE_preservesCoproducts
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {I : Type*} [HasColimitsOfShape (Discrete I) (DerivedCategory A)]
    [HasColimitsOfShape (Discrete I) A]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    (a : ℤ) :
    PreservesColimitsOfShape (Discrete I) ((DerivedCategory.TStructure.t (C := A)).truncGE a) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let T := t.truncGE a
  let π := t.truncGEπ a
  have hK (K : I → DerivedCategory A) : PreservesColimit (Discrete.functor K) T := by
    let L := fun i ↦ T.obj (K i)
    have : (∐ L).IsGE a := coproduct_isGE L a (fun i ↦ inferInstance)
    let f : ∐ K ⟶ ∐ L := Sigma.desc (fun i ↦ π.app (K i) ≫ Sigma.ι L i)
    let r : T.obj (∐ K) ⟶ ∐ L := t.descTruncGE f a
    let c := sigmaComparison T K
    have hc : IsIso c := by
      refine ⟨⟨r, ?_, ?_⟩⟩
      · apply Sigma.hom_ext
        intro i
        change Sigma.ι L i ≫ (c ≫ r) = Sigma.ι L i ≫ 𝟙 _
        rw [← Category.assoc, ι_comp_sigmaComparison]
        apply t.from_truncGE_obj_ext
        simp only [Category.comp_id]
        rw [← Category.assoc]
        change (π.app (K i) ≫ T.map (Sigma.ι K i)) ≫ r =
          π.app (K i) ≫ Sigma.ι L i
        rw [← π.naturality (Sigma.ι K i)]
        change (Sigma.ι K i ≫ (t.truncGEπ a).app (∐ K)) ≫ t.descTruncGE f a = _
        rw [Category.assoc, t.π_descTruncGE, Sigma.ι_desc]
      · apply t.from_truncGE_obj_ext
        dsimp only [r]
        rw [← Category.assoc, t.π_descTruncGE]
        apply Sigma.hom_ext
        intro i
        change Sigma.ι K i ≫ f ≫ c = Sigma.ι K i ≫ π.app (∐ K) ≫ 𝟙 _
        calc
          _ = π.app (K i) ≫ (Sigma.ι L i ≫ c) := by simp [f]
          _ = π.app (K i) ≫ T.map (Sigma.ι K i) := by
            rw [ι_comp_sigmaComparison]
          _ = _ := by simpa using (π.naturality (Sigma.ι K i)).symm
    exact PreservesCoproduct.of_iso_comparison T K
  let : ∀ K : I → DerivedCategory A, PreservesColimit (Discrete.functor K) T := hK
  exact preservesColimitsOfShape_of_discrete T

private theorem truncLE_preservesCoproducts
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {I : Type*} [HasColimitsOfShape (Discrete I) (DerivedCategory A)]
    [HasColimitsOfShape (Discrete I) A]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    (a : ℤ) :
    PreservesColimitsOfShape (Discrete I) ((DerivedCategory.TStructure.t (C := A)).truncLE a) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let T := t.truncLE a
  let ι := t.truncLEι a
  have hK (K : I → DerivedCategory A) : PreservesColimit (Discrete.functor K) T := by
    let L := fun i ↦ T.obj (K i)
    have : (∐ L).IsLE a := by
      apply (DerivedCategory.isLE_iff (∐ L) a).2
      intro q hq
      exact (isColimitOfPreserves (DerivedCategory.homologyFunctor A q)
        (coproductIsCoproduct L)).isZero_pt
        (Functor.isZero _ fun i ↦ DerivedCategory.isZero_of_isLE (L i.as) a q hq)
    let f : ∐ L ⟶ ∐ K := Sigma.desc (fun i ↦ ι.app (K i) ≫ Sigma.ι K i)
    let c := sigmaComparison T K
    have hcf : c ≫ ι.app (∐ K) = f := by
      apply Sigma.hom_ext
      intro i
      rw [← Category.assoc, ι_comp_sigmaComparison]
      simpa only [f, Sigma.ι_desc, Functor.id_map] using ι.naturality (Sigma.ι K i)
    -- The canonical truncation triangle supplies the other half of the coproduct.
    -- Prove invertibility by testing cohomology, where truncation retains a degree or zero.
    have hc : IsIso c := by
      apply (DerivedCategory.isIso_iff A c).2
      intro n
      by_cases hn : n ≤ a
      · have hι : IsIso ((DerivedCategory.homologyFunctor A n).map (ι.app (∐ K))) :=
          DerivedCategory.isIso_homologyFunctor_map_truncLTι_app _ _ _ (by omega)
        have hi (i : I) : IsIso
            ((DerivedCategory.homologyFunctor A n).map (ι.app (K i))) :=
          DerivedCategory.isIso_homologyFunctor_map_truncLTι_app _ _ _ (by omega)
        have hf : IsIso ((DerivedCategory.homologyFunctor A n).map f) := by
          let H := DerivedCategory.homologyFunctor A n
          have heq : H.map f = inv (sigmaComparison H L) ≫
              Limits.Sigma.map (fun i ↦ H.map (ι.app (K i))) ≫ sigmaComparison H K := by
            apply (cancel_epi (sigmaComparison H L)).1
            apply Sigma.hom_ext
            intro i
            simp only [ι_comp_sigmaComparison_assoc, IsIso.hom_inv_id_assoc,
              Sigma.ι_map_assoc]
            rw [← H.map_comp, Sigma.ι_desc, H.map_comp]
            change H.map (ι.app (K i)) ≫ H.map (Sigma.ι K i) =
              H.map (ι.app (K i)) ≫ Sigma.ι (fun i ↦ H.obj (K i)) i ≫ sigmaComparison H K
            rw [ι_comp_sigmaComparison]
          rw [heq]
          infer_instance
        have heq : (DerivedCategory.homologyFunctor A n).map c ≫
            (DerivedCategory.homologyFunctor A n).map (ι.app (∐ K)) =
            (DerivedCategory.homologyFunctor A n).map f := by
          rw [← Functor.map_comp, hcf]
        have : IsIso ((DerivedCategory.homologyFunctor A n).map c ≫
            (DerivedCategory.homologyFunctor A n).map (ι.app (∐ K))) := by
          rw [heq]
          exact hf
        exact IsIso.of_isIso_comp_right
          ((DerivedCategory.homologyFunctor A n).map c)
          ((DerivedCategory.homologyFunctor A n).map (ι.app (∐ K)))
      · have hz₁ := DerivedCategory.isZero_of_isLE (∐ L) a n (by omega)
        have hz₂ := DerivedCategory.isZero_of_isLE (T.obj (∐ K)) a n (by omega)
        exact isIso_of_source_target_iso_zero _ hz₁.isoZero hz₂.isoZero
    exact PreservesCoproduct.of_iso_comparison T K
  let : ∀ K : I → DerivedCategory A, PreservesColimit (Discrete.functor K) T := hK
  exact preservesColimitsOfShape_of_discrete T


open Classical in
/-- The canonical additive map from the direct sum of Hom groups, induced by the
coprojections of the specified ambient cofan. On a finitely supported tuple it sums
the composites with those coprojections.
Source: blueprint sk-thm-constructible-compactness, displayed comparison
(blueprint: sk-thm-constructible-compactness). -/
noncomputable def constructibleCompactnessComparison
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {I : Type t} (C : DerivedCategory A) (K : I → DerivedCategory A) (c : Cofan K) :
    (⨁ i : I, (C ⟶ K i)) →+ (C ⟶ c.pt) :=
  DirectSum.toAddMonoid fun i ↦ Preadditive.rightComp C (c.inj i)

open Classical in
private theorem comparison_bijective_of_equiv
    {B : Type u} [Category.{v} B] [Preadditive B]
    {I : Type w} (C : B) (K L : I → B) (c : Cofan K) (d : Cofan L)
    (e : ∀ i, (C ⟶ K i) ≃+ (C ⟶ L i))
    (eS : (C ⟶ c.pt) ≃+ (C ⟶ d.pt))
    (hnat : ∀ i f, eS (f ≫ c.inj i) = e i f ≫ d.inj i)
    (h : Function.Bijective
      (DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp C (d.inj i)))) :
    Function.Bijective
      (DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp C (c.inj i))) := by
  classical
  let a := DirectSum.map (fun i ↦ (e i).toAddMonoidHom)
  have ha : Function.Bijective a :=
    ⟨(DirectSum.map_injective _).2 (fun i ↦ (e i).injective),
      (DirectSum.map_surjective _).2 (fun i ↦ (e i).surjective)⟩
  have heq : (DirectSum.toAddMonoid (fun i ↦
      Preadditive.rightComp C (d.inj i))).comp a =
      eS.toAddMonoidHom.comp
        (DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp C (c.inj i))) := by
    apply DirectSum.addHom_ext
    intro i f
    simp only [AddMonoidHom.comp_apply, a, DirectSum.map_of,
      DirectSum.toAddMonoid_of]
    exact (hnat i f).symm
  have hb := h.comp ha
  change Function.Bijective
    ((DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp C (d.inj i))).comp a) at hb
  rw [heq] at hb
  constructor
  · intro x y hxy
    exact hb.1 (congrArg eS hxy)
  · intro f
    obtain ⟨x, hx⟩ := hb.2 (eS f)
    exact ⟨x, eS.injective hx⟩

private noncomputable def right_comp_equiv
    {B : Type u} [Category.{v} B] [Preadditive B] (C : B) {M N : B} (e : M ≅ N) :
    (C ⟶ M) ≃+ (C ⟶ N) where
  toFun f := f ≫ e.hom
  invFun f := f ≫ e.inv
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := by simp only [Preadditive.add_comp]

private theorem finite_window_comparison
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCoproducts.{t} (DerivedCategory A)]
    [HasCoproducts.{t} A]
    [∀ (I : Type t) (n : ℤ),
      PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    (C : A) (P : ObjectProperty (DerivedCategory A)) (d : ℕ)
    (hwindow : FiniteWindowAssertions C P d 0)
    (hsum : ∀ (I : Type t) (K : I → _) (c : Cofan K), IsColimit c →
      (∀ i, P (K i)) → P c.pt)
    (htrunc : ∀ K n, P K →
      P ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
      P ((DerivedCategory.TStructure.t.truncGE n).obj K))
    (hbounded : ∀ (a b : ℤ), a ≤ b → ∀ (I : Type t) (K : I → _),
      (∀ i, P (K i)) →
      (∀ i n, n < a ∨ b < n → IsZero ((DerivedCategory.homologyFunctor A n).obj (K i))) →
      ∃ (c : Cofan K) (_ : IsColimit c),
        Function.Bijective (constructibleBoundedComparison C K c 0))
    (I : Type t) (K : I → _) (hK : ∀ i, P (K i)) (c : Cofan K) (hc : IsColimit c) :
    Function.Bijective
      (constructibleCompactnessComparison ((DerivedCategory.singleFunctor A 0).obj C) K c) := by
  classical
  let B := DerivedCategory A
  let C₀ := (DerivedCategory.singleFunctor A 0).obj C
  let F : B ⥤ B := DerivedCategory.TStructure.t.truncLE 0 ⋙
    DerivedCategory.TStructure.t.truncGE (0 - (d : ℤ))
  have : PreservesColimitsOfShape (Discrete I)
      ((DerivedCategory.TStructure.t (C := A)).truncLE 0) := truncLE_preservesCoproducts 0
  have : PreservesColimitsOfShape (Discrete I)
      ((DerivedCategory.TStructure.t (C := A)).truncGE (0 - (d : ℤ))) :=
    truncGE_preservesCoproducts _
  let L := fun i ↦ F.obj (K i)
  have hL : ∀ i, P (L i) := fun i ↦
    (htrunc _ _ ((htrunc _ 0 (hK i)).1)).2
  have hb : ∀ i n, n < 0 - (d : ℤ) ∨ 0 < n →
      IsZero ((DerivedCategory.homologyFunctor A n).obj (L i)) := by
    intro i n hn
    rcases hn with hn | hn
    · exact DerivedCategory.isZero_of_isGE (L i) (0 - (d : ℤ)) n hn
    · exact DerivedCategory.isZero_of_isLE (L i) 0 n hn
  obtain ⟨cL, hcL, hcomp⟩ := hbounded (0 - (d : ℤ)) 0 (by omega) I L hL hb
  let cF : Cofan L := Cofan.mk (F.obj c.pt) (fun i ↦ F.map (c.inj i))
  have hcF : IsColimit cF :=
    (Cofan.isColimitMapCoconeEquiv F K c).toFun (isColimitOfPreserves F hc)
  let f : F.obj c.pt ≅ cL.pt := hcF.coconePointUniqueUpToIso hcL
  obtain ⟨e, _, hnat⟩ := hwindow
  let c₀ : Cofan (fun i ↦ (K i)⟦(0 : ℤ)⟧) :=
    Cofan.mk (c.pt⟦(0 : ℤ)⟧) (fun i ↦ (c.inj i)⟦(0 : ℤ)⟧')
  let cL₀ : Cofan (fun i ↦ (L i)⟦(0 : ℤ)⟧) :=
    Cofan.mk (cL.pt⟦(0 : ℤ)⟧) (fun i ↦ (cL.inj i)⟦(0 : ℤ)⟧')
  have hcomp₀ : Function.Bijective (constructibleBoundedComparison C K c 0) := by
    apply comparison_bijective_of_equiv C₀ _ _ c₀ cL₀
      (fun i ↦ e ⟨K i, hK i⟩)
      ((e ⟨c.pt, hsum I K c hc hK⟩).trans
        (right_comp_equiv C₀ ((shiftFunctor B (0 : ℤ)).mapIso f))) ?_ hcomp
    intro i g
    change (e ⟨c.pt, hsum I K c hc hK⟩ (g ≫ (c.inj i)⟦(0 : ℤ)⟧')) ≫
      f.hom⟦(0 : ℤ)⟧' = e ⟨K i, hK i⟩ g ≫ (cL.inj i)⟦(0 : ℤ)⟧'
    rw [hnat ⟨K i, hK i⟩ ⟨c.pt, hsum I K c hc hK⟩ (c.inj i) g]
    rw [Category.assoc, ← Functor.map_comp]
    congr 1
    exact congrArg (fun q ↦ (shiftFunctor B (0 : ℤ)).map q)
      (hcF.comp_coconePointUniqueUpToIso_hom hcL ⟨i⟩)
  apply comparison_bijective_of_equiv C₀ K _ c c₀
    (fun i ↦ right_comp_equiv C₀ ((shiftFunctorZero B ℤ).symm.app (K i)))
    (right_comp_equiv C₀ ((shiftFunctorZero B ℤ).symm.app c.pt)) ?_ hcomp₀
  intro i g
  change (g ≫ c.inj i) ≫ (shiftFunctorZero B ℤ).inv.app c.pt =
    (g ≫ (shiftFunctorZero B ℤ).inv.app (K i)) ≫ (c.inj i)⟦(0 : ℤ)⟧'
  simpa only [Category.assoc, Functor.id_map] using
    congrArg (fun q ↦ g ≫ q) ((shiftFunctorZero B ℤ).inv.naturality (c.inj i))

/-- The two compactness assertions for a specified condensed coefficient ring.
The first is compactness in the full localizing closure of Dbc, using the recorded
compact-object definition. The second uses ambient Hom groups and ambient coproducts
for every small family with ind-constructible cohomology, without a common bound.
Existence of the coproduct cofan is included, so no coproduct choice is assumed.
Any other coproduct gives the same comparison through its unique compatible isomorphism.
Source: blueprint sk-thm-constructible-compactness, both assertions
(blueprint: sk-thm-constructible-compactness). -/
def HasConstructibleCompactness
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) : Prop :=
  (∃ _ : HasCoproducts.{u + 1}
      (localizingClosure (constantModelBoundedConstructible Λ X)).FullSubcategory,
    ∀ C : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      constantModelBoundedConstructible Λ X C →
      ∃ hC : localizingClosure (constantModelBoundedConstructible Λ X) C,
        IsCompactObject.{u + 1}
          (ObjectProperty.FullSubcategory.mk C hC)) ∧
  (∀ (C : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
    constantModelBoundedConstructible Λ X C →
    ∀ (I : Type (u + 1))
      (K : I → DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      (∀ (i : I) (n : ℤ), ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ n).obj (K i))) →
      ∃ (c : Cofan K) (_ : IsColimit c),
        Function.Bijective (constructibleCompactnessComparison C K c))

private theorem constructible_compactness_of_sheaves
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (T : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    [T.IsTriangulated] [T.IsClosedUnderIsomorphisms]
    (hsum : ∀ (I : Type (u + 1)) (K : I → _) (c : Cofan K), IsColimit c →
      (∀ i, T (K i)) → T c.pt)
    (hL : localizingClosure (constantModelBoundedConstructible Λ X) ≤ T)
    (hT : ∀ K, T K ↔ ∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible Λ X) ((DerivedCategory.homologyFunctor _ n).obj K))
    (hsheaf : ∀ M, IsConstantModelConstructible Λ X M →
      ∃ _hM : T ((DerivedCategory.singleFunctor _ 0).obj M),
        ∀ (I : Type (u + 1)) (K : I → _) (_hK : ∀ i, T (K i))
          (c : Cofan K), IsColimit c →
          Function.Bijective
            (constructibleCompactnessComparison ((DerivedCategory.singleFunctor _ 0).obj M)
              K c)) : HasConstructibleCompactness Λ X := by
  classical
  let S := constantModelBoundedConstructible Λ X
  obtain ⟨hcop, _, _, hloc, hS, _⟩ := localizingClosure_exists Λ X S
  let := hcop
  let (I : Type (u + 1)) : T.IsClosedUnderColimitsOfShape (Discrete I) :=
    closed_under_coproducts T hsum I
  let : HasCoproducts.{u + 1} T.FullSubcategory := fun I ↦
    hasColimitsOfShape_of_closedUnderColimits (Discrete I) T
  let P : ObjectProperty _ := IsConstantModelConstructible Λ X
  let : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ constant_model_iso Λ X e h⟩
  have hcompact (C) (hC : S C) :
      ∃ h : T C, IsCompactObject.{u + 1} (ObjectProperty.FullSubcategory.mk C h) := by
    apply compact_devissage P T ?_ C hC.1 hC.2
    intro M hM
    obtain ⟨hM', hMcomp⟩ := hsheaf M hM
    exact ⟨hM', (compact_iff_ambient T ⟨_, hM'⟩).2 hMcomp⟩
  have hamb (C) (hC : S C) (I : Type (u + 1)) (K : I → _)
      (hK : ∀ i, T (K i)) (c : Cofan K) (hc : IsColimit c) :
      Function.Bijective (constructibleCompactnessComparison C K c) := by
    obtain ⟨hC', hCc⟩ := hcompact C hC
    exact (compact_iff_ambient T ⟨C, hC'⟩).1 hCc I K hK c hc
  let L := localizingClosure S
  let : L.IsClosedUnderIsomorphisms := hloc.2.1
  let (I : Type (u + 2)) : L.IsClosedUnderColimitsOfShape (Discrete I) := by
    apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
    rintro _ ⟨F, hF⟩
    exact hloc.2.2 F inferInstance (fun i ↦ hF ⟨i⟩)
  let (I : Type (u + 1)) : L.IsClosedUnderColimitsOfShape (Discrete I) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
      (Discrete.equivalence (Equiv.ulift : ULift.{u + 2} I ≃ I))
  let : HasCoproducts.{u + 1} L.FullSubcategory := fun I ↦
    hasColimitsOfShape_of_closedUnderColimits (Discrete I) L
  constructor
  · refine ⟨inferInstance, fun C hC ↦ ⟨hS C hC, ?_⟩⟩
    apply (compact_iff_ambient L ⟨C, hS C hC⟩).2
    intro I K hK c hc
    exact hamb C hC I K (fun i ↦ hL _ (hK i)) c hc
  · intro C hC I K hK
    exact ⟨_, coproductIsCoproduct K,
      hamb C hC I K (fun i ↦ (hT _).2 (hK i)) _ (coproductIsCoproduct K)⟩

private theorem constructible_compactness_of_window
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (T : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    [T.IsTriangulated] [T.IsClosedUnderIsomorphisms]
    (hsum : ∀ (I : Type (u + 1)) (K : I → _) (c : Cofan K), IsColimit c →
      (∀ i, T (K i)) → T c.pt)
    (hL : localizingClosure (constantModelBoundedConstructible Λ X) ≤ T)
    (hT : ∀ K, T K ↔ ∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible Λ X) ((DerivedCategory.homologyFunctor _ n).obj K))
    (htrunc : ∀ K n, T K →
      T ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
      T ((DerivedCategory.TStructure.t.truncGE n).obj K))
    (hwindow : ∀ C, IsConstantModelConstructible Λ X C →
      ∃ d : ℕ, FiniteWindowAssertions C T d 0)
    (hbounded : ∀ C, IsConstantModelConstructible Λ X C → ∀ (a b : ℤ), a ≤ b →
      ∀ (I : Type (u + 1)) (K : I → _), (∀ i, T (K i)) →
      (∀ i n, n < a ∨ b < n → IsZero ((DerivedCategory.homologyFunctor _ n).obj (K i))) →
      ∃ (c : Cofan K) (_ : IsColimit c),
        Function.Bijective (constructibleBoundedComparison C K c 0)) :
    HasConstructibleCompactness Λ X := by
  classical
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let : IsGrothendieckAbelian.{u + 1} A := Mod.isGrothendieckAbelian _
  let : Abelian.HasKInjectiveResolutions A :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{u + 1}
  let : HasColimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasColimits A
  let : HasCoproducts.{u + 1} A := fun I ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete I)
  let : HasCoproducts.{u + 1} (DerivedCategory A) :=
    (localizingClosure_exists Λ X (constantModelBoundedConstructible Λ X)).1
  let P : ObjectProperty A := IsConstantModelConstructible Λ X
  apply constructible_compactness_of_sheaves Λ X T hsum hL hT
  intro C hC
  have hsingle : T ((DerivedCategory.singleFunctor A 0).obj C) := by
    apply (hT _).2
    intro n
    by_cases hn : n = 0
    · subst n
      exact (ObjectProperty.ind P).prop_of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app C).symm
        (ObjectProperty.le_ind P C hC)
    · have hz : IsZero ((DerivedCategory.homologyFunctor A n).obj
          ((DerivedCategory.singleFunctor A 0).obj C)) := by
        rcases lt_or_gt_of_ne hn with hn | hn
        · exact DerivedCategory.isZero_of_isGE _ 0 n hn
        · exact DerivedCategory.isZero_of_isLE _ 0 n hn
      exact (ObjectProperty.ind P).prop_of_iso
        (((DerivedCategory.homologyFunctor A n).map_isZero
          (isZero_zero (DerivedCategory A))).iso hz)
        ((hT _).1 T.prop_zero n)
  refine ⟨hsingle, ?_⟩
  obtain ⟨d, hd⟩ := hwindow C hC
  intro I K hK c hc
  exact finite_window_comparison C T d hd hsum htrunc (hbounded C hC) I K hK c hc

private theorem subsingleton_ext_standard
    {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
    (C N : A) (r : ℕ) (h : Subsingleton (Abelian.Ext.{w} C N r)) :
    Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard A) C N r) := by
  let : HasExt.{max u v} A := HasExt.standard A
  exact (Abelian.Ext.chgUniv.{w, max u v} (X := C) (Y := N) (n := r)).injective.subsingleton

private theorem uniform_ext_standard
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    (C : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj Λ) X))
    (hC : IsConstantModelConstructible (coefficientHeartRingObj Λ) X C) :
    ∃ d : ℕ, ∀ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (coefficientHeartRingObj Λ) X),
      IsConstantModelConstructible (coefficientHeartRingObj Λ) X N →
      ∀ r : ℕ, d < r →
        Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C N r) := by
  obtain ⟨d, hd⟩ := (uniformConstructibleExt D ℓ hℓ Λ hΛ D.k
    (Or.inr ⟨RingEquiv.refl _⟩) X).1 ⟨C, hC⟩
  refine ⟨d, fun N hN r hr ↦ ?_⟩
  exact subsingleton_ext_standard C N r (hd ⟨N, hN⟩ r hr)

private theorem datum_charP (D : WeilConjectures.FiniteFieldDatum.{u}) : CharP D.k D.p := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq])
  exact charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p

/-- Every bounded constructible complex is compact in the localizing closure of Dbc;
its ambient Hom functor also commutes with every small coproduct of Dic objects.
Both rational coefficient choices are asserted, with their canonical ring structures.
Here `PadicAlgCl ℓ` is the fixed algebraic closure, and `E` ranges over all its finite
intermediate fields; this is the coefficient convention of sk-def-sfb-qlbar-condensed.
Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-constructible-compactness, statement and proof; Stacks Tags 09QH and 08J5
(blueprint: sk-thm-constructible-compactness).

Proof plan, for each of the two coefficient rings:
1. Use only the ordinary layer-(B) ambient category of sk-def-sfb-derived-categories.
   By det-ambient-ind-derived-triangulated, Dic is a full triangulated subcategory.
   By det-ambient-ind-derived-sums it contains Dbc and its localizing closure and
   is closed under ambient small sums and both truncations. The sums exist and are
   termwise by det-def-localizing-closure-existence. Fullness gives the same Hom
   groups and coproducts internally, so def-pc-compact-object is exactly the Hom
   comparison for every family in Dic.
2. For a constructible sheaf C, choose the nonnegative bound d_C of
   sk-lem-uniform-constructible-ext and set T_C = tau_ge_(-d_C) tau_le_0.
   The canonical map from the sum of T_C(K_i) to T_C(sum K_i) induces the identity
   on cohomology in [-d_C,0], and zero-to-zero outside. This uses def-kun-truncations
   and cohomology commuting with sums from det-ambient-ind-derived-sums. On complex
   representatives the map is induced by the truncated coprojections, so it is a
   quasi-isomorphism and is inverted by def-weil-abstract-derived-category.
3. Apply sk-lem-finite-window with m=0 to each K_i and their sum. Naturality and
   step 2 identify their Hom comparison with the comparison for the family T_C(K_i).
   This family has the common interval [-d_C,0]. Apply
   det-constructible-compactness-bounded with a=-d_C, b=0 and s=0 to make this
   comparison bijective. Thus C is compact in Dic for all families, including
   families with no common bound.
4. Compact objects of Dic are closed under shifts and triangles by
   lem-sc-compact-objects-thick (Tag 09QH). For bounded constructible C choose
   [a,b] containing its cohomology. The successive triangles of
   lem-weil-pbc-truncation-triangle have third term H^n(C)[-n], which is compact
   by step 3 and shift closure. The formulas of def-kun-truncations identify
   tau_le_(a-1) C with zero and tau_le_b C with C. Finite induction on the
   truncations therefore proves compactness for C.
5. Apply det-def-localizing-closure-existence to the actual class Dbc, rather than
   Dctf. By det-ambient-ind-derived-sums its closure is in Dic. Fullness and closure
   under ambient sums make the comparison of step 4 the internal compactness
   comparison in this localizing closure too. -/
theorem constructible_compactness
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    HasConstructibleCompactness (Profinite.continuousMapRingObj E) X ∧
      HasConstructibleCompactness (Profinite.padicAlgClRingObj ℓ) X := by
  let : CharP D.k D.p := datum_charP D
  let TE : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) X))) := fun K ↦
    ∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
      ((DerivedCategory.homologyFunctor _ n).obj K)
  let TQ : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))) := fun K ↦
    ∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
      ((DerivedCategory.homologyFunctor _ n).obj K)
  obtain ⟨hTE, hTQ⟩ := indConstructibleDerived_isTriangulated
    ℓ E D.k D.p D.prime.pos hℓ.symm X
  obtain ⟨hIE, hIQ⟩ := indConstructibleDerived_isClosedUnderIsomorphisms
    ℓ E D.k D.p D.prime.pos hℓ.symm X
  let : TE.IsTriangulated := hTE
  let : TQ.IsTriangulated := hTQ
  let : TE.IsClosedUnderIsomorphisms := hIE
  let : TQ.IsClosedUnderIsomorphisms := hIQ
  obtain ⟨_, hsumE, htruncE, _, hLE⟩ := indConstructibleDerived_sums_and_truncations
    ℓ E D.k D.p D.prime.pos hℓ.symm X
  obtain ⟨_, hsumQ, htruncQ, _, hLQ⟩ :=
    indConstructibleDerived_sums_and_truncations_padicAlgCl
      ℓ D.k D.p D.prime.pos hℓ.symm X
  constructor
  · apply constructible_compactness_of_window (Profinite.continuousMapRingObj E) X
      TE hsumE hLE (fun _ ↦ Iff.rfl) htruncE
    · intro C hC
      obtain ⟨d, hd⟩ := uniform_ext_standard D ℓ hℓ
        (Profinite.padicSubfieldCondensedRing ℓ E) (Or.inl ⟨E.1, E.2, rfl⟩) X C hC
      exact ⟨d, finiteWindow ℓ E X C hC d hd 0⟩
    · intro C hC a b hab I K hK hb
      have h := constructible_compactness_bounded
        ℓ E D.k D.p D.prime.pos hℓ.symm X C hC a b hab I K hK hb
      exact h.imp (fun _ h ↦ h.imp (fun _ hs ↦ hs 0))
  · apply constructible_compactness_of_window (Profinite.padicAlgClRingObj ℓ) X
      TQ hsumQ hLQ (fun _ ↦ Iff.rfl) htruncQ
    · intro C hC
      obtain ⟨d, hd⟩ := uniform_ext_standard D ℓ hℓ
        (Profinite.padicAlgClCondensedRing ℓ) (Or.inr rfl) X C hC
      exact ⟨d, finiteWindow_padicAlgCl ℓ X C hC d hd 0⟩
    · intro C hC a b hab I K hK hb
      have h := constructible_compactness_bounded_padicAlgCl
        ℓ D.k D.p D.prime.pos hℓ.symm X C hC a b hab I K hK hb
      exact h.imp (fun _ h ↦ h.imp (fun _ hs ↦ hs 0))

end AlgebraicGeometry.ProEtale
