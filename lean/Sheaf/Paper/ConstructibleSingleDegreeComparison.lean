/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.Paper.DetIndHeartIISums
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Mathlib.CategoryTheory.Shift.Localization

/-!
# The single-cohomology-degree base case of bounded compactness

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-constructible-compactness/sk-thm-constructible-compactness-bounded.md,
proof, base case a=b (blueprint: det-constructible-single-degree-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits DirectSum
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open CategoryTheory.Functor

private noncomputable def functorSumComparison
    {D : Type*} [Category* D] (F : D ⥤ AddCommGrpCat.{u + 1})
    {J : Type*} {K : J → D} (c : Cofan K) :
    (⨁ j, F.obj (K j)) →+ F.obj c.pt := by
  classical
  exact DirectSum.toAddMonoid fun j ↦ (F.map (c.inj j)).hom

private lemma functorSumComparison_naturality
    {D : Type*} [Category* D] (F : D ⥤ AddCommGrpCat.{u + 1})
    {J : Type*} {K L : J → D} (c : Cofan K) (d : Cofan L)
    (f : ∀ j, K j ⟶ L j) (g : c.pt ⟶ d.pt)
    (h : ∀ j, c.inj j ≫ g = f j ≫ d.inj j) :
    (F.map g).hom.comp (functorSumComparison F c) =
      (functorSumComparison F d).comp (DirectSum.map fun j ↦ (F.map (f j)).hom) := by
  classical
  apply DirectSum.addHom_ext
  intro j x
  simp only [AddMonoidHom.comp_apply, functorSumComparison, DirectSum.toAddMonoid_of,
    DirectSum.map_of]
  change F.map g (F.map (c.inj j) x) = F.map (d.inj j) (F.map (f j) x)
  simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using
    congrArg (fun z ↦ z x) (congrArg F.map (h j))

private lemma functorSumComparison_iso
    {D : Type*} [Category* D] (F : D ⥤ AddCommGrpCat.{u + 1})
    {J : Type*} {K L : J → D} (c : Cofan K) (d : Cofan L)
    (e : ∀ j, K j ≅ L j) (e' : c.pt ≅ d.pt)
    (h : ∀ j, c.inj j ≫ e'.hom = (e j).hom ≫ d.inj j)
    (hd : Function.Bijective (functorSumComparison F d)) :
    Function.Bijective (functorSumComparison F c) := by
  classical
  have he : ∀ j, Function.Bijective ((F.map (e j).hom).hom) := fun j ↦
    ⟨fun x y hxy ↦ by
      have := congrArg (fun z ↦ F.map (e j).inv z) hxy
      simpa only [← ConcreteCategory.comp_apply, ← F.map_comp, Iso.hom_inv_id,
        F.map_id, ConcreteCategory.id_apply] using this,
      fun y ↦ ⟨F.map (e j).inv y, by
        simp only [← ConcreteCategory.comp_apply, ← F.map_comp, Iso.inv_hom_id,
          F.map_id, ConcreteCategory.id_apply]⟩⟩
  have hi : Function.Injective ((F.map e'.hom).hom) := by
    intro x y hxy
    have := congrArg (fun z ↦ F.map e'.inv z) hxy
    simpa only [← ConcreteCategory.comp_apply, ← F.map_comp, Iso.hom_inv_id,
      F.map_id, ConcreteCategory.id_apply] using this
  have hb := hd.comp (show Function.Bijective
      (DirectSum.map fun j ↦ (F.map (e j).hom).hom) from
    ⟨(DirectSum.map_injective _).2 (fun j ↦ (he j).1),
      (DirectSum.map_surjective _).2 (fun j ↦ (he j).2)⟩)
  change Function.Bijective ((functorSumComparison F d).comp
    (DirectSum.map fun j ↦ (F.map (e j).hom).hom)) at hb
  rw [← show (F.map e'.hom).hom.comp (functorSumComparison F c) =
    (functorSumComparison F d).comp (DirectSum.map fun j ↦ (F.map (e j).hom).hom) from
      functorSumComparison_naturality F c d (fun j ↦ (e j).hom) e'.hom h] at hb
  change Function.Bijective ((F.map e'.hom).hom ∘ functorSumComparison F c) at hb
  exact hb.of_comp_left hi

private lemma functorSumComparison_natIso
    {D : Type*} [Category* D] {F G : D ⥤ AddCommGrpCat.{u + 1}}
    (e : F ≅ G) {J : Type*} {K : J → D} (c : Cofan K)
    (hG : Function.Bijective (functorSumComparison G c)) :
    Function.Bijective (functorSumComparison F c) := by
  let cF : Cofan (fun j ↦ F.obj (K j)) :=
    Cofan.mk (F.obj c.pt) (fun j ↦ F.map (c.inj j))
  let cG : Cofan (fun j ↦ G.obj (K j)) :=
    Cofan.mk (G.obj c.pt) (fun j ↦ G.map (c.inj j))
  exact functorSumComparison_iso (𝟭 _) cF cG (fun j ↦ e.app (K j))
    (e.app c.pt) (fun j ↦ e.hom.naturality (c.inj j)) hG

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def localizationHomFunctorIso
    {A D₁ D₂ : Type*} [Category* A] [Category.{u + 1} D₁] [Category.{u + 1} D₂]
    [Preadditive D₁] [Preadditive D₂] [HasBinaryBiproducts D₁] [HasBinaryBiproducts D₂]
    [HasShift A ℤ] [HasShift D₁ ℤ] [HasShift D₂ ℤ]
    (W : MorphismProperty A) [W.IsCompatibleWithShift ℤ]
    (Q₁ : A ⥤ D₁) (Q₂ : A ⥤ D₂) [Q₁.IsLocalization W] [Q₂.IsLocalization W]
    [Q₁.CommShift ℤ] [Q₂.CommShift ℤ]
    {B : Type*} [Category* B] (S : B ⥤ A) (C : A) (q : ℤ) :
    (S ⋙ Q₁ ⋙ shiftFunctor D₁ q ⋙ preadditiveCoyoneda.obj (Opposite.op (Q₁.obj C))) ≅
    (S ⋙ Q₂ ⋙ shiftFunctor D₂ q ⋙ preadditiveCoyoneda.obj (Opposite.op (Q₂.obj C))) := by
  let e := Localization.uniq Q₁ Q₂ W
  let E := e.functor
  let α := Localization.compUniqFunctor Q₁ Q₂ W
  let : E.Additive := E.additive_of_preserves_binary_products
  let : E.CommShift ℤ := Functor.commShiftOfLocalization Q₁ W ℤ Q₂ E
  let β : S ⋙ Q₁ ⋙ shiftFunctor D₁ q ⋙ E ≅ S ⋙ Q₂ ⋙ shiftFunctor D₂ q :=
    isoWhiskerLeft S (isoWhiskerLeft Q₁ (E.commShiftIso q) ≪≫
      (Functor.associator Q₁ E (shiftFunctor D₂ q)).symm ≪≫
      isoWhiskerRight α (shiftFunctor D₂ q))
  let φ (Y : B) : (Q₁.obj C ⟶ (Q₁.obj (S.obj Y))⟦q⟧) →+
      (Q₂.obj C ⟶ (Q₂.obj (S.obj Y))⟦q⟧) :=
    (Preadditive.leftComp _ (α.inv.app C)).comp
      ((Preadditive.rightComp _ (β.hom.app Y)).comp E.mapAddHom)
  have hφ (Y : B) : Function.Bijective (φ Y) := by
    have hE := (Functor.FullyFaithful.ofFullyFaithful E).map_bijective
      (Q₁.obj C) ((Q₁.obj (S.obj Y))⟦q⟧)
    have hβ : Function.Bijective
        (fun f : E.obj (Q₁.obj C) ⟶ E.obj ((Q₁.obj (S.obj Y))⟦q⟧) ↦
          f ≫ β.hom.app Y) := (β.app Y).homToEquiv.bijective
    have hα : Function.Bijective
        (fun f : E.obj (Q₁.obj C) ⟶ (Q₂.obj (S.obj Y))⟦q⟧ ↦
          α.inv.app C ≫ f) := (α.app C).homFromEquiv.bijective
    exact hα.comp (hβ.comp hE)
  refine NatIso.ofComponents (fun Y ↦ (AddEquiv.ofBijective (φ Y) (hφ Y)).toAddCommGrpIso) ?_
  intro Y Z f
  apply AddCommGrpCat.ext
  intro x
  change (Q₁.obj C ⟶ (Q₁.obj (S.obj Y))⟦q⟧) at x
  change α.inv.app C ≫ E.map (x ≫ (shiftFunctor D₁ q).map (Q₁.map (S.map f))) ≫
      β.hom.app Z =
    (α.inv.app C ≫ E.map x ≫ β.hom.app Y) ≫
      (shiftFunctor D₂ q).map (Q₂.map (S.map f))
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg (fun z ↦ α.inv.app C ≫ E.map x ≫ z) (β.hom.naturality f)

private noncomputable def singleHomToComplexIso
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{u + 1} A]
    (C : A) (q : ℤ) :
    (DerivedCategory.singleFunctor A 0 ⋙ shiftFunctor (DerivedCategory A) q ⋙
      preadditiveCoyoneda.obj (Opposite.op ((DerivedCategory.singleFunctor A 0).obj C))) ≅
    (CochainComplex.singleFunctor A 0 ⋙ DerivedCategory.Q ⋙
      shiftFunctor (DerivedCategory A) q ⋙ preadditiveCoyoneda.obj
        (Opposite.op (DerivedCategory.Q.obj ((CochainComplex.singleFunctor A 0).obj C)))) :=
  isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ A 0) _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (CochainComplex.singleFunctor A 0)
      (isoWhiskerLeft (DerivedCategory.Q (C := A))
        (isoWhiskerLeft (shiftFunctor (DerivedCategory A) q)
          (preadditiveCoyoneda.mapIso
            ((DerivedCategory.singleFunctorIsoCompQ A 0).app C).op).symm))

private noncomputable def cofanPointIso
    {D : Type*} [Category* D] {J : Type*} {K L : J → D}
    (c : Cofan K) (d : Cofan L) (hc : IsColimit c) (hd : IsColimit d)
    (e : ∀ j, K j ≅ L j) : c.pt ≅ d.pt where
  hom := hc.desc (Cofan.mk d.pt (fun j ↦ (e j).hom ≫ d.inj j))
  inv := hd.desc (Cofan.mk c.pt (fun j ↦ (e j).inv ≫ c.inj j))
  hom_inv_id := by
    apply hc.hom_ext
    intro ⟨j⟩
    simp [Category.assoc, Cofan.inj]
  inv_hom_id := by
    apply hd.hom_ext
    intro ⟨j⟩
    simp [Category.assoc, Cofan.inj]

open Classical in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxHeartbeats 200000 in
-- Resolving module-category colimits and the two localization presentations needs this budget.
/-- A family concentrated in a single degree has the Ext coproduct comparison.
Source: blueprint main-20261015, sk-thm-constructible-compactness-bounded,
proof, base case a=b, and its displayed Ext^(s-a) comparison
(blueprint: det-constructible-single-degree-comparison).

Proof: For each K_i, the canonical t-structure gives an isomorphism
K_i ≅ H^a(K_i)[-a]. This follows by representing K_i by a complex, applying
upper and lower canonical truncations, and noting that the resulting complex has
one nonzero term. The map on H^a is the identity. Form the coproduct of the
sheaves H^a(K_i). By isColimit_mapCocone_grothendieckSum, the localization
of their termwise single-complex coproduct is a derived coproduct. Hence the image under
the degree-zero single functor of the sheaf coproduct is that derived coproduct.
Shifts preserve coproducts, being equivalences. Transport the chosen cofan c
along the component isomorphisms and the unique compatible coproduct isomorphism.
The shifted Hom groups become Ext^(s-a)(C,H^a(K_i)). Apply det_ind_heart_ii_sums
at s-a. Every isomorphism used commutes with the coprojections, so the transported
homomorphism sends a summand f to its composite with the shifted coprojection,
exactly the displayed DirectSum.toAddMonoid. Transport bijectivity back along
these additive isomorphisms. This also covers negative shifts, zero cohomology
sheaves, and empty families; no boundedness induction is used. -/
theorem constructible_single_degree_comparison
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : Λ = Profinite.continuousMapRingObj E ∨ Λ = Profinite.padicAlgClRingObj ℓ)
    [HasDerivedCategory.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))]
    (C : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hC : IsConstantModelConstructible Λ X C)
    (a : ℤ) (I : Type (u + 1))
    (K : I → DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (c : Cofan K) (hc : IsColimit c)
    (hge : ∀ i, (K i).IsGE a) (hle : ∀ i, (K i).IsLE a)
    (hK : ∀ i, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
      ((DerivedCategory.homologyFunctor _ a).obj (K i))) (s : ℤ) :
    Function.Bijective
      (DirectSum.toAddMonoid (fun i ↦
        Preadditive.rightComp ((DerivedCategory.singleFunctor _ 0).obj C)
          ((shiftFunctor _ s).map (c.inj i)))) := by
  classical
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X)
  let : IsGrothendieckAbelian.{u + 1} A := Mod.isGrothendieckAbelian _
  let : HasColimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasColimits A
  let : HasCoproducts.{u + 1} A :=
    fun J ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  let B : I → A := fun i ↦ (DerivedCategory.homologyFunctor A a).obj (K i)
  have hzero (i : I) (q : ℤ) (hq : q ≠ a) :
      IsZero ((DerivedCategory.homologyFunctor A q).obj (K i)) := by
    by_cases hqa : q < a
    · let := hge i
      exact (DerivedCategory.isGE_iff (K i) a).1 inferInstance q hqa
    · have haq : a < q := lt_of_le_of_ne (le_of_not_gt hqa) hq.symm
      let := hle i
      exact (DerivedCategory.isLE_iff (K i) a).1 inferInstance q haq
  have hi (i : I) : Nonempty (K i ≅ (DerivedCategory.singleFunctor A a).obj (B i)) :=
    DerivedCategory.nonempty_iso_singleFunctor_obj_homologyFunctor_obj (K i) a
      (fun q hq ↦ hzero i q hq)
  let e (i : I) := Classical.choice (hi i)
  let cB : Cofan B := Cofan.mk (∐ B) (Sigma.ι B)
  have hcB : IsColimit cB := coproductIsCoproduct B
  let d : Cofan (fun i ↦ (DerivedCategory.singleFunctor A a).obj (B i)) :=
    Cofan.mk ((DerivedCategory.singleFunctor A a).obj cB.pt)
      (fun i ↦ (DerivedCategory.singleFunctor A a).map (cB.inj i))
  have hd : IsColimit d := by
    let S := CochainComplex.singleFunctor A a
    let L : I → CochainComplex A ℤ := fun i ↦ S.obj (B i)
    let : PreservesColimit (Discrete.functor L) (DerivedCategory.Q (C := A)) :=
      preservesColimit_of_preserves_colimit_cocone
        (HomologicalComplex.isColimitCoconeOfHasColimitEval (Discrete.functor L))
        (DerivedCategory.isColimit_mapCocone_grothendieckSum A I L).some
    let : PreservesColimit (Discrete.functor B) S := by
      change PreservesColimit (Discrete.functor B) (HomologicalComplex.single A (.up ℤ) a)
      infer_instance
    have hS := isColimitCofanMkObjOfIsColimit S B (fun i ↦ cB.inj i) hcB
    exact isColimitCofanMkObjOfIsColimit (DerivedCategory.Q (C := A)) L _ hS
  let F := preadditiveCoyoneda.obj
    (Opposite.op ((DerivedCategory.singleFunctor A 0).obj C))
  have hsum : Function.Bijective (functorSumComparison (F.shift s) d) := by
    let G := DerivedCategory.singleFunctor A a ⋙ F.shift s
    let H := DerivedCategory.singleFunctor A 0 ⋙ F.shift (s - a)
    let eF : G ≅ H := isoWhiskerRight
      ((DerivedCategory.singleFunctors A).shiftIso s (a - s) a (by omega) ≪≫
        ((DerivedCategory.singleFunctors A).shiftIso (s - a) (a - s) 0 (by omega)).symm) F
    change Function.Bijective (functorSumComparison G cB)
    apply functorSumComparison_natIso eF cB
    let D₁ := DerivedCategory A
    let : HasBinaryBiproducts D₁ := inferInstance
    let Q₁ := DerivedCategory.Q (C := A)
    let e₁ := singleHomToComplexIso C (s - a)
    let h₀ : HasDerivedCategory.{u + 1} A := HasDerivedCategory.ofIsGrothendieckAbelian A
    let := h₀
    let D₀ := @DerivedCategory A _ _ h₀
    let : HasBinaryBiproducts D₀ := inferInstance
    let Q₀ : CochainComplex A ℤ ⥤ D₀ := @DerivedCategory.Q A _ _ h₀
    let F₀ : D₀ ⥤ AddCommGrpCat.{u + 1} := preadditiveCoyoneda.obj
      (Opposite.op ((@DerivedCategory.singleFunctor A _ _ h₀ 0).obj C))
    let H₀ : A ⥤ AddCommGrpCat.{u + 1} :=
      @DerivedCategory.singleFunctor A _ _ h₀ 0 ⋙ shiftFunctor D₀ (s - a) ⋙ F₀
    have h₀sum : Function.Bijective (functorSumComparison H₀ cB) := by
      change Function.Bijective (DirectSum.toAddMonoid fun i ↦
        Preadditive.rightComp ((@DerivedCategory.singleFunctor A _ _ h₀ 0).obj C)
          ((shiftFunctor D₀ (s - a)).map
            ((@DerivedCategory.singleFunctor A _ _ h₀ 0).map (cB.inj i))))
      exact det_ind_heart_ii_sums ℓ E X Λ hΛ C hC (s - a) I B hK cB hcB
    let eH := @singleHomToComplexIso _ _ _ h₀ C (s - a) ≪≫
      localizationHomFunctorIso (HomologicalComplex.quasiIso A (.up ℤ))
        Q₀ Q₁ (CochainComplex.singleFunctor A 0)
        ((CochainComplex.singleFunctor A 0).obj C) (s - a) ≪≫
      e₁.symm
    exact functorSumComparison_natIso eH.symm cB h₀sum
  exact functorSumComparison_iso (F.shift s) c d e
    (cofanPointIso c d hc hd e)
    (fun i ↦ hc.fac (Cofan.mk d.pt (fun j ↦ (e j).hom ≫ d.inj j)) ⟨i⟩)
    hsum

end AlgebraicGeometry.ProEtale
