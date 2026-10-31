/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.BifunctorChainCurrying
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Localized signed currying into K-injective targets

Source: Stacks Project, Cohomology on Sites, Tags 0A96 and 08J9, with the row
Hom and left-first flipped total conventions of Tag 0A5Y's external adaptation.
(blueprint: lem-sf-kflat-bifunctor-kinjective-currying)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex

/-- Admissibility means that the left-first total with the fixed second complex
preserves all quasi-isomorphisms. This is the admissibility notion in the item,
without a boundedness or termwise flatness condition.
Source: Stacks 0A96, K-flat acyclic-total argument.
(blueprint: lem-sf-kflat-bifunctor-kinjective-currying) -/
def IsBifunctorTensorAdmissible
    {A : Type u} [Category.{v} A] [Abelian A] [HasCountableCoproducts A]
    (F : A ⥤ A ⥤ A) [F.Additive] [∀ X : A, (F.obj X).Additive]
    (T : CochainComplex A ℤ) : Prop :=
  ∀ {P P' : CochainComplex A ℤ} (f : P ⟶ P'), QuasiIso f →
    QuasiIso (HomologicalComplex.mapBifunctorMap f (𝟙 T) F.flip (.up ℤ))

open HomComplex

private lemma homComplexMap_delta
    {A : Type u} [Category.{v} A] [Abelian A]
    {P J N I : CochainComplex A ℤ}
    (e : HomComplex P J ≅ HomComplex N I) (r s : ℤ) (z : Cochain P J r) :
    δ r s (e.hom.f r z) = e.hom.f s (δ r s z) :=
  ConcreteCategory.congr_hom (e.hom.comm r s) z

private noncomputable def homComplexMap
    {A : Type u} [Category.{v} A] [Abelian A]
    {P J N I : CochainComplex A ℤ}
    (e : HomComplex P J ≅ HomComplex N I) (f : P ⟶ J) : N ⟶ I :=
  Cocycle.homOf (Cocycle.mk (e.hom.f 0 (Cochain.ofHom f)) 1 rfl (by
    rw [homComplexMap_delta, δ_ofHom, map_zero]))

@[simp] private lemma ofHom_homComplexMap
    {A : Type u} [Category.{v} A] [Abelian A]
    {P J N I : CochainComplex A ℤ}
    (e : HomComplex P J ≅ HomComplex N I) (f : P ⟶ J) :
    Cochain.ofHom (homComplexMap e f) = e.hom.f 0 (Cochain.ofHom f) := by
  simp [homComplexMap]

private noncomputable def homComplexEquiv
    {A : Type u} [Category.{v} A] [Abelian A]
    {P J N I : CochainComplex A ℤ}
    (e : HomComplex P J ≅ HomComplex N I) : (P ⟶ J) ≃ (N ⟶ I) where
  toFun := homComplexMap e
  invFun := homComplexMap e.symm
  left_inv f := Cochain.ofHom_injective (by
    simp only [ofHom_homComplexMap]
    exact Iso.hom_inv_id_apply ((HomologicalComplex.eval _ _ 0).mapIso e) _)
  right_inv f := Cochain.ofHom_injective (by
    simp only [ofHom_homComplexMap]
    exact Iso.inv_hom_id_apply ((HomologicalComplex.eval _ _ 0).mapIso e) _)

@[simp] private lemma ofHom_homComplexEquiv
    {A : Type u} [Category.{v} A] [Abelian A]
    {P J N I : CochainComplex A ℤ}
    (e : HomComplex P J ≅ HomComplex N I) (f : P ⟶ J) :
    Cochain.ofHom (homComplexEquiv e f) = e.hom.f 0 (Cochain.ofHom f) :=
  ofHom_homComplexMap e f

private noncomputable def homComplexMapHomotopy
    {A : Type u} [Category.{v} A] [Abelian A]
    {P J N I : CochainComplex A ℤ}
    (e : HomComplex P J ≅ HomComplex N I) {f g : P ⟶ J} (h : Homotopy f g) :
    Homotopy (homComplexMap e f) (homComplexMap e g) :=
  (Cochain.equivHomotopy _ _).symm ⟨e.hom.f (-1) (Cochain.ofHomotopy h), by
    rw [ofHom_homComplexMap, ofHom_homComplexMap, homComplexMap_delta,
      δ_ofHomotopy, map_sub, sub_add_cancel]⟩

private lemma homComplexEquiv_homotopy
    {A : Type u} [Category.{v} A] [Abelian A]
    {P J N I : CochainComplex A ℤ}
    (e : HomComplex P J ≅ HomComplex N I) (f g : P ⟶ J) :
    Nonempty (Homotopy f g) ↔
      Nonempty (Homotopy (homComplexEquiv e f) (homComplexEquiv e g)) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨homComplexMapHomotopy e h⟩
  · rintro ⟨h⟩
    simpa only [Equiv.symm_apply_apply] using
      (show Nonempty (Homotopy ((homComplexEquiv e).symm (homComplexEquiv e f))
        ((homComplexEquiv e).symm (homComplexEquiv e g))) from
          ⟨homComplexMapHomotopy e.symm h⟩)

private noncomputable def homComplexQuotEquiv
    {A : Type u} [Category.{v} A] [Abelian A]
    {P J N I : CochainComplex A ℤ}
    (e : HomComplex P J ≅ HomComplex N I) :
    ((HomotopyCategory.quotient A (.up ℤ)).obj P ⟶
      (HomotopyCategory.quotient A (.up ℤ)).obj J) ≃
    ((HomotopyCategory.quotient A (.up ℤ)).obj N ⟶
      (HomotopyCategory.quotient A (.up ℤ)).obj I) where
  toFun := Quot.lift
    (fun f ↦ (HomotopyCategory.quotient A (.up ℤ)).map (homComplexEquiv e f))
    (by
      intro f g h
      obtain ⟨h⟩ := (HomRel.compClosure_iff_self _ _ _).1 h
      exact HomotopyCategory.eq_of_homotopy _ _ (homComplexMapHomotopy e h))
  invFun := Quot.lift
    (fun f ↦ (HomotopyCategory.quotient A (.up ℤ)).map ((homComplexEquiv e).symm f))
    (by
      intro f g h
      obtain ⟨h⟩ := (HomRel.compClosure_iff_self _ _ _).1 h
      exact HomotopyCategory.eq_of_homotopy _ _ (homComplexMapHomotopy e.symm h))
  left_inv := by
    intro f
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective f
    change (HomotopyCategory.quotient A (.up ℤ)).map
      ((homComplexEquiv e).symm (homComplexEquiv e f)) = _
    rw [Equiv.symm_apply_apply]
  right_inv := by
    intro f
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective f
    change (HomotopyCategory.quotient A (.up ℤ)).map
      (homComplexEquiv e ((homComplexEquiv e).symm f)) = _
    rw [Equiv.apply_symm_apply]

private noncomputable def kInjectiveQHomEquiv
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (P I : CochainComplex A ℤ) [I.IsKInjective] :
    ((HomotopyCategory.quotient A (.up ℤ)).obj P ⟶
      (HomotopyCategory.quotient A (.up ℤ)).obj I) ≃
      (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj I) :=
  (Equiv.ofBijective _ (IsKInjective.Qh_map_bijective _ I)).trans
    (Iso.homCongr ((DerivedCategory.quotientCompQhIso A).app P)
      ((DerivedCategory.quotientCompQhIso A).app I))

private lemma kInjectiveQHomEquiv_map
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (P I : CochainComplex A ℤ) [I.IsKInjective] (f : P ⟶ I) :
    kInjectiveQHomEquiv P I ((HomotopyCategory.quotient A (.up ℤ)).map f) =
      DerivedCategory.Q.map f := by
  change (DerivedCategory.quotientCompQhIso A).inv.app P ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map f) ≫
      (DerivedCategory.quotientCompQhIso A).hom.app I = _
  rw [DerivedCategory.quotientCompQhIso_hom_naturality, Iso.inv_hom_id_app_assoc]

/-- K-injectivity of the row Hom, signed chain currying, and its normalized
localization with naturality in all three variables.

Source: Stacks 0A96 and the first proof paragraph of 08J9; signed external
currying is the row-convention adaptation of Stacks 0A5Y.
(blueprint: lem-sf-kflat-bifunctor-kinjective-currying)

Proof: (1) If K is acyclic, K to zero is a quasi-isomorphism. Admissibility of T
makes Tot(K,T) acyclic, since additivity identifies Tot(0,T) with zero. The
external Hom-complex currying isomorphism of
lem-sf-kflat-bifunctor-chain-currying identifies maps K to Hom(T,I), modulo
homotopy, with maps Tot(K,T) to I modulo homotopy. The latter vanish because
I is K-injective. Thus Hom(T,I) is K-injective.
(2) Restrict that isomorphism to degree-zero cocycles. Its degree-zero formula
is the displayed counit formula with sign (-1)^(p*q). Its degree-minus-one
formula, with sign (-1)^(q*(p-1)), transports boundaries and hence homotopies;
the inverse gives reflection as well as preservation.
(3) Use IsKInjective.Qh_map_bijective from
lem-weil-pbc-kinjective-hom-derived, first inversely for the target I, then
inverse signed currying on homotopy classes, then localization for the target
Hom(T,I), which is K-injective by (1). Postcompose with rho inverse. Every
step is bijective and its value on an actual uncurried map is the stated
normalization.
(4) Represent a by an actual chain map using that localization bijection.
Chain-currying naturality identifies its transformed curry with precomposition
by f and the Hom map induced by g,h. Apply (3) at T',I' and use naturality of
rho. This gives the displayed equation and is independent of representatives. -/
theorem exists_bifunctorKInjectiveCurrying
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasCountableProducts A] [HasCountableCoproducts A] [HasDerivedCategory.{w} A]
    (F : A ⥤ A ⥤ A) (H₀ : Aᵒᵖ ⥤ A ⥤ A)
    [F.Additive] [∀ X : A, (F.obj X).Additive]
    [H₀.Additive] [∀ X : Aᵒᵖ, (H₀.obj X).Additive]
    (adj : F ⊣₂ H₀)
    (H : (DerivedCategory A)ᵒᵖ × DerivedCategory A ⥤ DerivedCategory A)
    (ρ : ∀ (T I : CochainComplex A ℤ), I.IsKInjective →
      (H.obj (op (DerivedCategory.Q.obj T), DerivedCategory.Q.obj I) ≅
        DerivedCategory.Q.obj (bifunctorHomObj H₀ T I)))
    (hρ : ∀ (T T' I I' : CochainComplex A ℤ)
      (hI : I.IsKInjective) (hI' : I'.IsKInjective) (g : T' ⟶ T) (h : I ⟶ I'),
      H.map (Prod.mkHom (DerivedCategory.Q.map g).op (DerivedCategory.Q.map h)) ≫
          (ρ T' I' hI').hom =
        (ρ T I hI).hom ≫ DerivedCategory.Q.map
          (bifunctorHomMapLeft (H := H₀) (Y := I) g ≫
            bifunctorHomMapRight (H := H₀) (K := T') h)) :
    (∀ (T I : CochainComplex A ℤ), IsBifunctorTensorAdmissible F T →
      I.IsKInjective → (bifunctorHomObj H₀ T I).IsKInjective) ∧
    ∃ uncurry : ∀ (P T I : CochainComplex A ℤ),
      IsBifunctorTensorAdmissible F T → I.IsKInjective →
      (P ⟶ bifunctorHomObj H₀ T I) ≃
        (HomologicalComplex.mapBifunctor P T F.flip (.up ℤ) ⟶ I),
      (∀ (P T I : CochainComplex A ℤ)
        (hT : IsBifunctorTensorAdmissible F T) (hI : I.IsKInjective)
        (φ : P ⟶ bifunctorHomObj H₀ T I) (p q n : ℤ) (hpq : p + q = n),
        HomologicalComplex.ιMapBifunctor P T F.flip (.up ℤ) p q n hpq ≫
            (uncurry P T I hT hI φ).f n =
          (p * q).negOnePow •
            ((F.obj (T.X q)).map
                (φ.f p ≫ bifunctorHomπ H₀ T I p q n (by omega)) ≫
              (adj.adj (T.X q)).counit.app (I.X n))) ∧
      (∀ (P T I : CochainComplex A ℤ)
        (hT : IsBifunctorTensorAdmissible F T) (hI : I.IsKInjective)
        (φ φ' : P ⟶ bifunctorHomObj H₀ T I),
        Nonempty (Homotopy φ φ') ↔
          Nonempty (Homotopy (uncurry P T I hT hI φ) (uncurry P T I hT hI φ'))) ∧
      ∃ d : ∀ (P T I : CochainComplex A ℤ),
        IsBifunctorTensorAdmissible F T → I.IsKInjective →
        (DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor P T F.flip (.up ℤ)) ⟶
          DerivedCategory.Q.obj I) ≃
        (DerivedCategory.Q.obj P ⟶
          H.obj (op (DerivedCategory.Q.obj T), DerivedCategory.Q.obj I)),
        (∀ (P T I : CochainComplex A ℤ)
          (hT : IsBifunctorTensorAdmissible F T) (hI : I.IsKInjective)
          (φ : P ⟶ bifunctorHomObj H₀ T I),
          d P T I hT hI (DerivedCategory.Q.map (uncurry P T I hT hI φ)) =
            DerivedCategory.Q.map φ ≫ (ρ T I hI).inv) ∧
        (∀ (P P' T T' I I' : CochainComplex A ℤ)
          (hT : IsBifunctorTensorAdmissible F T)
          (hT' : IsBifunctorTensorAdmissible F T')
          (hI : I.IsKInjective) (hI' : I'.IsKInjective)
          (f : P' ⟶ P) (g : T' ⟶ T) (h : I ⟶ I')
          (a : DerivedCategory.Q.obj
            (HomologicalComplex.mapBifunctor P T F.flip (.up ℤ)) ⟶ DerivedCategory.Q.obj I),
          d P' T' I' hT' hI'
              (DerivedCategory.Q.map
                  (HomologicalComplex.mapBifunctorMap f g F.flip (.up ℤ)) ≫
                a ≫ DerivedCategory.Q.map h) =
            DerivedCategory.Q.map f ≫ d P T I hT hI a ≫
              H.map (Prod.mkHom (DerivedCategory.Q.map g).op (DerivedCategory.Q.map h))) := by
  classical
  obtain ⟨E, hE, _hEinv, _hEuniq, hEnat, _hZ, _hZ', _hB, _hB', _hδ, _hδ'⟩ :=
    exists_bifunctorChainCurrying F H₀ adj
  let U (P T I : CochainComplex A ℤ) := homComplexEquiv (E P T I)
  have hU (P T I : CochainComplex A ℤ) (φ : P ⟶ bifunctorHomObj H₀ T I) :
      Cochain.ofHom (U P T I φ) = (E P T I).hom.f 0 (Cochain.ofHom φ) :=
    ofHom_homComplexEquiv _ _
  have hUzero (P T I : CochainComplex A ℤ) : U P T I 0 = 0 := by
    apply Cochain.ofHom_injective
    rw [hU, Cochain.ofHom_zero, map_zero, Cochain.ofHom_zero]
  have hUhom (P T I : CochainComplex A ℤ) (φ φ' : P ⟶ bifunctorHomObj H₀ T I) :
      Nonempty (Homotopy φ φ') ↔ Nonempty (Homotopy (U P T I φ) (U P T I φ')) :=
    homComplexEquiv_homotopy _ _ _
  have hUnat (P P' T T' I I' : CochainComplex A ℤ)
      (f : P' ⟶ P) (g : T' ⟶ T) (h : I ⟶ I') (φ : P ⟶ bifunctorHomObj H₀ T I) :
      U P' T' I' (f ≫ φ ≫
          (bifunctorHomMapLeft (H := H₀) (Y := I) g ≫
            bifunctorHomMapRight (H := H₀) (K := T') h)) =
        HomologicalComplex.mapBifunctorMap f g F.flip (.up ℤ) ≫ U P T I φ ≫ h := by
    apply Cochain.ofHom_injective
    simpa only [Cochain.ofHom_comp, hU, Cochain.comp_assoc_of_first_is_zero_cochain] using
      hEnat P P' T T' I I' f g h 0 (Cochain.ofHom φ)
  have hKI (T I : CochainComplex A ℤ) (hT : IsBifunctorTensorAdmissible F T)
      (hI : I.IsKInjective) : (bifunctorHomObj H₀ T I).IsKInjective := by
    let := hI
    let G := F.flip.map₂CochainComplex.flip.obj T
    have hG : G.PreservesZeroMorphisms := by
      constructor
      intro P P'
      change HomologicalComplex.mapBifunctorMap (0 : P ⟶ P') (𝟙 T) F.flip (.up ℤ) = 0
      ext n : 1
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q hpq
      rw [HomologicalComplex.ι_mapBifunctorMap]
      simp
    let := hG
    constructor
    intro K φ hK
    have hzero : QuasiIso (0 : K ⟶ (HomologicalComplex.zero : CochainComplex A ℤ)) := by
      constructor
      intro n
      exact (quasiIsoAt_iff_exactAt _ _ (hK n)).2
        (HomologicalComplex.acyclic_of_isZero _ HomologicalComplex.isZero_zero n)
    have ht := hT (0 : K ⟶ (HomologicalComplex.zero : CochainComplex A ℤ)) hzero
    have htotal : (HomologicalComplex.mapBifunctor K T F.flip (.up ℤ)).Acyclic := by
      intro n
      exact (quasiIsoAt_iff_exactAt'
        (HomologicalComplex.mapBifunctorMap
          (0 : K ⟶ (HomologicalComplex.zero : CochainComplex A ℤ)) (𝟙 T) F.flip (.up ℤ)) n
        (HomologicalComplex.acyclic_of_isZero _
          (Functor.map_isZero G HomologicalComplex.isZero_zero) n)).1 (by infer_instance)
    apply (hUhom K T I φ 0).mpr
    rw [hUzero]
    exact IsKInjective.nonempty_homotopy_zero _ htotal
  refine ⟨hKI, fun P T I _ _ ↦ U P T I, ?_, ?_, ?_⟩
  · intro P T I hT hI φ p q n hpq
    rw [← Cochain.ofHom_v (U P T I φ), hU]
    simpa only [Cochain.ofHom_v, mul_comm q p] using
      hE P T I 0 (Cochain.ofHom φ) p q p n n (add_zero p) hpq
        (by omega) (add_zero n)
  · intro P T I hT hI φ φ'
    exact hUhom P T I φ φ'
  · let d (P T I : CochainComplex A ℤ)
        (hT : IsBifunctorTensorAdmissible F T) (hI : I.IsKInjective) :
        (DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor P T F.flip (.up ℤ)) ⟶
          DerivedCategory.Q.obj I) ≃
        (DerivedCategory.Q.obj P ⟶
          H.obj (op (DerivedCategory.Q.obj T), DerivedCategory.Q.obj I)) := by
        let := hI
        let := hKI T I hT hI
        exact (kInjectiveQHomEquiv _ I).symm.trans
          ((homComplexQuotEquiv (E P T I)).symm.trans
            ((kInjectiveQHomEquiv P _).trans (ρ T I hI).symm.homToEquiv))
    have hd (P T I : CochainComplex A ℤ)
        (hT : IsBifunctorTensorAdmissible F T) (hI : I.IsKInjective)
        (φ : P ⟶ bifunctorHomObj H₀ T I) :
        d P T I hT hI (DerivedCategory.Q.map (U P T I φ)) =
          DerivedCategory.Q.map φ ≫ (ρ T I hI).inv := by
      let := hI
      let := hKI T I hT hI
      change kInjectiveQHomEquiv P (bifunctorHomObj H₀ T I)
        ((homComplexQuotEquiv (E P T I)).symm
          ((kInjectiveQHomEquiv _ I).symm (DerivedCategory.Q.map (U P T I φ)))) ≫ _ = _
      rw [← kInjectiveQHomEquiv_map, Equiv.symm_apply_apply]
      change kInjectiveQHomEquiv P (bifunctorHomObj H₀ T I)
        ((HomotopyCategory.quotient A (.up ℤ)).map ((U P T I).symm (U P T I φ))) ≫ _ = _
      rw [Equiv.symm_apply_apply, kInjectiveQHomEquiv_map]
      rfl
    refine ⟨d, hd, ?_⟩
    intro P P' T T' I I' hT hT' hI hI' f g h a
    let := hI
    obtain ⟨a, rfl⟩ := (kInjectiveQHomEquiv _ I).surjective a
    obtain ⟨a, rfl⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective a
    rw [kInjectiveQHomEquiv_map]
    obtain ⟨φ, rfl⟩ := (U P T I).surjective a
    rw [← Functor.map_comp, ← Functor.map_comp, ← hUnat P P' T T' I I' f g h φ,
      hd P' T' I' hT' hI', hd P T I hT hI]
    simp only [Functor.map_comp, Category.assoc]
    have hr : DerivedCategory.Q.map
        (bifunctorHomMapLeft (H := H₀) (Y := I) g ≫
          bifunctorHomMapRight (H := H₀) (K := T') h) ≫ (ρ T' I' hI').inv =
        (ρ T I hI).inv ≫
          H.map (Prod.mkHom (DerivedCategory.Q.map g).op (DerivedCategory.Q.map h)) := by
      apply (cancel_mono (ρ T' I' hI').hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [hρ T T' I I' hI hI' g h, Iso.inv_hom_id_assoc]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun z ↦ DerivedCategory.Q.map f ≫ DerivedCategory.Q.map φ ≫ z) hr

end CochainComplex
