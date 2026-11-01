/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData
import WeilConjectures.CategoryTheory.DerivedExactSquareComposition

/-! Qh-object case of intrinsic finite-dualizing restriction composition. -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local instance] normalizedDVRModuleRes_limits normalizedDVRModuleRes_colimits
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (X : Scheme.{u})

private theorem fd_eqToIso_section
    {C : Type*} [Category C] {R : Sheaf (ProEt.topology X) RingCat.{u + 1}}
    {F G : C ⥤ SheafOfModules.{u + 1} R} (h : F = G)
    (M : C) (W : X.ProEtᵒᵖ) (x : (F.obj M).val.obj W) :
    HEq (((eqToIso h).hom.app M).val.app W x) x := by
  subst h
  rfl

private theorem fd_eqToIso_inv_section
    {C : Type*} [Category C] {R : Sheaf (ProEt.topology X) RingCat.{u + 1}}
    {F G : C ⥤ SheafOfModules.{u + 1} R} (h : F = G)
    (M : C) (W : X.ProEtᵒᵖ) (x : (G.obj M).val.obj W) :
    HEq (((eqToIso h).inv.app M).val.app W x) x := by
  subst h
  rfl

private def fdTransportSquare
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (U : C ⥤ D) (V : C' ⥤ D') (F : C ⥤ C')
    {G G' : D ⥤ D'} (h : G = G') (e : U ⋙ G' ≅ F ⋙ V) :
    U ⋙ G ≅ F ⋙ V :=
  Functor.isoWhiskerLeft U (eqToIso h) ≪≫ e

private theorem fdTransportSquare_section
    {C C' : Type*} [Category C] [Category C']
    {R S : Sheaf (ProEt.topology X) RingCat.{u + 1}}
    (f g : R ⟶ S) (U : C ⥤ SheafOfModules.{u + 1} S)
    (V : C' ⥤ SheafOfModules.{u + 1} R) (F : C ⥤ C')
    (h : SheafOfModules.restrictScalars.{u + 1} f =
      SheafOfModules.restrictScalars.{u + 1} g)
    (e : U ⋙ SheafOfModules.restrictScalars.{u + 1} g ≅ F ⋙ V)
    (M : C) (W : X.ProEtᵒᵖ) (x : (U.obj M).val.obj W) :
    HEq (((fdTransportSquare U V F h e).hom.app M).val.app W x)
      ((e.hom.app M).val.app W x) := by
  have he := fd_eqToIso_section X h (U.obj M) W x
  exact heq_of_eq (congrArg (fun z ↦ (e.hom.app M).val.app W z) (eq_of_heq he))

private def fdGenericRestriction
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) :
    (sfIntrinsicModuleEquivalence X B).functor ⋙ finiteDualizingIntrinsicRes X φ ≅
      Sheaf.restrictScalars (ProEt.topology X) φ.ulift ⋙
        (sfIntrinsicModuleEquivalence X A).functor :=
  (finiteDualizingRestriction_existsUnique X φ).choose

private theorem fdGenericRestriction_section
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
    (W : X.ProEtᵒᵖ) (x : M.obj.obj W) :
    HEq (((fdGenericRestriction X φ).hom.app M).val.app W
      (sfIntrinsicRealizationUnit X B M W x))
      (sfIntrinsicRealizationUnit X A
        ((Sheaf.restrictScalars (ProEt.topology X) φ.ulift).obj M) W x) :=
  (finiteDualizingRestriction_existsUnique X φ).choose_spec.1 M W x

private abbrev fdRing (A : Type u) [CommRing A] :=
  (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing X A)

private def fdGenericTransportRestriction
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    (f : fdRing X A ⟶ fdRing X B)
    (h : SheafOfModules.restrictScalars.{u + 1} f = finiteDualizingIntrinsicRes X φ) :
    (sfIntrinsicModuleEquivalence X B).functor ⋙ SheafOfModules.restrictScalars.{u + 1} f ≅
      Sheaf.restrictScalars (ProEt.topology X) φ.ulift ⋙
        (sfIntrinsicModuleEquivalence X A).functor :=
  fdTransportSquare _ _ _ h (fdGenericRestriction X φ)

private theorem fdGenericTransportRestriction_section
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    (f : fdRing X A ⟶ fdRing X B)
    (h : SheafOfModules.restrictScalars.{u + 1} f = finiteDualizingIntrinsicRes X φ)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
    (W : X.ProEtᵒᵖ) (x : M.obj.obj W) :
    HEq (((fdGenericTransportRestriction X φ f h).hom.app M).val.app W
      (sfIntrinsicRealizationUnit X B M W x))
      (sfIntrinsicRealizationUnit X A
        ((Sheaf.restrictScalars (ProEt.topology X) φ.ulift).obj M) W x) := by
  exact (fdTransportSquare_section X f (finiteDualizingIntrinsicRingMap X φ)
    _ _ _ h (fdGenericRestriction X φ) M W (sfIntrinsicRealizationUnit X B M W x)).trans
      (fdGenericRestriction_section X φ M W x)

private def fdOrdinaryRestriction {m n : ℕ} (h : n ≤ m) :=
  fdGenericTransportRestriction X (finiteDualizingQuotientBase l E h)
    (normalizedDVRQuotient l E X h) (finiteDualizingRestriction_eq l E X h)

private theorem fd_unit_surjective (A : Type u) [CommRing A] [Finite A]
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (W : X.ProEtᵒᵖ) : Function.Surjective (sfIntrinsicRealizationUnit X A M W) := by
  let a := ProEtale.finiteCoefficientIntrinsicScalarMap X A
  let P := (ProEtale.finiteCoefficientModulePresheaf X.ProEt
    (ULift.{u + 1, u} A)).obj M.obj
  let η := (PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
    a).unit.app P
  have : IsIso η := by
    change IsIso ((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
      a).unit.app P)
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose (ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1})).obj M).property
  intro x
  refine ⟨(inv η).app W x, ?_⟩
  exact congrArg (fun k ↦ k.app W x) (IsIso.inv_hom_id η)

private theorem fd_map_unit (A : Type u) [CommRing A] [Finite A]
    {M N : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))}
    (f : M ⟶ N) (W : X.ProEtᵒᵖ) (x : M.obj.obj W) :
    ((sfIntrinsicModuleEquivalence X A).functor.map f).val.app W
      (sfIntrinsicRealizationUnit X A M W x) =
        sfIntrinsicRealizationUnit X A N W (f.hom.app W x) := by
  have h := (PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap X A)).unit.naturality
      ((ProEtale.finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1, u} A)).map f.hom)
  exact (congrArg (fun k ↦ k.app W x) h).symm

private def fdSheafRestrictionComp
    {R S T : Sheaf (ProEt.topology X) RingCat.{u + 1}}
    (f : R ⟶ S) (g : S ⟶ T) (fg : R ⟶ T) (h : fg = f ≫ g) :
    SheafOfModules.restrictScalars.{u + 1} fg ≅
      SheafOfModules.restrictScalars.{u + 1} g ⋙
        SheafOfModules.restrictScalars.{u + 1} f :=
  (normalizedDVRRestrictionCompIso f g ≪≫
    eqToIso (congrArg (fun k ↦ SheafOfModules.restrictScalars.{u + 1} k) h.symm)).symm

private theorem fdSheafRestrictionComp_section
    {R S T : Sheaf (ProEt.topology X) RingCat.{u + 1}}
    (f : R ⟶ S) (g : S ⟶ T) (fg : R ⟶ T) (h : fg = f ≫ g)
    (M : SheafOfModules.{u + 1} T) (W : X.ProEtᵒᵖ) (x : M.val.obj W) :
    HEq (((fdSheafRestrictionComp X f g fg h).hom.app M).val.app W x) x := by
  exact fd_eqToIso_inv_section X
    (F := SheafOfModules.restrictScalars.{u + 1} (f ≫ g))
    (G := SheafOfModules.restrictScalars.{u + 1} fg)
    (congrArg (fun k ↦ SheafOfModules.restrictScalars.{u + 1} k) h.symm) M W x

private def fdSystemModuleComp
    (S : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) RingCat.{u + 1})
    {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :
    SheafOfModules.restrictScalars.{u + 1} (S.map (homOfLE (hmn.trans hrm)).op) ≅
      SheafOfModules.restrictScalars.{u + 1} (S.map (homOfLE hmn).op) ⋙
        SheafOfModules.restrictScalars.{u + 1} (S.map (homOfLE hrm).op) :=
  fdSheafRestrictionComp X _ _ _ (S.map_comp (homOfLE hrm).op (homOfLE hmn).op)

private def fdModuleComp {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m) :=
  fdSystemModuleComp X (integralCoefficientSheafSystem l E X) hrm hmn

private theorem fd_generic_ordinary_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C)
    (hχ : RingHom.ulift.{u + 1, u + 1} χ =
      (RingHom.ulift.{u + 1, u + 1} ψ).comp (RingHom.ulift.{u + 1, u + 1} φ))
    (f : fdRing X A ⟶ fdRing X B) (g : fdRing X B ⟶ fdRing X C)
    (fg : fdRing X A ⟶ fdRing X C) (hfg : fg = f ≫ g)
    (hf : SheafOfModules.restrictScalars.{u + 1} f = finiteDualizingIntrinsicRes X φ)
    (hg : SheafOfModules.restrictScalars.{u + 1} g = finiteDualizingIntrinsicRes X ψ)
    (hfg' : SheafOfModules.restrictScalars.{u + 1} fg = finiteDualizingIntrinsicRes X χ)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} C))) :
    (fdGenericTransportRestriction X χ fg hfg').hom.app M ≫
      (sfIntrinsicModuleEquivalence X A).functor.map
        ((Sheaf.restrictScalarsCompIso (ProEt.topology X)
          (RingHom.ulift.{u + 1, u + 1} φ) (RingHom.ulift.{u + 1, u + 1} ψ)
          (RingHom.ulift.{u + 1, u + 1} χ) hχ).inv.app M) =
    (fdSheafRestrictionComp X f g fg hfg).hom.app
        ((sfIntrinsicModuleEquivalence X C).functor.obj M) ≫
      (SheafOfModules.restrictScalars.{u + 1} f).map
        ((fdGenericTransportRestriction X ψ g hg).hom.app M) ≫
      (fdGenericTransportRestriction X φ f hf).hom.app
        ((Sheaf.restrictScalars (ProEt.topology X)
          (RingHom.ulift.{u + 1, u + 1} ψ)).obj M) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  obtain ⟨y, rfl⟩ := fd_unit_surjective X C M W x
  change ((sfIntrinsicModuleEquivalence X A).functor.map _).val.app W
      (((fdGenericTransportRestriction X χ fg hfg').hom.app M).val.app W _) =
    ((fdGenericTransportRestriction X φ f hf).hom.app
      ((Sheaf.restrictScalars (ProEt.topology X)
        (RingHom.ulift.{u + 1, u + 1} ψ)).obj M)).val.app W
      (((fdGenericTransportRestriction X ψ g hg).hom.app M).val.app W
        (((fdSheafRestrictionComp X f g fg hfg).hom.app
          ((sfIntrinsicModuleEquivalence X C).functor.obj M)).val.app W
            (sfIntrinsicRealizationUnit X C M W y)))
  have h₀ := eq_of_heq
    (fdGenericTransportRestriction_section X χ fg hfg' M W y)
  have h₁ := eq_of_heq (fdSheafRestrictionComp_section X f g fg hfg
    ((sfIntrinsicModuleEquivalence X C).functor.obj M) W
    (sfIntrinsicRealizationUnit X C M W y))
  have h₂ := eq_of_heq (fdGenericTransportRestriction_section X ψ g hg M W y)
  have h₃ := eq_of_heq (fdGenericTransportRestriction_section X φ f hf
    ((Sheaf.restrictScalars (ProEt.topology X) ψ.ulift).obj M) W y)
  calc
    _ = sfIntrinsicRealizationUnit X A _ W y :=
      (congrArg (fun z ↦ ((sfIntrinsicModuleEquivalence X A).functor.map
        ((Sheaf.restrictScalarsCompIso (ProEt.topology X)
          φ.ulift ψ.ulift χ.ulift hχ).inv.app M)).val.app W z) h₀).trans
            (fd_map_unit X A
              ((Sheaf.restrictScalarsCompIso (ProEt.topology X)
                φ.ulift ψ.ulift χ.ulift hχ).inv.app M) W y)
    _ = _ := (h₃.symm.trans (congrArg (fun z ↦
      ((fdGenericTransportRestriction X φ f hf).hom.app
        ((Sheaf.restrictScalars (ProEt.topology X) ψ.ulift).obj M)).val.app W z)
          h₂.symm)).trans (congrArg (fun z ↦
            ((fdGenericTransportRestriction X φ f hf).hom.app
              ((Sheaf.restrictScalars (ProEt.topology X) ψ.ulift).obj M)).val.app W
                (((fdGenericTransportRestriction X ψ g hg).hom.app M).val.app W z))
                  h₁.symm)

private theorem fd_derive_transport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory C'] [HasDerivedCategory D']
    (U : C ⥤ D) (V : C' ⥤ D') (F : C ⥤ C') (G G' : D ⥤ D')
    [U.Additive] [V.Additive] [F.Additive] [G.Additive] [G'.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (h : G = G') (e : U ⋙ G' ≅ F ⋙ V) :
    HEq (Functor.mapDerivedCategorySquareIso
      (Functor.isoWhiskerLeft U (eqToIso h) ≪≫ e))
      (Functor.mapDerivedCategorySquareIso e) := by
  subst G'
  simp only [eqToIso_refl, Functor.isoWhiskerLeft_refl, Iso.refl_trans]
  rfl

private theorem fd_derivedRestriction {m n : ℕ} (h : n ≤ m) :
    let := (normalizedDVRModuleRes_exact l E X h).1
    let := (normalizedDVRModuleRes_exact l E X h).2
    Functor.mapDerivedCategorySquareIso (fdOrdinaryRestriction l E X h) =
      finiteDualizingIntrinsicRestriction l E X h := by
  let := (normalizedDVRModuleRes_exact l E X h).1
  let := (normalizedDVRModuleRes_exact l E X h).2
  have ht := fd_derive_transport
    (sfIntrinsicModuleEquivalence X
      (Padic.coefficientExtensionRing l E (n + 1))).functor
    (sfIntrinsicModuleEquivalence X
      (Padic.coefficientExtensionRing l E (m + 1))).functor
    (Sheaf.restrictScalars (ProEt.topology X) (finiteDualizingQuotient l E h))
    (normalizedDVRModuleRes l E X h)
    (finiteDualizingIntrinsicRes X (finiteDualizingQuotientBase l E h))
    (finiteDualizingRestriction_eq l E X h)
    (fdGenericRestriction X (finiteDualizingQuotientBase l E h))
  have hs := (finiteDualizingIntrinsicRestriction_existsUnique l E X h).choose_spec.1
  exact eq_of_heq (ht.trans hs.symm)

private theorem fd_square_symm
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    {R : C ⥤ D} {G : D ⥤ F} {L : C ⥤ E} {S : E ⥤ F}
    [R.Additive] [G.Additive] [L.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (q : R ⋙ G ≅ L ⋙ S) :
    (Functor.mapDerivedCategorySquareIso q.symm).hom =
      (Functor.mapDerivedCategorySquareIso q).inv := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]

private theorem fd_derivedRestriction_symm {m n : ℕ} (h : n ≤ m) :
    let := (normalizedDVRModuleRes_exact l E X h).1
    let := (normalizedDVRModuleRes_exact l E X h).2
    Functor.mapDerivedCategorySquareIso (fdOrdinaryRestriction l E X h).symm =
      (finiteDualizingIntrinsicRestriction l E X h).symm := by
  let := (normalizedDVRModuleRes_exact l E X h).1
  let := (normalizedDVRModuleRes_exact l E X h).2
  apply Iso.ext
  exact (fd_square_symm _).trans (congrArg Iso.inv (fd_derivedRestriction l E X h))

private theorem fd_derived_sheaf_comp_inverse
    {R S T : Sheaf (ProEt.topology X) RingCat.{u + 1}}
    (f : R ⟶ S) (g : S ⟶ T) (fg : R ⟶ T) (h : fg = f ≫ g)
    [PreservesFiniteLimits (SheafOfModules.restrictScalars.{u + 1} f)]
    [PreservesFiniteColimits (SheafOfModules.restrictScalars.{u + 1} f)]
    [PreservesFiniteLimits (SheafOfModules.restrictScalars.{u + 1} g)]
    [PreservesFiniteColimits (SheafOfModules.restrictScalars.{u + 1} g)]
    [PreservesFiniteLimits (SheafOfModules.restrictScalars.{u + 1} fg)]
    [PreservesFiniteColimits (SheafOfModules.restrictScalars.{u + 1} fg)] :
    Functor.mapDerivedCategoryNatIso (fdSheafRestrictionComp X f g fg h) ≪≫
        Functor.mapDerivedCategoryCompIso
          (SheafOfModules.restrictScalars.{u + 1} g)
          (SheafOfModules.restrictScalars.{u + 1} f) =
      ((Functor.mapDerivedCategoryCompIso
          (SheafOfModules.restrictScalars.{u + 1} g)
          (SheafOfModules.restrictScalars.{u + 1} f)).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (normalizedDVRRestrictionCompIso f g ≪≫ eqToIso
            (congrArg (fun k ↦ SheafOfModules.restrictScalars.{u + 1} k) h.symm))).symm := by
  apply Iso.ext
  simp only [fdSheafRestrictionComp, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv]

private theorem fd_forward
    {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {X₁ X₂ : C} {Y₀ Y₁ Z₀ : D}
    (q₀ : Y₀ ≅ Z₀) (q₁ : Y₁ ≅ G.obj X₁)
    (q₂ : X₁ ≅ X₂) (a : Y₀ ⟶ Y₁) (b : Z₀ ⟶ G.obj X₂)
    (h : q₀.inv ≫ a = b ≫ G.map q₂.inv ≫ q₁.inv) :
    a ≫ q₁.hom ≫ G.map q₂.hom = q₀.hom ≫ b := by
  have he := congrArg (fun t ↦ q₀.hom ≫ t ≫ q₁.hom ≫ G.map q₂.hom) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    ← G.map_comp, Iso.inv_hom_id, G.map_id, Category.comp_id] using he

private theorem fd_generic_ordinary_forward
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C)
    (hχ : RingHom.ulift.{u + 1, u + 1} χ =
      (RingHom.ulift.{u + 1, u + 1} ψ).comp (RingHom.ulift.{u + 1, u + 1} φ))
    (f : fdRing X A ⟶ fdRing X B) (g : fdRing X B ⟶ fdRing X C)
    (fg : fdRing X A ⟶ fdRing X C) (hfg : fg = f ≫ g)
    (hf : SheafOfModules.restrictScalars.{u + 1} f = finiteDualizingIntrinsicRes X φ)
    (hg : SheafOfModules.restrictScalars.{u + 1} g = finiteDualizingIntrinsicRes X ψ)
    (hfg' : SheafOfModules.restrictScalars.{u + 1} fg = finiteDualizingIntrinsicRes X χ) :
    ∀ M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} C)),
    (sfIntrinsicModuleEquivalence X A).functor.map
        ((Sheaf.restrictScalarsCompIso (ProEt.topology X)
          φ.ulift ψ.ulift χ.ulift hχ).inv.app M) ≫
      (fdGenericTransportRestriction X φ f hf).inv.app
        ((Sheaf.restrictScalars (ProEt.topology X) ψ.ulift).obj M) ≫
      (SheafOfModules.restrictScalars.{u + 1} f).map
        ((fdGenericTransportRestriction X ψ g hg).inv.app M) =
    (fdGenericTransportRestriction X χ fg hfg').inv.app M ≫
      (fdSheafRestrictionComp X f g fg hfg).hom.app
        ((sfIntrinsicModuleEquivalence X C).functor.obj M) := by
  intro M
  exact fd_forward (SheafOfModules.restrictScalars.{u + 1} f)
    ((fdGenericTransportRestriction X χ fg hfg').symm.app M)
    ((fdGenericTransportRestriction X φ f hf).symm.app
      ((Sheaf.restrictScalars (ProEt.topology X) ψ.ulift).obj M))
    ((fdGenericTransportRestriction X ψ g hg).symm.app M)
    _ _ (fd_generic_ordinary_comp X φ ψ χ hχ f g fg hfg hf hg hfg' M)

private theorem fd_fixed_derived_comp_inverse
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : χ = ψ.comp φ) :
    Functor.mapDerivedCategoryNatIso
        (Sheaf.restrictScalarsCompIso (ProEt.topology X) φ ψ χ hχ).symm ≪≫
      Functor.mapDerivedCategoryCompIso
        (Sheaf.restrictScalars (ProEt.topology X) ψ)
        (Sheaf.restrictScalars (ProEt.topology X) φ) =
    (Sheaf.derivedRestrictScalarsCompIso (ProEt.topology X) hχ).symm := by
  apply Iso.ext
  simp only [Sheaf.derivedRestrictScalarsCompIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Functor.mapDerivedCategoryNatIso_symm, Iso.symm_inv]

private theorem fd_derived_comp_app
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    [Abelian C₀] [Abelian C₁] [Abelian C₂]
    [Abelian D₀] [Abelian D₁] [Abelian D₂]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory D₀] [HasDerivedCategory D₁] [HasDerivedCategory D₂]
    (F₀₁ : C₀ ⥤ C₁) (F₁₂ : C₁ ⥤ C₂) (F₀₂ : C₀ ⥤ C₂)
    (G₀₁ : D₀ ⥤ D₁) (G₁₂ : D₁ ⥤ D₂) (G₀₂ : D₀ ⥤ D₂)
    (U₀ : C₀ ⥤ D₀) (U₁ : C₁ ⥤ D₁) (U₂ : C₂ ⥤ D₂)
    [F₀₁.Additive] [F₁₂.Additive] [F₀₂.Additive]
    [G₀₁.Additive] [G₁₂.Additive] [G₀₂.Additive]
    [U₀.Additive] [U₁.Additive] [U₂.Additive]
    [PreservesFiniteLimits F₀₁] [PreservesFiniteColimits F₀₁]
    [PreservesFiniteLimits F₁₂] [PreservesFiniteColimits F₁₂]
    [PreservesFiniteLimits F₀₂] [PreservesFiniteColimits F₀₂]
    [PreservesFiniteLimits G₀₁] [PreservesFiniteColimits G₀₁]
    [PreservesFiniteLimits G₁₂] [PreservesFiniteColimits G₁₂]
    [PreservesFiniteLimits G₀₂] [PreservesFiniteColimits G₀₂]
    [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
    [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
    [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
    (q₀₁ : F₀₁ ⋙ U₁ ≅ U₀ ⋙ G₀₁) (q₁₂ : F₁₂ ⋙ U₂ ≅ U₁ ⋙ G₁₂)
    (q₀₂ : F₀₂ ⋙ U₂ ≅ U₀ ⋙ G₀₂)
    (cF : F₀₂ ≅ F₀₁ ⋙ F₁₂) (cG : G₀₂ ≅ G₀₁ ⋙ G₁₂)
    (hq : ∀ M : C₀, U₂.map (cF.hom.app M) ≫ q₁₂.hom.app (F₀₁.obj M) ≫
      G₁₂.map (q₀₁.hom.app M) = q₀₂.hom.app M ≫ cG.hom.app (U₀.obj M))
    (d₀₁ : U₀.mapDerivedCategory ⋙ G₀₁.mapDerivedCategory ≅
      F₀₁.mapDerivedCategory ⋙ U₁.mapDerivedCategory)
    (d₁₂ : U₁.mapDerivedCategory ⋙ G₁₂.mapDerivedCategory ≅
      F₁₂.mapDerivedCategory ⋙ U₂.mapDerivedCategory)
    (d₀₂ : U₀.mapDerivedCategory ⋙ G₀₂.mapDerivedCategory ≅
      F₀₂.mapDerivedCategory ⋙ U₂.mapDerivedCategory)
    (dF : F₀₂.mapDerivedCategory ≅ F₀₁.mapDerivedCategory ⋙ F₁₂.mapDerivedCategory)
    (dG : G₀₂.mapDerivedCategory ≅ G₀₁.mapDerivedCategory ⋙ G₁₂.mapDerivedCategory)
    (h₀₁ : Functor.mapDerivedCategorySquareIso q₀₁ = d₀₁.symm)
    (h₁₂ : Functor.mapDerivedCategorySquareIso q₁₂ = d₁₂.symm)
    (h₀₂ : Functor.mapDerivedCategorySquareIso q₀₂ = d₀₂.symm)
    (hcF : Functor.mapDerivedCategoryNatIso cF ≪≫
      Functor.mapDerivedCategoryCompIso F₀₁ F₁₂ = dF)
    (hcG : Functor.mapDerivedCategoryNatIso cG ≪≫
      Functor.mapDerivedCategoryCompIso G₀₁ G₁₂ = dG) (K : DerivedCategory C₀) :
    d₀₂.inv.app K ≫ dG.hom.app (U₀.mapDerivedCategory.obj K) =
      U₂.mapDerivedCategory.map (dF.hom.app K) ≫
        d₁₂.inv.app (F₀₁.mapDerivedCategory.obj K) ≫
        G₁₂.mapDerivedCategory.map (d₀₁.inv.app K) := by
  have hd := Functor.mapDerivedCategorySquareIso_comp
    F₀₁ F₁₂ F₀₂ G₀₁ G₁₂ G₀₂ U₀ U₁ U₂ q₀₁ q₁₂ q₀₂ cF cG hq
  rw [hcF, hcG, h₀₁, h₁₂, h₀₂] at hd
  have ht := congrArg (fun e ↦ e.hom.app K) hd
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] using ht.symm

/-- The composition comparison on the image of the homotopy-category localization.
Source: the comparison pasting step of the intrinsic restriction composition proof
(blueprint: lem-coef-dualizing-intrinsic-restriction-comp-qh-x7).

Check the ordinary restriction square on realization-unit sections, which generate
each realized sheaf. The composition theorem for exact derived squares then gives
the comparison on the localized representative. -/
theorem finiteDualizingIntrinsicRestriction_comp_Qh
    {r m n : ℕ} (hrm : m ≤ r) (hmn : n ≤ m)
    (P : CochainComplex (Sheaf (ProEt.topology X)
      (ModuleCat (finiteDualizingCoeff l E n))) ℤ) :
    (finiteDualizingIntrinsicRestriction l E X (hmn.trans hrm)).inv.app
        (DerivedCategory.Q.obj P) ≫
        (normalizedDVRResComp l E X hrm hmn).inv.app
          ((sfIntrinsicDerivedEquivalence X
            (Padic.coefficientExtensionRing l E (n + 1))).functor.obj
            (DerivedCategory.Q.obj P)) =
      (sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing l E (r + 1))).functor.map
        ((Sheaf.derivedRestrictScalarsCompIso (ProEt.topology X)
          (finiteDualizingQuotient_comp l E hrm hmn)).inv.app
          (DerivedCategory.Q.obj P)) ≫
        (finiteDualizingIntrinsicRestriction l E X hrm).inv.app
          ((Sheaf.derivedRestrictScalars (ProEt.topology X)
            (finiteDualizingQuotient l E hmn)).obj
            (DerivedCategory.Q.obj P)) ≫
        (normalizedDVRRes l E X hrm).map
          ((finiteDualizingIntrinsicRestriction l E X hmn).inv.app
            (DerivedCategory.Q.obj P)) := by
  let F₀₁ := Sheaf.restrictScalars (ProEt.topology X) (finiteDualizingQuotient l E hmn)
  let F₁₂ := Sheaf.restrictScalars (ProEt.topology X) (finiteDualizingQuotient l E hrm)
  let F₀₂ := Sheaf.restrictScalars (ProEt.topology X)
    (finiteDualizingQuotient l E (hmn.trans hrm))
  let G₀₁ := normalizedDVRModuleRes l E X hmn
  let G₁₂ := normalizedDVRModuleRes l E X hrm
  let G₀₂ := normalizedDVRModuleRes l E X (hmn.trans hrm)
  let U₀ := (sfIntrinsicModuleEquivalence X
    (Padic.coefficientExtensionRing l E (n + 1))).functor
  let U₁ := (sfIntrinsicModuleEquivalence X
    (Padic.coefficientExtensionRing l E (m + 1))).functor
  let U₂ := (sfIntrinsicModuleEquivalence X
    (Padic.coefficientExtensionRing l E (r + 1))).functor
  let : U₀.Additive := sfIntrinsicModuleEquivalence_functor_additive
    (Padic.coefficientExtensionRing l E (n + 1)) X
  let : U₁.Additive := sfIntrinsicModuleEquivalence_functor_additive
    (Padic.coefficientExtensionRing l E (m + 1)) X
  let : U₂.Additive := sfIntrinsicModuleEquivalence_functor_additive
    (Padic.coefficientExtensionRing l E (r + 1)) X
  let : PreservesFiniteLimits G₀₁ := (normalizedDVRModuleRes_exact l E X hmn).1
  let : PreservesFiniteColimits G₀₁ := (normalizedDVRModuleRes_exact l E X hmn).2
  let : PreservesFiniteLimits G₁₂ := (normalizedDVRModuleRes_exact l E X hrm).1
  let : PreservesFiniteColimits G₁₂ := (normalizedDVRModuleRes_exact l E X hrm).2
  let : PreservesFiniteLimits G₀₂ :=
    (normalizedDVRModuleRes_exact l E X (hmn.trans hrm)).1
  let : PreservesFiniteColimits G₀₂ :=
    (normalizedDVRModuleRes_exact l E X (hmn.trans hrm)).2
  let cF := (Sheaf.restrictScalarsCompIso (ProEt.topology X)
    (finiteDualizingQuotient l E hrm) (finiteDualizingQuotient l E hmn)
    (finiteDualizingQuotient l E (hmn.trans hrm))
    (finiteDualizingQuotient_comp l E hrm hmn)).symm
  let cG : G₀₂ ≅ G₀₁ ⋙ G₁₂ := fdModuleComp l E X hrm hmn
  let q₀₁ := (fdOrdinaryRestriction l E X hmn).symm
  let q₁₂ := (fdOrdinaryRestriction l E X hrm).symm
  let q₀₂ := (fdOrdinaryRestriction l E X (hmn.trans hrm)).symm
  have hq := fd_generic_ordinary_forward X
    (finiteDualizingQuotientBase l E hrm) (finiteDualizingQuotientBase l E hmn)
    (finiteDualizingQuotientBase l E (hmn.trans hrm))
    (finiteDualizingQuotient_comp l E hrm hmn)
    (normalizedDVRQuotient l E X hrm) (normalizedDVRQuotient l E X hmn)
    (normalizedDVRQuotient l E X (hmn.trans hrm))
    ((integralCoefficientSheafSystem l E X).map_comp
      (homOfLE hrm).op (homOfLE hmn).op)
    (finiteDualizingRestriction_eq l E X hrm) (finiteDualizingRestriction_eq l E X hmn)
    (finiteDualizingRestriction_eq l E X (hmn.trans hrm))
  have hcF : Functor.mapDerivedCategoryNatIso cF ≪≫
      Functor.mapDerivedCategoryCompIso F₀₁ F₁₂ =
      (Sheaf.derivedRestrictScalarsCompIso (ProEt.topology X)
        (finiteDualizingQuotient_comp l E hrm hmn)).symm := by
    exact fd_fixed_derived_comp_inverse X
      (finiteDualizingQuotient l E hrm) (finiteDualizingQuotient l E hmn)
      (finiteDualizingQuotient l E (hmn.trans hrm))
      (finiteDualizingQuotient_comp l E hrm hmn)
  have hcG : Functor.mapDerivedCategoryNatIso cG ≪≫
      Functor.mapDerivedCategoryCompIso G₀₁ G₁₂ =
      (normalizedDVRResComp l E X hrm hmn).symm := by
    exact fd_derived_sheaf_comp_inverse X
      (normalizedDVRQuotient l E X hrm) (normalizedDVRQuotient l E X hmn)
      (normalizedDVRQuotient l E X (hmn.trans hrm))
      ((integralCoefficientSheafSystem l E X).map_comp
        (homOfLE hrm).op (homOfLE hmn).op)
  exact fd_derived_comp_app F₀₁ F₁₂ F₀₂ G₀₁ G₁₂ G₀₂ U₀ U₁ U₂
    q₀₁ q₁₂ q₀₂ cF cG hq
    (finiteDualizingIntrinsicRestriction l E X hmn)
    (finiteDualizingIntrinsicRestriction l E X hrm)
    (finiteDualizingIntrinsicRestriction l E X (hmn.trans hrm))
    (Sheaf.derivedRestrictScalarsCompIso (ProEt.topology X)
      (finiteDualizingQuotient_comp l E hrm hmn)).symm
    (normalizedDVRResComp l E X hrm hmn).symm
    (fd_derivedRestriction_symm l E X hmn)
    (fd_derivedRestriction_symm l E X hrm)
    (fd_derivedRestriction_symm l E X (hmn.trans hrm)) hcF hcG
    (DerivedCategory.Q.obj P)
end WeilConjectures
