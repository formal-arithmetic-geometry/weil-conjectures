/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses

/-! # Derived internal Hom without identifying the site universes

This is the same Hom-complex localization as derivedInternalHom, with the module
universe large enough to contain the site objects and arrows independently.
The ordinary-etale fixed-coefficient specialization is also publicly available through
Etale.derivedHom and Etale.derivedTensorHomAdjunction. Their original definitions
are imported directly; the generic construction and its comparisons are unchanged.

## References

* Stacks Project, Sections 08J7, 0A8X and 07A5, and Lemma 0A95
-/

@[expose] public section

set_option autoImplicit false

universe c v r w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The usual Hom-complex bifunctor with functorial K-injective replacement
inverts quasi-isomorphisms in each variable. -/
theorem derivedInternalHomOfUniverses_inverts
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (I : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ ⥤
      CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (η : 𝟭 (CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) ⟶ I)
    (hI : ∀ M : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ,
      QuasiIso (η.app M) ∧ (I.obj M).IsKInjective) :
    ((HomologicalComplex.quasiIso
      (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) (ComplexShape.up ℤ)).op.prod
      (HomologicalComplex.quasiIso
        (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
        (ComplexShape.up ℤ))).IsInvertedBy
        ((𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙
          DerivedCategory.Q) := by
  intro X Y f hf
  have : QuasiIso f.1.unop := hf.1
  have : QuasiIso f.2 := hf.2
  have : QuasiIso (η.app X.2) := (hI X.2).1
  have : QuasiIso (η.app Y.2) := (hI Y.2).1
  have : (I.obj X.2).IsKInjective := (hI X.2).2
  have : (I.obj Y.2).IsKInjective := (hI Y.2).2
  have hη : QuasiIso ((η.app X.2) ≫ I.map f.2) := by
    rw [← η.naturality f.2]
    dsimp
    infer_instance
  have : QuasiIso (I.map f.2) :=
    (quasiIso_iff_comp_left _ _).mp hη
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
  exact quasiIso_homComplex_mapOfUniverses.{c, v, r} (I.map f.2) f.1.unop

/-- Derived internal Hom on the full module derived category, computed with the
canonical functorial K-injective replacement in its second variable. -/
noncomputable def derivedInternalHomOfUniverses
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))] :
    (DerivedCategory (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))ᵒᵖ ×
      DerivedCategory (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ⥤
        DerivedCategory (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :=
  letI : IsGrothendieckAbelian.{max c v r} (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  Localization.lift
    ((𝟭 _).prod (CochainComplex.kInjectiveResolutionFunctor.{max c v r} _) ⋙
      Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ DerivedCategory.Q)
    (derivedInternalHomOfUniverses_inverts.{c, v, r, w} J R _
      (CochainComplex.toKInjectiveResolution.{max c v r} _)
      (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r}
        _ M).2, CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r}
          _ M⟩))
    ((DerivedCategory.Q).op.prod DerivedCategory.Q)

/-- Comparison with any functorial K-injective replacement, naturally in both variables. -/
theorem derivedInternalHomOfUniverses_comparison
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (I : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ ⥤
      CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (η : 𝟭 (CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) ⟶ I)
    (hI : ∀ M : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ,
      QuasiIso (η.app M) ∧ (I.obj M).IsKInjective) :
    Nonempty (((DerivedCategory.Q).op.prod DerivedCategory.Q) ⋙
      derivedInternalHomOfUniverses.{c, v, r, w} J R ≅
        (𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙
          DerivedCategory.Q) := by
  let A := SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
  let : IsGrothendieckAbelian.{max c v r} A :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  let I₀ := CochainComplex.kInjectiveResolutionFunctor.{max c v r} A
  let η₀ := CochainComplex.toKInjectiveResolution.{max c v r} A
  let H := Functor.uncurry.obj
    (homComplexFunctor.{c, v, max c v r, max c v r} (R := R)) ⋙ DerivedCategory.Q.{w}
  have hinv (F G : CochainComplex A ℤ ⥤ CochainComplex A ℤ) (α : F ⟶ G)
      (hα : ∀ M, QuasiIso (α.app M))
      (hF : ∀ M, (F.obj M).IsKInjective)
      (hG : ∀ M, (G.obj M).IsKInjective) :
      IsIso (Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 _)) α) H) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    have : QuasiIso (α.app X.2) := hα X.2
    have : (F.obj X.2).IsKInjective := hF X.2
    have : (G.obj X.2).IsKInjective := hG X.2
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
    exact quasiIso_homComplex_mapOfUniverses.{c, v, r} (α.app X.2) (𝟙 X.1.unop)
  let α := Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 _)) (Functor.whiskerLeft I₀ η)) H
  let β := Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 _)) (Functor.whiskerRight η₀ I)) H
  have : IsIso α := hinv _ _ _ (fun M ↦ (hI (I₀.obj M)).1)
    (fun M ↦ CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r} A M)
    (fun M ↦ (hI (I₀.obj M)).2)
  have : IsIso β := hinv _ _ _ (fun M ↦ by
      have : QuasiIso (η.app M) := (hI M).1
      have : QuasiIso (η.app (I₀.obj M)) := (hI (I₀.obj M)).1
      have : QuasiIso (η₀.app M) :=
        (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} A M).2
      apply (quasiIso_iff_comp_left (η.app M) _).mp
      change QuasiIso (η.app M ≫ I.map (η₀.app M))
      have hn := η.naturality (η₀.app M)
      dsimp at hn
      rw [← hn]
      infer_instance)
    (fun M ↦ (hI M).2) (fun M ↦ (hI (I₀.obj M)).2)
  exact ⟨Localization.fac _
      (derivedInternalHomOfUniverses_inverts.{c, v, r, w} J R I₀ η₀ (fun M ↦
        ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} A M).2,
          CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r} A M⟩))
      ((DerivedCategory.Q).op.prod DerivedCategory.Q) ≪≫
    asIso α ≪≫ (asIso β).symm⟩

/-- Independence of the source representative and of any K-injective target representative. -/
theorem derivedInternalHomOfUniverses_obj_iso
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (L M : DerivedCategory (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
    (Lc Ic : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    [Ic.IsKInjective]
    (_eL : DerivedCategory.Q.obj Lc ≅ L) (_eM : DerivedCategory.Q.obj Ic ≅ M) :
    Nonempty ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op L, M) ≅
      DerivedCategory.Q.obj (homComplex (R := R) Lc Ic)) := by
  let A := SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
  let : IsGrothendieckAbelian.{max c v r} A :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  let I₀ := CochainComplex.kInjectiveResolutionFunctor.{max c v r} A
  let η₀ := CochainComplex.toKInjectiveResolution.{max c v r} A
  obtain ⟨e⟩ := derivedInternalHomOfUniverses_comparison.{c, v, r, w} J R I₀ η₀ (fun M ↦
    ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} A M).2,
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r} A M⟩)
  have : QuasiIso (η₀.app Ic) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} A Ic).2
  have : (I₀.obj Ic).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r} A Ic
  let f := ((homComplexFunctor (R := R)).obj (op Lc)).map (η₀.app Ic)
  have : QuasiIso f := by
    simpa using quasiIso_homComplex_mapOfUniverses.{c, v, r}
      (I' := Ic) (I := I₀.obj Ic) (η₀.app Ic) (𝟙 Lc)
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).mpr inferInstance
  exact ⟨(derivedInternalHomOfUniverses.{c, v, r, w} J R).mapIso (_eL.op.prod _eM.symm) ≪≫
    e.app (op Lc, Ic) ≪≫ (asIso (DerivedCategory.Q.map f)).symm⟩

end CategoryTheory
