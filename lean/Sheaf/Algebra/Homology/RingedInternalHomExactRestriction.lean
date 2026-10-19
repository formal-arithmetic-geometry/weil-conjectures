/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
import all Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.HomTensorTotal
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions

/-!
# Internal derived Hom calculus on small ringed sites

Source: Stacks Project, Cohomology on Sites, Tags 08J9, 08JB and 08JC
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).

The tensor functor is specified by its natural total-tensor comparison on K-flat
representatives. Restriction uses Mathlib's slice functors and their induced functors
on unbounded derived categories. The opposite triangulated structure reverses shifts.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

private theorem ringedSite_pushforward_limits
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {G : C ⥤ D} [Functor.IsContinuous G J K]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ) := by
  let T := SheafOfModules.forget.{u} S ⋙ PresheafOfModules.toPresheaf S.obj
  have : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ ⋙ T) := by
    change PreservesFiniteLimits
      ((SheafOfModules.forget.{u} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringLeft _ _ _).obj G.op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ T

private theorem ringedSite_pushforward_colimits
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {G : C ⥤ D} [Functor.IsContinuous G J K] [G.IsCocontinuous J K]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ) := by
  let H := G.sheafPushforwardContinuous AddCommGrpCat.{u} J K
  have : PreservesColimitsOfSize.{u, u} H :=
    (G.sheafAdjunctionCocontinuous AddCommGrpCat.{u} J K).leftAdjoint_preservesColimits
  let T := SheafOfModules.toSheaf.{u} S
  have : PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ ⋙ T) := by
    change PreservesFiniteColimits (SheafOfModules.toSheaf.{u} R ⋙ H)
    infer_instance
  have : ReflectsFiniteColimits T :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact preservesFiniteColimits_of_reflects_of_preserves _ T

/-- The overFunctor slice restriction is additive.

Source: Stacks Project, Tag 08JB, restriction to a localized ringed site.
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).

Proof: Restriction evaluates a sectionwise linear natural transformation on the slice site.
    Addition of such transformations is sectionwise, so restriction preserves addition. -/
@[instance]
theorem ringedSite_overFunctor_additive
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) (U :
    C) : (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R) U).Additive := by
  constructor
  intro X Y f g
  ext V x
  rfl

/-- The overFunctor slice restriction preserves finite limits.

Source: Stacks Project, Tag 08JB, restriction to a localized ringed site.
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).

Proof: Kernels and finite products of module sheaves are computed sectionwise. Evaluation along
    the forgetful functor from the slice preserves these constructions. The ring transport in
    overMap is the canonical identity on sections. -/
@[instance]
theorem ringedSite_overFunctor_limits
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) (U :
    C) : PreservesFiniteLimits (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U) := by
  exact ringedSite_pushforward_limits (𝟙 _)

/-- The overFunctor slice restriction preserves finite colimits.

Source: Stacks Project, Tag 08JB, restriction to a localized ringed site.
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).

Proof: Finite sums are sectionwise and cokernels are sheafified sectionwise cokernels. Coverings
    of an object of a slice are exactly coverings of its domain with the given structural arrow.
    Thus restriction commutes with sheafification and with these cokernels. The same argument
    applies to overMap. -/
@[instance]
theorem ringedSite_overFunctor_colimits
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) (U :
    C) : PreservesFiniteColimits (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U) := by
  exact ringedSite_pushforward_colimits (𝟙 _)

/-- The overMap slice restriction is additive.

Source: Stacks Project, Tag 08JB, restriction to a localized ringed site.
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).

Proof: Restriction evaluates a sectionwise linear natural transformation on the slice site.
    Addition of such transformations is sectionwise, so restriction preserves addition. -/
@[instance]
theorem ringedSite_overMap_additive
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) {U V
    : C} (f : V ⟶ U) : (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R) f).Additive := by
  constructor
  intro X Y f g
  ext V x
  rfl

/-- The overMap slice restriction preserves finite limits.

Source: Stacks Project, Tag 08JB, restriction to a localized ringed site.
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).

Proof: Kernels and finite products of module sheaves are computed sectionwise. Evaluation along
    the forgetful functor from the slice preserves these constructions. The ring transport in
    overMap is the canonical identity on sections. -/
@[instance]
theorem ringedSite_overMap_limits
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) {U V
    : C} (f : V ⟶ U) : PreservesFiniteLimits (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) f) := by
  exact ringedSite_pushforward_limits (Sheaf.pushforwardOverMapIso _ f).inv

/-- The overMap slice restriction preserves finite colimits.

Source: Stacks Project, Tag 08JB, restriction to a localized ringed site.
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).

Proof: Finite sums are sectionwise and cokernels are sheafified sectionwise cokernels. Coverings
    of an object of a slice are exactly coverings of its domain with the given structural arrow.
    Thus restriction commutes with sheafification and with these cokernels. The same argument
    applies to overMap. -/
@[instance]
theorem ringedSite_overMap_colimits
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) {U V
    : C} (f : V ⟶ U) : PreservesFiniteColimits (SheafOfModules.overMap.{u} ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R) f) := by
  exact ringedSite_pushforward_colimits (Sheaf.pushforwardOverMapIso _ f).inv

set_option maxHeartbeats 400000 in
-- Descending the trifunctor comparison requires several large tensor instances.
set_option backward.isDefEq.respectTransparency true in
/-- The tensor--Hom currying isomorphism is natural in all three derived objects.
The parameters P, hP, T and r specify the derived tensor in the node: total
tensor on K-flat representatives. They impose no condition on K, L or M.

Source: Stacks Project, Tag 08J9 (lemma-internal-hom).
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).

Proof: Use the concrete functorial flat resolution (lem-pc-kflat-resolution) to localize the
    full subcategory P at quasi-isomorphisms, and replace M functorially by a K-injective I
    (prop-pur-kinjective-resolutions-exist). Currying identifies Hom(A, Hom(B,I)) with Hom(Tot(A
    tensor B),I): Hom out of a direct sum is a product. Expanding the differential gives d_I
    f(a,b) - (-1)^n f(d_A a,b) - (-1)^(n+p) f(a,d_B b) on both sides. The inverse is uncurrying.
    Hom(B,I) is K-injective by lem-pur-hom-kflat-into-kinjective; K-flatness computes derived
    tensor. The representative comparisons of def-pur-derived-internal-hom and
    lem-pur-rhom-well-defined descend the chain isomorphism to the localization. Its formula
    commutes with precomposition in A,B and postcomposition in I, giving the displayed naturality
    equation. -/
theorem ringedInternalHom_tensor_adjunction
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))]
    (P : ObjectProperty (CochainComplex (ringedSiteModules.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R)) ℤ))
    (hP : ∀ X, P X ↔ X.IsAcyclicTensorKFlat)
    (T : (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))) × (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R))) ⥤ (DerivedCategory (ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))))
    (r : (P.ι.prod P.ι) ⋙ Functor.uncurry.obj
    ((@CategoryTheory.MonoidalCategory.curriedTensor (ringedSiteModules.{u} ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) _
    (SheafOfModules.monoidalCategory R)).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
    ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q)) ⋙ T) :
    ∃ e : ∀ K L M : (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R))),
    (derivedInternalHom.{u, w} J R).obj (op K, (derivedInternalHom.{u, w} J R).obj (op L, M)) ≅
    (derivedInternalHom.{u, w} J R).obj (op (T.obj (K, L)), M),
    ∀ (K L M K' L' M' : (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R)))) (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M'),
    (e K L M).hom ≫ (derivedInternalHom.{u, w} J R).map ((T.map (a, b)).op, c) =
    (derivedInternalHom.{u, w} J R).map (a.op, (derivedInternalHom.{u, w} J R).map (b.op, c)) ≫ (e
    K' L' M').hom := by
  classical
  let A := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.monoidalClosed_kfi (R := R)
  let := SheafOfModules.monoidalPreadditive_kfi R
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  have := SheafOfModules.hasExactColimits_int_kfi R
  let := SheafOfModules.hasFunctorialFlatResolution_kfi R
  have (X : A) : PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor A).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := MonoidalCategory.tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ (β_ X Y)) (by intros; simp))
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  let Q : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution A).some.reduced
  have flat (K : CochainComplex A ℤ) (hK : W.kFlat K) : P K := by
    apply (hP K).mpr
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic] at hK
    intro Z hZ
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (CochainComplex.mapBifunctor Z K (MonoidalCategory.curriedTensor A))).mp
        (hK _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic Z).mpr hZ)).2
  let B := ObjectProperty.lift P Λ.resolutionFunctor
    (fun K ↦ flat _ (Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K))
  let Φ : LocalizerMorphism (W.inverseImage P.ι) W :=
    { functor := P.ι
      map := fun _ _ _ h ↦ h }
  have : Φ.IsInduced := ⟨rfl⟩
  have : Φ.IsLocalizedEquivalence :=
    Φ.isLocalizedEquivalence_of_functorial_left_resolutions (ρ := B) Λ.resolutionNatTrans
      (fun K ↦ by
        dsimp only [W]
        rw [HomologicalComplex.mem_quasiIso_iff]
        infer_instance) rfl
  have : (P.ι ⋙ Q).IsLocalization (W.inverseImage P.ι) :=
    LocalizerMorphism.IsLocalizedEquivalence.isLocalization Φ Q
  let D := DerivedCategory A
  let K := CochainComplex A ℤ
  let S := P.FullSubcategoryᵒᵖ × (P.FullSubcategoryᵒᵖ × K)
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  let H := Functor.uncurry.obj (homComplexFunctor (R := R))
  let F := derivedInternalHom.{u, w} J R
  obtain ⟨e₀⟩ := derivedInternalHom_comparison J R I η (fun M ↦
    ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2,
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M⟩)
  have rep (G : S ⥤ Kᵒᵖ × K) (hG : ∀ X, (G.obj X).2.IsKInjective) :
      Nonempty (G ⋙ (Q.op.prod Q) ⋙ F ≅ G ⋙ H ⋙ Q) := by
    let α := Functor.whiskerLeft G
      (Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 Kᵒᵖ)) η) (H ⋙ Q))
    have : IsIso α := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro X
      have : ((G.obj X).2).IsKInjective := hG X
      have : (I.obj (G.obj X).2).IsKInjective :=
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A _
      have : QuasiIso (η.app (G.obj X).2) :=
        (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A _).2
      apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
      exact quasiIso_homComplex_map (I' := (G.obj X).2)
        (I := I.obj (G.obj X).2) (η.app (G.obj X).2) (𝟙 (G.obj X).1.unop)
    exact ⟨Functor.isoWhiskerLeft G e₀ ≪≫ (asIso α).symm⟩
  let a := CategoryTheory.Prod.fst P.FullSubcategoryᵒᵖ (P.FullSubcategoryᵒᵖ × K) ⋙ P.ι.op
  let b := CategoryTheory.Prod.snd P.FullSubcategoryᵒᵖ (P.FullSubcategoryᵒᵖ × K) ⋙
    CategoryTheory.Prod.fst P.FullSubcategoryᵒᵖ K ⋙ P.ι.op
  let c := CategoryTheory.Prod.snd P.FullSubcategoryᵒᵖ (P.FullSubcategoryᵒᵖ × K) ⋙
    CategoryTheory.Prod.snd P.FullSubcategoryᵒᵖ K
  let inner := (b.prod' (c ⋙ I)) ⋙ H
  have hinner (X : S) : (inner.obj X).IsKInjective :=
    CochainComplex.isKInjective_homComplex_of_isKFlat (P.ι.obj X.2.1.unop)
      (I.obj X.2.2) ((hP _).mp X.2.1.unop.property)
  let eInner : (b.prod' c) ⋙ (Q.op.prod Q) ⋙ F ≅ inner ⋙ Q :=
    Functor.isoWhiskerLeft (b.prod' c) e₀
  let eLeft₁ := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (Functor.diag S)
      (NatIso.prod (Iso.refl (a ⋙ Q.op)) eInner)) F
  obtain ⟨eLeft₂⟩ := rep (a.prod' inner) hinner
  let eLeft : (a ⋙ Q.op).prod' ((b.prod' c) ⋙ (Q.op.prod Q) ⋙ F) ⋙ F ≅
      (a.prod' inner) ⋙ H ⋙ Q := eLeft₁ ≪≫ eLeft₂
  let tensor := (a.prod' b) ⋙ (prodOpEquiv K (D := K)).inverse ⋙
    (Functor.uncurry.obj ((MonoidalCategory.curriedTensor A).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ))).op
  let eRight : (tensor ⋙ Q.op).prod' (c ⋙ Q) ⋙ F ≅
      (tensor.prod' (c ⋙ I)) ⋙ H ⋙ Q :=
    Functor.isoWhiskerLeft (tensor.prod' c) e₀
  have tensor_map (K₁ K₂ L₁ L₂ : K) (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) :
      (Functor.uncurry.obj ((MonoidalCategory.curriedTensor A).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ))).map (X := (K₁, K₂)) (Y := (L₁, L₂)) (f, g) =
      HomologicalComplex.mapBifunctorMap f g (MonoidalCategory.curriedTensor A) (.up ℤ) := by
    change HomologicalComplex.mapBifunctorMap f (𝟙 K₂)
      (MonoidalCategory.curriedTensor A) (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 L₁) g
        (MonoidalCategory.curriedTensor A) (.up ℤ) = _
    simp only [HomologicalComplex.mapBifunctorMap, Functor.map_id, NatTrans.id_app,
      Category.id_comp, Category.comp_id, ← HomologicalComplex₂.total.map_comp]
  obtain ⟨eC, heC⟩ := homComplex_tensorTotal_iso R
  let eChain : (a.prod' inner) ⋙ H ≅ (tensor.prod' (c ⋙ I)) ⋙ H :=
    NatIso.ofComponents (fun X ↦ eC X.1.unop.obj X.2.1.unop.obj (I.obj X.2.2))
      (fun {X Y} f ↦ by
        change
          ((((homComplexFunctor (R := R)).map f.1.unop.hom.op).app
            (homComplex (R := R) X.2.1.unop.obj (I.obj X.2.2))) ≫
              ((homComplexFunctor (R := R)).obj (op Y.1.unop.obj)).map
                ((((homComplexFunctor (R := R)).map f.2.1.unop.hom.op).app
                  (I.obj X.2.2)) ≫
                    ((homComplexFunctor (R := R)).obj (op Y.2.1.unop.obj)).map
                      (I.map f.2.2))) ≫
            (eC Y.1.unop.obj Y.2.1.unop.obj (I.obj Y.2.2)).hom =
          (eC X.1.unop.obj X.2.1.unop.obj (I.obj X.2.2)).hom ≫
            ((((homComplexFunctor (R := R)).map
              ((Functor.uncurry.obj ((MonoidalCategory.curriedTensor A).map₂HomologicalComplex
                (.up ℤ) (.up ℤ) (.up ℤ))).map
                  (X := (Y.1.unop.obj, Y.2.1.unop.obj))
                  (Y := (X.1.unop.obj, X.2.1.unop.obj))
                  (f.1.unop.hom, f.2.1.unop.hom)).op).app (I.obj X.2.2)) ≫
                ((homComplexFunctor (R := R)).obj
                  (op (HomologicalComplex.mapBifunctor Y.1.unop.obj Y.2.1.unop.obj
                    (MonoidalCategory.curriedTensor A) (.up ℤ)))).map (I.map f.2.2))
        rw [tensor_map]
        exact (Category.assoc _ _ _).trans
          (heC X.1.unop.obj Y.1.unop.obj X.2.1.unop.obj Y.2.1.unop.obj
          (I.obj X.2.2) (I.obj Y.2.2) f.1.unop.hom f.2.1.unop.hom (I.map f.2.2)))
  let E := Dᵒᵖ × (Dᵒᵖ × D)
  let ad := CategoryTheory.Prod.fst Dᵒᵖ (Dᵒᵖ × D)
  let bd := CategoryTheory.Prod.snd Dᵒᵖ (Dᵒᵖ × D) ⋙ CategoryTheory.Prod.fst Dᵒᵖ D
  let cd := CategoryTheory.Prod.snd Dᵒᵖ (Dᵒᵖ × D) ⋙ CategoryTheory.Prod.snd Dᵒᵖ D
  let td := (ad.prod' bd) ⋙ (prodOpEquiv D (D := D)).inverse ⋙ T.op
  let FL : E ⥤ D := ad.prod' ((bd.prod' cd) ⋙ F) ⋙ F
  let FR : E ⥤ D := td.prod' cd ⋙ F
  let L := (P.ι ⋙ Q).op.prod ((P.ι ⋙ Q).op.prod Q)
  let p12 := ((CategoryTheory.Prod.fst P.FullSubcategoryᵒᵖ
    (P.FullSubcategoryᵒᵖ × K)).prod'
      (CategoryTheory.Prod.snd P.FullSubcategoryᵒᵖ (P.FullSubcategoryᵒᵖ × K) ⋙
        CategoryTheory.Prod.fst P.FullSubcategoryᵒᵖ K)) ⋙
          (prodOpEquiv P.FullSubcategory (D := P.FullSubcategory)).inverse
  let er : tensor ⋙ Q.op ≅ L ⋙ td :=
    Functor.isoWhiskerLeft p12 (NatIso.op r).symm
  let eRight₂ : (tensor ⋙ Q.op).prod' (c ⋙ Q) ⋙ F ≅ L ⋙ FR :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (Functor.diag S) (NatIso.prod er (Iso.refl (c ⋙ Q)))) F
  let ePre : L ⋙ FL ≅ L ⋙ FR :=
    eLeft ≪≫ Functor.isoWhiskerRight eChain Q ≪≫ eRight.symm ≪≫ eRight₂
  let WL := (W.inverseImage P.ι).op.prod ((W.inverseImage P.ι).op.prod W)
  let e : FL ≅ FR := (Localization.fullyFaithfulWhiskeringLeft L WL D).preimageIso ePre
  refine ⟨fun K L M ↦ e.app (op K, op L, M), ?_⟩
  intro K L M K' L' M' a b c
  exact (e.hom.naturality (show (op K, op L, M) ⟶ (op K', op L', M') from
    (a.op, b.op, c))).symm

/-- Derived internal Hom commutes naturally with slice restriction, compatibly
with successive restrictions. The comparison for V to U, followed by transport
along the canonical derived overFunctorMap, equals direct restriction to V.

Source: Stacks Project, Tag 08JB (lemma-restriction-RHom-to-U).
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).

Proof: Represent M by a K-injective I and L by A. The sections of Hom(A,I) restricted to U, over
    each arrow W to U, are the same families of local maps as the sections of Hom(A restricted to
    U, I restricted to U); their differentials coincide. Restriction preserves K-injectivity
    (lem-pur-kinjective-restrict-localized), so these complexes compute derived internal Hom. The
    same construction for Over.map f gives s. On every object mapping to V both successive and
    direct comparisons are identity on these families, after the canonical overFunctorMap
    transport. This proves the displayed equation; pre- and postcomposition give naturality.
    Independence of representatives follows from lem-pur-rhom-well-defined. -/
theorem ringedInternalHom_restriction
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))] [hDCU : ∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
    (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over U))] :
    ∃ (e : ∀ U : C, (derivedInternalHom.{u, w} J R) ⋙ (SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).mapDerivedCategory ≅
    ((SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
    R) U).mapDerivedCategory.op.prod (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U).mapDerivedCategory) ⋙ (@derivedInternalHom.{u, w}
    (Over U) inferInstance (J.over U) (R.over U) (hDCU U)))
    (s : ∀ (U V : C) (f : V ⟶ U), (@derivedInternalHom.{u, w} (Over U) inferInstance (J.over U)
    (R.over U) (hDCU U)) ⋙ (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R) f).mapDerivedCategory ≅
    ((SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    f).mapDerivedCategory.op.prod (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) f).mapDerivedCategory) ⋙ (@derivedInternalHom.{u, w}
    (Over V) inferInstance (J.over V) (R.over V) (hDCU V))),
    ∀ (U V : C) (f : V ⟶ U) (L M : (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))),
    (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    f).mapDerivedCategory.map ((e U).hom.app (op L, M)) ≫
    (s U V f).hom.app (op ((SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U).mapDerivedCategory.obj L),
    (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    U).mapDerivedCategory.obj M) ≫
    (@derivedInternalHom.{u, w} (Over V) inferInstance (J.over V) (R.over V) (hDCU V)).map
    (X := (op ((SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R) f).mapDerivedCategory.obj ((SheafOfModules.overFunctor.{u} ((sheafCompose
    J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).mapDerivedCategory.obj L)),
    (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    f).mapDerivedCategory.obj ((SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U).mapDerivedCategory.obj M)))
    (Y := (op ((SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R) V).mapDerivedCategory.obj L), (SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) V).mapDerivedCategory.obj M))
    (((((Functor.mapDerivedCategoryCompIso (SheafOfModules.overFunctor.{u} ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U) (SheafOfModules.overMap.{u} ((sheafCompose J
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R) f)).symm ≪≫ Functor.mapDerivedCategoryNatIso
    (SheafOfModules.overFunctorMap ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    f))).inv.app L).op, (((Functor.mapDerivedCategoryCompIso (SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U) (SheafOfModules.overMap.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) f)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) f))).hom.app M) =
    (((Functor.mapDerivedCategoryCompIso (SheafOfModules.overFunctor.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) U) (SheafOfModules.overMap.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R) f)).symm ≪≫ Functor.mapDerivedCategoryNatIso
    (SheafOfModules.overFunctorMap ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    f))).hom.app ((derivedInternalHom.{u, w} J R).obj (op L, M)) ≫
    (e V).hom.app (op L, M) := by
  sorry

/-- Internal derived Hom preserves distinguished triangles in each variable
and commutes with shifts. The first variable is a functor from the opposite
triangulated category, whose shift by m is the original shift by -m.

Source: Stacks Project, Tag 08JC (lemma-RHom-triangulated).
(blueprint: lem-weil-pbc-ringed-internal-hom-exact-restriction).

Proof: For the first variable fix a K-injective I representing M. The graded splitting of the cone
    gives Hom(C(f),I) as Hom(B,I) plus Hom(A[1],I). Put X=Hom(B,I), Y=Hom(A,I), h=f*. In degree n
    its differential is (d_X x, d_Y y+(-1)^(n+1)h(x)); (x,y) maps to ((-1)^(n-1)y,x) in C(h)[-1].
    Rotation gives the reversed distinguished triangle. For the second variable choose K-injective
    representatives J,I; lem-weil-pbc-kinjective-hom-derived represents the morphism by a chain
    map g. TR3 and lem-sf-triangle-morphism-iso identify its cone triangle with the given
    triangle. Its cone is K-injective: Hom from any acyclic test complex is the cone of two
    acyclic ordinary Hom complexes, hence acyclic. Then Hom(A,C(g)) is the cone of Hom(A,g), with
    differential (dx+Hom(A,g)y,-dy). These cone calculations descend by
    lem-pur-homotopy-category-triangulated and lem-pur-rhom-well-defined. The natural shift
    identifications from lem-pur-derived-internal-hom-shift-left and
    lem-pur-derived-internal-hom-shift-right give H(P[m],Q)=H(P,Q)[-m] and H(P,Q[n])=H(P,Q)[n].
    The cone signs give the required triangulated structures. Only finite splittings occur, so no
    boundedness or finite-generation hypothesis is used. -/
theorem ringedInternalHom_exact
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))] :
    (∀ L : (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))), ∃ _ : ((Functor.curry.obj (derivedInternalHom.{u, w} J R)).obj (op
    L)).CommShift ℤ,
    ((Functor.curry.obj (derivedInternalHom.{u, w} J R)).obj (op L)).IsTriangulated) ∧
    (∀ M : (DerivedCategory (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
    RingCat.{u})).obj R))), ∃ _ : ((Functor.curry.obj (derivedInternalHom.{u, w} J R)).flip.obj
    M).CommShift ℤ,
    ((Functor.curry.obj (derivedInternalHom.{u, w} J R)).flip.obj M).IsTriangulated) := by
  sorry

end CategoryTheory
