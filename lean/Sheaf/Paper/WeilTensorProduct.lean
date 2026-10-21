/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Paper.PbcWeilCategory
public import Sheaf.Paper.WeilCompletedTensorReflector
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.ResolvingRepresentativeWhiskering
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.RingTheory.Localization.BaseChange
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided

/-!
# Completed adic tensor and its geometric Frobenius

Source: blueprint, sec-six-functors/sk-rem-sf-pf-done, order 2107
(blueprint: def-wf-tensor-product).
Derived tensor means K-flat tensor, then the explicit intrinsic Koszul completion,
then raw scalar localization. No preservation or exactness on Weil pairs is assumed.

The finite coefficient stages use `pbcStageDatum` and `pbcStageUniformizer`:
these are the valuation-ring data transported along `Shrink.algEquiv`, with the
actual field inclusions conjugated by that canonical equivalence.

## Main definitions

- `SheafOfModules.wfSiteDerivedTensor`: the localized K-flat tensor bifunctor.
- `wfIntegralTensor`, `wfRationalTensor`: completed integral and rational tensor.
- `wfRationalTensorPullback`: the normalized Frobenius/tensor comparison.
- `WeilConjectures.wfTensorFrobenius`: tensor of the given Weil structures.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

attribute [local irreducible] ScalarLocalization.composition
namespace SheafOfModules


/-- The derived tensor supplied by localization of the flat-term K-flat subcategory.
The representative comparison in site_derived_tensor_descent determines this functor
up to the unique compatible natural isomorphism; no functorial representatives are chosen.
Source: Stacks 06YS and 06YT (blueprint: def-wf-tensor-product). -/
def wfSiteDerivedTensor {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v})
    [HasDerivedCategory.{w} (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))] :
    DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ×
    DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ⥤
    DerivedCategory (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) :=
  (wf_site_derived_tensor_descent.{u, v, w, 0, 0} J R).choose_spec.2.2.1.choose_spec.2.choose

set_option backward.isDefEq.respectTransparency false in
open MonoidalCategory in
private theorem wfTensorLeft_quasiIso
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    {R : Sheaf J CommRingCat.{max u v}}
    {K E E' : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ} (α : E ⟶ E')
    (hα : QuasiIso α) (hK : CochainComplex.IsAcyclicTensorKFlat (J := J) (R := R) K) :
    let := monoidalCategory R
    QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 K) α
      (MonoidalCategory.curriedTensor _) (.up ℤ)) := by
  let := cochainModulesMonoidal R
  let := cochainModulesSymmetric R
  let := cochainModulesPreadditive R
  have hk : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat K := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro N hN
    obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
    have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (CochainComplex.mapBifunctor N K (curriedTensor _))).2 (hK N hN)
    refine ⟨?_, hr⟩
    exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr
  exact hk.whiskerLeft hα

set_option backward.isDefEq.respectTransparency false in
/-- A flat-term K-flat first argument computes tensor against every second complex.
Source: Stacks 06YS and 06YT (blueprint: def-wf-tensor-product).
Proof: choose a flat-term K-flat resolution V→D of the second complex. K-flatness
of P and signed symmetry make Tot(P⊗V)→Tot(P⊗D) a quasi-isomorphism. The descent
comparison computes tensor on P,V. Localize the quasi-isomorphism V→D and use
functoriality in the second variable. Compose these three isomorphisms. Replacing
P by any flat-term K-flat resolution of a representative of M gives the stated
first-variable formula, with no functorial choice of representatives.
-/
theorem wfSiteDerivedTensor_first {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify J AddCommGrpCat.{max u v}]
    (R : Sheaf J CommRingCat.{max u v})
    [HasDerivedCategory.{w} (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))]
    (P D : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)
    (_hP : CochainComplex.IsAcyclicTensorKFlat (J := J) (R := R) P)
    (_hflat : ∀ n : ℤ, CategoryTheory.exactFunctor _ _
      ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) _
          (SheafOfModules.monoidalCategory.{v, u, max u v} R)).flip.obj (P.X n))) :
    Nonempty (DerivedCategory.Q.obj
        (CochainComplex.mapBifunctor P D
          (@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{max u v}
            ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) _
              (SheafOfModules.monoidalCategory.{v, u, max u v} R))) ≅
      (wfSiteDerivedTensor J R).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj D)) := by
  let := monoidalCategory R
  obtain ⟨V, v, hV, hflatV, hv, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (C := C) (J := J) (R := R) D
  have hV' : CochainComplex.IsAcyclicTensorKFlat (J := J) (R := R) V := hV
  let h := wf_site_derived_tensor_descent.{u, v, w, 0, 0} J R
  let S := h.choose
  have hS := h.choose_spec.1
  let c := h.choose_spec.2.2.1.choose_spec.1.some
  let d := h.choose_spec.2.2.1.choose_spec.2.choose_spec.some
  let p : S.FullSubcategory := ⟨(HomotopyCategory.quotient _ _).obj P,
    (hS _).2 ⟨_hP, _hflat⟩⟩
  let q : S.FullSubcategory := ⟨(HomotopyCategory.quotient _ _).obj V,
    (hS _).2 ⟨hV', hflatV⟩⟩
  let f := HomologicalComplex.mapBifunctorMap (𝟙 P) v
    (MonoidalCategory.curriedTensor _) (.up ℤ)
  have : QuasiIso f := wfTensorLeft_quasiIso v hv _hP
  have : IsIso (DerivedCategory.Q.map f) := by infer_instance
  have : QuasiIso v := hv
  exact ⟨(asIso (DerivedCategory.Q.map f)).symm ≪≫
    (DerivedCategory.Qh.mapIso (c.app (P, V))).symm ≪≫ d.app (p, q) ≪≫
      (wfSiteDerivedTensor J R).mapIso
        (Iso.prod (Iso.refl _) (asIso (DerivedCategory.Q.map v)))⟩

end SheafOfModules
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] SheafOfModules.wfSiteDerivedTensor
  intrinsicCompletion intrinsicCompletionUnit intrinsicCompletionComplex
  intrinsicCompletionComplexUnit
set_option backward.isDefEq.respectTransparency false in
private theorem scalarLocalization_precomp_injective
    {R : Type u} [CommRing R] {C : Type v} [Category C]
    [Preadditive C] [Linear R C] (p : R) {E : Type w} [Category E]
    (F G : ScalarLocalization R C p ⥤ E)
    (h : ScalarLocalization.localization R C p ⋙ F =
      ScalarLocalization.localization R C p ⋙ G) : F = G := by
  classical
  let Q := ScalarLocalization.localization R C p
  let e := eqToIso h
  let i (K : ScalarLocalization R C p) : F.obj K ≅ G.obj K := e.app K.obj
  have nat {K L : ScalarLocalization R C p} (f : K.obj ⟶ L.obj) :
      F.map (Q.map f) ≫ (i L).hom = (i K).hom ≫ G.map (Q.map f) :=
    e.hom.naturality f
  have nat_all : ∀ {K L : ScalarLocalization R C p} (f : K ⟶ L),
      F.map f ≫ (i L).hom = (i K).hom ≫ G.map f := by
    rintro ⟨K⟩ ⟨L⟩ f
    let K : ScalarLocalization R C p := ⟨K⟩
    let L : ScalarLocalization R C p := ⟨L⟩
    obtain ⟨⟨g, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers p)
      (TensorProduct.mk R (Localization.Away p) (K.obj ⟶ L.obj) 1) f
    let z : K.obj ⟶ K.obj := (s : R) • 𝟙 K.obj
    have hz : Q.map z ≫ f = Q.map g := by
      change ScalarLocalization.composition R C p _ _ _ f (1 ⊗ₜ[R] z) = 1 ⊗ₜ[R] g
      have ht : (1 : Localization.Away p) ⊗ₜ[R] z =
          algebraMap R (Localization.Away p) (s : R) • (𝟙 K) := by
        dsimp [z]
        rw [TensorProduct.tmul_smul]
        exact (algebraMap_smul (M := Localization.Away p ⊗[R] (K.obj ⟶ K.obj))
          (Localization.Away p) (s : R) (1 ⊗ₜ[R] 𝟙 K.obj)).symm
      rw [ht, map_smul]
      change algebraMap R (Localization.Away p) (s : R) • (𝟙 K ≫ f) =
        1 ⊗ₜ[R] g
      rw [Category.id_comp]
      change algebraMap R (Localization.Away p) (s : R) •
        (f : Localization.Away p ⊗[R] (K.obj ⟶ L.obj)) = 1 ⊗ₜ[R] g
      have : IsScalarTower R (Localization.Away p) (K ⟶ L) :=
        inferInstanceAs (IsScalarTower R (Localization.Away p)
          (Localization.Away p ⊗[R] (K.obj ⟶ L.obj)))
      rw [algebraMap_smul]
      exact hs
    have hu := IsLocalization.map_units (Localization.Away p) s
    let j : K ≅ K :=
      { hom := (hu.unit : Localization.Away p) • 𝟙 K
        inv := ((hu.unit⁻¹ : (Localization.Away p)ˣ) : Localization.Away p) • 𝟙 K
        hom_inv_id := by simp [Linear.comp_smul, smul_smul]
        inv_hom_id := by simp [Linear.comp_smul, smul_smul] }
    have hj : Q.map z = j.hom := by
      change (1 : Localization.Away p) ⊗ₜ[R] ((s : R) • 𝟙 K.obj) = _
      rw [TensorProduct.tmul_smul]
      change (s : R) • (1 ⊗ₜ[R] 𝟙 K.obj) =
        (hu.unit : Localization.Away p) • (1 ⊗ₜ[R] 𝟙 K.obj)
      rw [hu.unit_spec, algebraMap_smul]
    have : IsIso (Q.map z) := by rw [hj]; exact j.isIso_hom
    apply (cancel_epi (F.map (Q.map z))).1
    rw [← Category.assoc, ← F.map_comp, hz, nat]
    rw [← Category.assoc, nat z, Category.assoc, ← G.map_comp, hz]
  refine CategoryTheory.Functor.ext
    (fun K ↦ CategoryTheory.Functor.congr_obj h K.obj) ?_
  intro K L f
  apply (cancel_mono (i L).hom).1
  have hi (K : ScalarLocalization R C p) : (i K).hom =
      eqToHom (CategoryTheory.Functor.congr_obj h K.obj) := eqToHom_app h K.obj
  simpa only [hi, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    using nat_all f

private theorem scalarLocalization_mapHom_tmul
    {R : Type u} [CommRing R] {C : Type v} [Category C]
    [Preadditive C] [Linear R C] (p : R) (H : C ⥤ C) [H.Additive] [H.Linear R]
    {M N : C} (s : Localization.Away p) (f : M ⟶ N) :
    ScalarLocalization.mapHom R C p H M N (s ⊗ₜ[R] f) = s ⊗ₜ[R] H.map f :=
  LinearMap.baseChange_tmul _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem scalarLocalization_bilinear_naturality
    {R : Type u} [CommRing R] {C : Type v} [Category C]
    [Preadditive C] [Linear R C] (p : R) (H : C ⥤ C) [H.Additive] [H.Linear R]
    {M M' N N' S S' T T' : C}
    (b : (Localization.Away p ⊗[R] (M ⟶ M')) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[R] (N ⟶ N')) →ₗ[Localization.Away p]
        (Localization.Away p ⊗[R] (S ⟶ S')))
    (b' : (Localization.Away p ⊗[R] (H.obj M ⟶ H.obj M')) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[R] (H.obj N ⟶ H.obj N')) →ₗ[Localization.Away p]
        (Localization.Away p ⊗[R] (T ⟶ T')))
    (t : (M ⟶ M') → (N ⟶ N') → (S ⟶ S'))
    (t' : (H.obj M ⟶ H.obj M') → (H.obj N ⟶ H.obj N') → (T ⟶ T'))
    (hb : ∀ f g s z, b (s ⊗ₜ[R] f) (z ⊗ₜ[R] g) = (s * z) ⊗ₜ[R] (t f g))
    (hb' : ∀ f g s t, b' (s ⊗ₜ[R] f) (t ⊗ₜ[R] g) = (s * t) ⊗ₜ[R] (t' f g))
    (i : H.obj S ⟶ T) (i' : H.obj S' ⟶ T')
    (hi : ∀ f g, H.map (t f g) ≫ i' = i ≫ t' (H.map f) (H.map g))
    (f : Localization.Away p ⊗[R] (M ⟶ M'))
    (g : Localization.Away p ⊗[R] (N ⟶ N')) :
    ScalarLocalization.composition R C p _ _ _ (1 ⊗ₜ[R] i')
        (ScalarLocalization.mapHom R C p H _ _ (b f g)) =
      ScalarLocalization.composition R C p _ _ _
        (b' (ScalarLocalization.mapHom R C p H _ _ f)
          (ScalarLocalization.mapHom R C p H _ _ g)) (1 ⊗ₜ[R] i) := by
  induction f using TensorProduct.induction_on with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul s f =>
    induction g using TensorProduct.induction_on with
    | zero => simp
    | add g₁ g₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
    | tmul t g =>
      rw [hb, scalarLocalization_mapHom_tmul, scalarLocalization_mapHom_tmul,
        scalarLocalization_mapHom_tmul, hb', ScalarLocalization.composition_tmul,
        ScalarLocalization.composition_tmul, one_mul, mul_one, hi]

variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)

/-- Ordinary uncompleted derived tensor over the actual completed coefficient sheaf.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
abbrev wfOrdinaryDerivedTensor :
    PbcCompletedDerived X d × PbcCompletedDerived X d ⥤ PbcCompletedDerived X d :=
  SheafOfModules.wfSiteDerivedTensor (ProEt.topology X) (pbcAdicCompletion X d)

set_option backward.isDefEq.respectTransparency false in
/-- The localization model's natural comparison on flat-term K-flat representatives.
Source: Stacks 06YT; blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: take the natural representative comparison from site-derived-tensor descent.
The homotopy quotient comparison identifies its source with total tensor of complexes.
Flatness means exactness of sheaf tensor, so the two flat-term subcategories coincide.
Their localization comparisons give the displayed natural isomorphism. Restriction
of transformations to the resolving subcategory is bijective by descent, so the
compatible comparison with any other model exists uniquely. Thus the chosen model
is determined up to its unique compatible natural isomorphism. -/
theorem wfTensorRepresentative_exists :
    ∃ i :
      (((proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι.prod
          (proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι) ⋙
        Functor.uncurry.obj
          ((proEtaleOrdinaryTensor X (pbcAdicCompletion X d)).map₂HomologicalComplex
           (.up ℤ) (.up ℤ) (.up ℤ)) ⋙ DerivedCategory.Q) ≅
      ((((proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι ⋙ DerivedCategory.Q).prod
        ((proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι ⋙ DerivedCategory.Q)) ⋙
          wfOrdinaryDerivedTensor X d),
      ∀ b : ProEtaleTensorModel X (pbcAdicCompletion X d),
        ∃! e : wfOrdinaryDerivedTensor X d ≅ b.tensor,
          i.hom ≫ Functor.whiskerLeft
            ((((proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι ⋙
                DerivedCategory.Q).prod
              ((proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).ι ⋙
                DerivedCategory.Q))) e.hom = b.representative.hom := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  let R : Sheaf (ProEt.topology X) CommRingCat.{u + 1} := pbcAdicCompletion X d
  let h := SheafOfModules.wf_site_derived_tensor_descent.{u + 1, u, u + 2, 0, 0}
    (ProEt.topology X) R
  let S := h.choose
  have hS := h.choose_spec.1
  let c := h.choose_spec.2.2.1.choose_spec.1.some
  let t := h.choose_spec.2.2.1.choose_spec.2.choose_spec.some
  let P := proEtaleFlatRepresentatives X R
  let J : P.FullSubcategory ⥤ S.FullSubcategory :=
    ObjectProperty.lift S (P.ι ⋙ HomotopyCategory.quotient _ _) (by
      intro K
      apply (hS _).2
      refine ⟨K.property.1, ?_⟩
      intro n
      exact (exactFunctor (proEtaleRingModules X R) (proEtaleRingModules X R)).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso
          (C := X.ProEt) (J := ProEt.topology X) R (K.obj.X n))
        (K.property.2 n))
  let L := HomotopyCategory.quotient (proEtaleRingModules X R) (.up ℤ)
  let B := h.choose_spec.2.2.1.choose
  let T := h.choose_spec.2.2.1.choose_spec.2.choose
  let tc := Functor.uncurry.obj
    ((proEtaleOrdinaryTensor X R).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))
  have hc : (L.prod L) ⋙ B ≅ tc ⋙ L := c
  have ht : (S.ι.prod S.ι) ⋙ B ⋙ DerivedCategory.Qh ≅
      ((S.ι ⋙ DerivedCategory.Qh).prod (S.ι ⋙ DerivedCategory.Qh)) ⋙ T := t
  have hj : (P.ι.prod P.ι) ⋙ (L.prod L) = (J.prod J) ⋙ (S.ι.prod S.ι) := rfl
  let i0 := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (P.ι.prod P.ι) hc.symm) DerivedCategory.Qh
  let middle := Functor.isoWhiskerRight (eqToIso hj) (B ⋙ DerivedCategory.Qh)
  let i1 := i0 ≪≫ middle ≪≫ Functor.isoWhiskerLeft (J.prod J) ht
  have hjQ : (J.prod J) ⋙
      ((S.ι ⋙ DerivedCategory.Qh).prod (S.ι ⋙ DerivedCategory.Qh)) =
      ((P.ι ⋙ L ⋙ DerivedCategory.Qh).prod (P.ι ⋙ L ⋙ DerivedCategory.Qh)) := rfl
  let q := Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso _)
  let i2 := i1 ≪≫ Functor.isoWhiskerRight (eqToIso hjQ) T
  let i3 := i2 ≪≫ Functor.isoWhiskerRight (NatIso.prod q q) T
  let i := Functor.isoWhiskerLeft ((P.ι.prod P.ι) ⋙ tc)
    (DerivedCategory.quotientCompQhIso _).symm ≪≫ i3
  have hT : T = wfOrdinaryDerivedTensor X d := by
    unfold T wfOrdinaryDerivedTensor SheafOfModules.wfSiteDerivedTensor
    rfl
  rw [hT] at i
  refine ⟨i, ?_⟩
  intro b
  let H : ObjectProperty (HomotopyCategory (pbcModules X (pbcAdicCompletion X d)) (.up ℤ)) :=
    fun K ↦ P K.as
  have hres : ∀ K : HomotopyCategory (pbcModules X (pbcAdicCompletion X d)) (.up ℤ),
      ∃ (L : H.FullSubcategory) (f : L.obj ⟶ K),
        HomotopyCategory.quasiIso _ (.up ℤ) f := by
    intro K
    obtain ⟨L, f, hk, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (C := X.ProEt) (J := ProEt.topology X) (R := R) K.as
    refine ⟨⟨(HomotopyCategory.quotient _ (.up ℤ)).obj L, hk, ?_⟩,
      (HomotopyCategory.quotient _ (.up ℤ)).map f, ?_⟩
    · intro n
      exact (exactFunctor (proEtaleRingModules X R) (proEtaleRingModules X R)).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso
          (C := X.ProEt) (J := ProEt.topology X) R (L.X n)).symm (hf n)
    · exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq
  set_option backward.isDefEq.respectTransparency true in
    have hff := CategoryTheory.resolvingRepresentativesFullyFaithfulWhiskering
      (K := CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
      (H := HomotopyCategory (pbcModules X (pbcAdicCompletion X d)) (.up ℤ))
      (D := PbcCompletedDerived X d) (PbcCompletedDerived X d)
      (HomotopyCategory.quotient _ (.up ℤ)) HomotopyCategory.quotient_obj_surjective
      (HomotopyCategory.quasiIso _ (.up ℤ)) DerivedCategory.Qh P H
      (fun _ ↦ Iff.rfl) hres
  obtain ⟨ff⟩ := hff
  let ff' := ff.ofIso ((Functor.whiskeringLeft _ _ (PbcCompletedDerived X d)).mapIso
    (NatIso.prod (Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso _))
      (Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso _))))
  have hmap : Functor.whiskerLeft
      ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q))
      (ff'.preimageIso (i.symm ≪≫ b.representative)).hom =
        (i.symm ≪≫ b.representative).hom :=
    ff'.map_preimage (i.symm ≪≫ b.representative).hom
  refine ⟨ff'.preimageIso (i.symm ≪≫ b.representative), ?_, ?_⟩
  · change i.hom ≫ Functor.whiskerLeft
        ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q)) _ = _
    rw [hmap]
    exact i.hom_inv_id_assoc _
  · intro e he
    apply Iso.ext
    apply ff'.map_injective
    change Functor.whiskerLeft
        ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q)) e.hom =
      Functor.whiskerLeft ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q))
        (ff'.preimageIso (i.symm ≪≫ b.representative)).hom
    apply (cancel_epi i.hom).1
    rw [he, hmap]
    exact (i.hom_inv_id_assoc _).symm

/-- The existing pullback-comparison interface with this very localized tensor.
Source: Stacks 06YT; blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfTensorModel : ProEtaleTensorModel X (pbcAdicCompletion X d) where
  tensor := wfOrdinaryDerivedTensor X d
  representative := (wfTensorRepresentative_exists X d).choose

/-- Integral completed tensor is ordinary derived tensor followed by the Koszul reflector.
Source: blueprint order 2107; Bhatt--Scholze Definition 3.4.10
(blueprint: def-wf-tensor-product). -/
def wfIntegralTensor : WfCompleteCategory X d r a ha × WfCompleteCategory X d r a ha ⥤
    WfCompleteCategory X d r a ha :=
  ((ObjectProperty.ι (WfIsComplete X d r a ha)).prod
    (ObjectProperty.ι (WfIsComplete X d r a ha))) ⋙
      wfOrdinaryDerivedTensor X d ⋙ wfCompletion X d r a ha

/-- The ambient rational category keeps all integral complete objects, without boundedness.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
abbrev WfAmbientRationalCategory (p : A) :=
  ScalarLocalization A (WfCompleteCategory X d r a ha) p

/-- The underlying object of rational tensor, before specifying its localized Hom action.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfRationalTensorObj (p : A)
    (M N : WfAmbientRationalCategory X d r a ha p) :
    WfAmbientRationalCategory X d r a ha p :=
  ⟨(wfIntegralTensor X d r a ha).obj (M.obj, N.obj)⟩

/-- Bilinear scalar extension is uniquely determined on pure tensors, including denominators.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: sheaf tensor is linear in each variable. Its K-flat localization is linear by
extension of transformations from K-flat representatives; the reflector is linear by its
unit and the Hom bijection. Extend this bilinear map along A→A[1/p] in both variables.
The tensor-product universal property gives the displayed pure-tensor formula and uniqueness.
Writing coefficients as inverse powers gives precisely denominator p^(r+s). -/
theorem wfRationalTensorHom_exists (p : A)
    (M M' N N' : WfAmbientRationalCategory X d r a ha p) :
    ∃! b : (M ⟶ M') →ₗ[Localization.Away p] (N ⟶ N') →ₗ[Localization.Away p]
        (wfRationalTensorObj X d r a ha p M N ⟶ wfRationalTensorObj X d r a ha p M' N'),
      ∀ (f : M.obj ⟶ M'.obj) (g : N.obj ⟶ N'.obj) (s t : Localization.Away p),
        b (s ⊗ₜ[A] f) (t ⊗ₜ[A] g) =
          (s * t) ⊗ₜ[A] (wfIntegralTensor X d r a ha).map (Prod.mkHom f g) := by
  sorry

/-- The unique localized bilinear map; its values are prescribed on every numerator.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfRationalTensorHom (p : A)
    (M M' N N' : WfAmbientRationalCategory X d r a ha p) :=
  (wfRationalTensorHom_exists X d r a ha p M M' N N').exists.choose

private theorem wfRationalTensorHom_tmul (p : A)
    (M M' N N' : WfAmbientRationalCategory X d r a ha p)
    (f : M.obj ⟶ M'.obj) (g : N.obj ⟶ N'.obj) (s t : Localization.Away p) :
    wfRationalTensorHom X d r a ha p M M' N N' (s ⊗ₜ[A] f) (t ⊗ₜ[A] g) =
      (s * t) ⊗ₜ[A] (wfIntegralTensor X d r a ha).map (Prod.mkHom f g) :=
  (wfRationalTensorHom_exists X d r a ha p M M' N N').exists.choose_spec f g s t

attribute [local irreducible] wfRationalTensorHom

/-- The extended tensor maps satisfy the bifunctor laws.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: on pure tensors the identity law follows from integral tensor's identity law and
1*1=1. Composition follows from integral functoriality and commutative multiplication of
localized scalars. Bilinearity extends these equations to all localized morphisms. -/
theorem wfRationalTensor_laws (p : A) :
    (∀ M N : WfAmbientRationalCategory X d r a ha p,
      wfRationalTensorHom X d r a ha p M M N N (𝟙 M) (𝟙 N) = 𝟙 _) ∧
    ∀ (M M' M'' N N' N'' : WfAmbientRationalCategory X d r a ha p)
      (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N''),
      wfRationalTensorHom X d r a ha p M M'' N N'' (f ≫ f') (g ≫ g') =
        wfRationalTensorHom X d r a ha p M M' N N' f g ≫
          wfRationalTensorHom X d r a ha p M' M'' N' N'' f' g' := by
  constructor
  · intro M N
    change wfRationalTensorHom X d r a ha p M M N N
      ((1 : Localization.Away p) ⊗ₜ[A] 𝟙 M.obj)
      ((1 : Localization.Away p) ⊗ₜ[A] 𝟙 N.obj) =
        (1 : Localization.Away p) ⊗ₜ[A] 𝟙 _
    rw [wfRationalTensorHom_tmul, one_mul]
    congr 1
    exact (wfIntegralTensor X d r a ha).map_id (M.obj, N.obj)
  · intro M M' M'' N N' N'' f f' g g'
    change wfRationalTensorHom X d r a ha p M M'' N N''
      (ScalarLocalization.composition A (WfCompleteCategory X d r a ha) p _ _ _ f' f)
      (ScalarLocalization.composition A (WfCompleteCategory X d r a ha) p _ _ _ g' g) =
        ScalarLocalization.composition A (WfCompleteCategory X d r a ha) p _ _ _
          (wfRationalTensorHom X d r a ha p M' M'' N' N'' f' g')
          (wfRationalTensorHom X d r a ha p M M' N N' f g)
    induction f using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add f₁ f₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
    | tmul s f =>
      induction f' using TensorProduct.induction_on with
      | zero => simp only [map_zero, LinearMap.zero_apply]
      | add f₁ f₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
      | tmul t f' =>
        induction g using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | add g₁ g₂ h₁ h₂ => simp only [map_add, h₁, h₂]
        | tmul u g =>
          induction g' using TensorProduct.induction_on with
          | zero => simp only [map_zero, LinearMap.zero_apply]
          | add g₁ g₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
          | tmul v g' =>
            rw [ScalarLocalization.composition_tmul, ScalarLocalization.composition_tmul,
              wfRationalTensorHom_tmul, wfRationalTensorHom_tmul,
              wfRationalTensorHom_tmul, ScalarLocalization.composition_tmul]
            have ht := (wfIntegralTensor X d r a ha).map_comp
              (Prod.mkHom f g) (Prod.mkHom f' g')
            rw [← ht]
            congr 1
            ac_rfl

/-- Completed tensor rationalized with the stated product-of-denominators convention.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfRationalTensor (p : A) :
    WfAmbientRationalCategory X d r a ha p × WfAmbientRationalCategory X d r a ha p ⥤
      WfAmbientRationalCategory X d r a ha p where
  obj MN := wfRationalTensorObj X d r a ha p MN.1 MN.2
  map {MN PQ} f := wfRationalTensorHom X d r a ha p MN.1 PQ.1 MN.2 PQ.2 f.1 f.2
  map_id MN := (wfRationalTensor_laws X d r a ha p).1 MN.1 MN.2
  map_comp f g := (wfRationalTensor_laws X d r a ha p).2 _ _ _ _ _ _ f.1 g.1 f.2 g.2


variable (e : Aut X)

/-- The completion comparison is uniquely fixed by its unit square.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: on flat-term K-flat representatives use the degreewise balanced tensor comparison.
The coefficient limit identification fixes a_j, hence identifies Q_m and every transition.
On the product use the map whose components are the transported projections. The transition
identity makes this commute with 1-shift. On each fiber term B^i plus B^(i-1) use the
comparison on both summands; it commutes with (dx,(1-t)x-dy). This produces the displayed
isomorphism and its (u,0) unit equation. The reflector's Hom bijection shows uniqueness,
including when a representative is already flat K-flat and when the scheme is empty. -/
theorem wfPullbackCompletion_exists (M : PbcCompletedDerived X d) :
    ∃! c : (pbcIsoAmbientPullback e.hom d).obj (wfCompletionObj X d r a ha M) ≅
        wfCompletionObj X d r a ha ((pbcIsoAmbientPullback e.hom d).obj M),
      (pbcIsoAmbientPullback e.hom d).map (wfCompletionUnit X d r a ha M) ≫ c.hom =
        wfCompletionUnit X d r a ha ((pbcIsoAmbientPullback e.hom d).obj M) := by
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- Exact coefficient transport preserves intrinsic completeness for the actual scalar list.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: the finite coefficient comparisons preserve every constant section a_j, and commute
with quotient maps. Their limit fixes a_j on the completed ring. Apply the exact inverse
site equivalences to the strict Koszul tower. They preserve products and both finite
fiber summands; the projection comparison commutes with 1-shift and with the signed
fiber differential. It identifies the (u,0) units, hence preserves their invertibility. -/
theorem wfIsoPullback_complete (M : WfCompleteCategory X d r a ha) :
    WfIsComplete X d r a ha ((pbcIsoAmbientPullback e.hom d).obj M.obj) := by
  change IsIso (wfCompletionUnit X d r a ha
    ((pbcIsoAmbientPullback e.hom d).obj M.obj))
  obtain ⟨c, hc, _⟩ := wfPullbackCompletion_exists X d r a ha e M.obj
  have : IsIso (wfCompletionUnit X d r a ha M.obj) := M.property
  rw [← hc]
  infer_instance

/-- The same exact transport on all complete objects, before raw rationalization.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfCompletePullback : WfCompleteCategory X d r a ha ⥤ WfCompleteCategory X d r a ha :=
  ObjectProperty.lift (WfIsComplete X d r a ha)
    (ObjectProperty.ι (WfIsComplete X d r a ha) ⋙ pbcIsoAmbientPullback e.hom d)
    (wfIsoPullback_complete X d r a ha e)

/-- Constant sections are fixed by the completed coefficient identification.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: check the scalar action after every finite quotient projection. The constant
inverse-image comparison is adjoint to identity on constants, so fixes each residue.
The limit map therefore fixes every scalar. The sectionwise linear equation descends
through complexes and localization, and restricts to the complete full subcategory. -/
theorem wfCompletePullback_linear :
    (wfCompletePullback X d r a ha e).Additive ∧
      (wfCompletePullback X d r a ha e).Linear A := by
  sorry

/-- The additive part of the specified coefficient transport.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
instance wfCompletePullback_additive : (wfCompletePullback X d r a ha e).Additive :=
  (wfCompletePullback_linear X d r a ha e).1

/-- The A-linear part of the specified coefficient transport.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
instance wfCompletePullback_isLinear : (wfCompletePullback X d r a ha e).Linear A :=
  (wfCompletePullback_linear X d r a ha e).2

/-- Frobenius transport on the ambient raw rationalization, on every complete object.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
abbrev wfAmbientRationalPullback (p : A) :=
  ScalarLocalization.map A (WfCompleteCategory X d r a ha) p
    (wfCompletePullback X d r a ha e)

/-- The specified product/fiber comparison, determined equivalently by the unit square.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfPullbackCompletion (M : PbcCompletedDerived X d) :=
  (wfPullbackCompletion_exists X d r a ha e M).exists.choose

/-- The integral comparison is the completed canonical derived tensor comparison.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfIntegralTensorPullback (M N : WfCompleteCategory X d r a ha) :
    (wfCompletePullback X d r a ha e).obj ((wfIntegralTensor X d r a ha).obj (M, N)) ≅
      (wfIntegralTensor X d r a ha).obj
        ((wfCompletePullback X d r a ha e).obj M, (wfCompletePullback X d r a ha e).obj N) :=
  ObjectProperty.isoMk _
    (wfPullbackCompletion X d r a ha e ((wfOrdinaryDerivedTensor X d).obj (M.obj, N.obj)) ≪≫
      (ObjectProperty.ι (WfIsComplete X d r a ha)).mapIso
        ((wfCompletion X d r a ha).mapIso
          ((proEtaleCanonicalTensorComparison e.hom (pbcAdicCompletion X d)
            (pbcAdicCompletion X d) (asIso (completedCoefficientMap e.hom d))
            (wfTensorModel X d) (wfTensorModel X d)).app (M.obj, N.obj))))

private theorem wfCompletion_unit_map {M N : PbcCompletedDerived X d} (f : M ⟶ N) :
    wfCompletionUnit X d r a ha M ≫ ((wfCompletion X d r a ha).map f).hom =
      f ≫ wfCompletionUnit X d r a ha N := by
  exact (Equiv.ofBijective _
    ((wfCompletionReflector X d r a ha).2 M
      (wfCompletionObj X d r a ha N) ((wfCompletionReflector X d r a ha).1 N))).apply_symm_apply _

private theorem wfPullbackCompletion_naturality {M N : PbcCompletedDerived X d}
    (f : M ⟶ N) :
    (pbcIsoAmbientPullback e.hom d).map (((wfCompletion X d r a ha).map f).hom) ≫
        (wfPullbackCompletion X d r a ha e N).hom =
      (wfPullbackCompletion X d r a ha e M).hom ≫
        ((wfCompletion X d r a ha).map ((pbcIsoAmbientPullback e.hom d).map f)).hom := by
  let H := pbcIsoAmbientPullback e.hom d
  let cM := wfPullbackCompletion X d r a ha e M
  have hc (K : PbcCompletedDerived X d) :
      H.map (wfCompletionUnit X d r a ha K) ≫
          (wfPullbackCompletion X d r a ha e K).hom =
        wfCompletionUnit X d r a ha (H.obj K) :=
    (wfPullbackCompletion_exists X d r a ha e K).exists.choose_spec
  apply (cancel_epi cM.inv).1
  apply ((wfCompletionReflector X d r a ha).2 (H.obj M)
    (wfCompletionObj X d r a ha (H.obj N))
    ((wfCompletionReflector X d r a ha).1 (H.obj N))).1
  have hm : wfCompletionUnit X d r a ha (H.obj M) ≫ cM.inv =
      H.map (wfCompletionUnit X d r a ha M) := by
    rw [← hc M, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  dsimp only
  rw [← Category.assoc, hm, ← Category.assoc, ← H.map_comp,
    wfCompletion_unit_map, H.map_comp, Category.assoc, hc N]
  change H.map f ≫ wfCompletionUnit X d r a ha (H.obj N) =
    wfCompletionUnit X d r a ha (H.obj M) ≫ cM.inv ≫ cM.hom ≫
      ((wfCompletion X d r a ha).map (H.map f)).hom
  rw [Iso.inv_hom_id_assoc, wfCompletion_unit_map]

set_option backward.isDefEq.respectTransparency false in
private theorem wfIntegralTensorPullback_naturality
    {M M' N N' : WfCompleteCategory X d r a ha} (f : M ⟶ M') (g : N ⟶ N') :
    (wfCompletePullback X d r a ha e).map
        ((wfIntegralTensor X d r a ha).map (Prod.mkHom f g)) ≫
          (wfIntegralTensorPullback X d r a ha e M' N').hom =
      (wfIntegralTensorPullback X d r a ha e M N).hom ≫
        (wfIntegralTensor X d r a ha).map (Prod.mkHom
          ((wfCompletePullback X d r a ha e).map f)
          ((wfCompletePullback X d r a ha e).map g)) := by
  apply ObjectProperty.hom_ext
  let T := wfOrdinaryDerivedTensor X d
  let H := pbcIsoAmbientPullback e.hom d
  let L := wfCompletion X d r a ha
  let alpha := proEtaleCanonicalTensorComparison e.hom (pbcAdicCompletion X d)
    (pbcAdicCompletion X d) (asIso (completedCoefficientMap e.hom d))
    (wfTensorModel X d) (wfTensorModel X d)
  change H.map ((L.map (T.map (Prod.mkHom f.hom g.hom))).hom) ≫
      (wfPullbackCompletion X d r a ha e (T.obj (M'.obj, N'.obj))).hom ≫
        (L.map (alpha.hom.app (M'.obj, N'.obj))).hom =
    ((wfPullbackCompletion X d r a ha e (T.obj (M.obj, N.obj))).hom ≫
      (L.map (alpha.hom.app (M.obj, N.obj))).hom) ≫
        (L.map (T.map (Prod.mkHom (H.map f.hom) (H.map g.hom)))).hom
  rw [← Category.assoc, wfPullbackCompletion_naturality, Category.assoc]
  rw [Category.assoc]
  congr 1
  have hn := congrArg (fun k ↦ (L.map k).hom)
    (alpha.hom.naturality (Prod.mkHom f.hom g.hom))
  simpa only [T, H, wfTensorModel, Functor.comp_map, Functor.prod_map, Functor.map_comp,
    ObjectProperty.FullSubcategory.comp_hom] using hn

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Rationalizing the constructed integral comparison fixes every component uniquely.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: tensor with one the integral comparison and its inverse on Hom modules. The
integral comparison is natural by naturality of the canonical tensor comparison and
of the product/fiber comparison. Its naturality extends to all fractions by A-linearity
and inversion of p. Every object is an original integral object, so the component
formula gives uniqueness. The two displayed directions are thus fixed, not chosen. -/
theorem wfRationalTensorPullback_exists (p : A) :
    ∃! mu : wfRationalTensor X d r a ha p ⋙ wfAmbientRationalPullback X d r a ha e p ≅
        ((wfAmbientRationalPullback X d r a ha e p).prod
          (wfAmbientRationalPullback X d r a ha e p)) ⋙ wfRationalTensor X d r a ha p,
      ∀ M N : WfCompleteCategory X d r a ha,
        mu.hom.app (⟨M⟩, ⟨N⟩) =
          (ScalarLocalization.localization A (WfCompleteCategory X d r a ha) p).map
            (wfIntegralTensorPullback X d r a ha e M N).hom  := by
  let Q := ScalarLocalization.localization A (WfCompleteCategory X d r a ha) p
  let mu : wfRationalTensor X d r a ha p ⋙ wfAmbientRationalPullback X d r a ha e p ≅
      ((wfAmbientRationalPullback X d r a ha e p).prod
        (wfAmbientRationalPullback X d r a ha e p)) ⋙ wfRationalTensor X d r a ha p :=
    NatIso.ofComponents
    (fun MN ↦ Q.mapIso
      (wfIntegralTensorPullback X d r a ha e MN.1.obj MN.2.obj)) (by
        intro MN PQ v
        rcases MN with ⟨M, N⟩
        rcases PQ with ⟨M', N'⟩
        rcases v with ⟨f, g⟩
        change ScalarLocalization.composition A (WfCompleteCategory X d r a ha) p _ _ _
            (1 ⊗ₜ[A] (wfIntegralTensorPullback X d r a ha e M'.obj N'.obj).hom)
            (ScalarLocalization.mapHom A (WfCompleteCategory X d r a ha) p
              (wfCompletePullback X d r a ha e) _ _
              (wfRationalTensorHom X d r a ha p M M' N N' f g)) =
          ScalarLocalization.composition A (WfCompleteCategory X d r a ha) p _ _ _
            (wfRationalTensorHom X d r a ha p _ _ _ _
              (ScalarLocalization.mapHom A (WfCompleteCategory X d r a ha) p
                (wfCompletePullback X d r a ha e) _ _ f)
              (ScalarLocalization.mapHom A (WfCompleteCategory X d r a ha) p
                (wfCompletePullback X d r a ha e) _ _ g))
            (1 ⊗ₜ[A] (wfIntegralTensorPullback X d r a ha e M.obj N.obj).hom)
        exact scalarLocalization_bilinear_naturality p
          (wfCompletePullback X d r a ha e)
          (wfRationalTensorHom X d r a ha p M M' N N')
          (wfRationalTensorHom X d r a ha p _ _ _ _)
          (fun f g ↦ (wfIntegralTensor X d r a ha).map (Prod.mkHom f g))
          (fun f g ↦ (wfIntegralTensor X d r a ha).map (Prod.mkHom f g))
          (wfRationalTensorHom_tmul X d r a ha p M M' N N')
          (wfRationalTensorHom_tmul X d r a ha p _ _ _ _)
          (wfIntegralTensorPullback X d r a ha e M.obj N.obj).hom
          (wfIntegralTensorPullback X d r a ha e M'.obj N'.obj).hom
          (wfIntegralTensorPullback_naturality X d r a ha e) f g)
  refine ⟨mu, (fun M N ↦ rfl), ?_⟩
  intro nu hnu
  apply Iso.ext
  apply NatTrans.ext
  funext MN
  exact hnu MN.1.obj MN.2.obj

/-- The typed pullback/tensor comparison in the displayed direction of the source.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfRationalTensorPullback (p : A) :=
  (wfRationalTensorPullback_exists X d r a ha e p).exists.choose

/-- The exact PBC integral subcategory lies in this same intrinsically complete category.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: its first defining condition supplies an intrinsic-completion witness after the
canonical completed-ring presentation comparison. The mutually inverse exact coefficient
restrictions preserve the strict Koszul tower and unit. The Koszul reflector shows
independence of the generating tuple and representative. Therefore the canonical
representative and the given generating tuple have invertible intrinsic unit. -/
theorem wfConstructible_complete (M : PbcBoundedConstructibleComplete X d) :
    WfIsComplete X d r a ha M.obj := by
  sorry

/-- Inclusion of the specified constructible objects, retaining all their derived arrows.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfIntegralConstructibleInclusion :
    PbcBoundedConstructibleComplete X d ⥤ WfCompleteCategory X d r a ha :=
  ObjectProperty.lift (WfIsComplete X d r a ha)
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X d))
    (wfConstructible_complete X d r a ha)

/-- The inclusion on rational coefficients is uniquely determined by integral localization.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: the inclusion is A-linear since its underlying maps are unchanged. Extend its
Hom maps by tensor with the identity of A[1/p]. This respects the given composition
and identity formulas. Every localized morphism is a fraction of an integral morphism,
and the objects are unchanged, so the equality determines the functor uniquely. -/
theorem wfConstructibleInclusion_exists (p : A) :
    ∃! F : PbcRationalCategory X d p ⥤ WfAmbientRationalCategory X d r a ha p,
      pbcRationalization X d p ⋙ F =
        wfIntegralConstructibleInclusion X d r a ha ⋙
          ScalarLocalization.localization A (WfCompleteCategory X d r a ha) p := by
  let I := wfIntegralConstructibleInclusion X d r a ha
  let : I.Additive := ⟨fun {_ _ _ _} ↦ rfl⟩
  let : I.Linear A := ⟨fun {_ _} _ _ ↦ rfl⟩
  let F : PbcRationalCategory X d p ⥤ WfAmbientRationalCategory X d r a ha p :=
    { obj := fun M ↦ ⟨I.obj M.obj⟩
      map := fun f ↦ (I.mapLinearMap A).baseChange (Localization.Away p) f
      map_id := fun M ↦ by
        change (I.mapLinearMap A).baseChange (Localization.Away p)
          (1 ⊗ₜ[A] 𝟙 M.obj) = (1 : Localization.Away p) ⊗ₜ[A] 𝟙 (I.obj M.obj)
        rw [LinearMap.baseChange_tmul]
        rfl
      map_comp := fun {M N P} f g ↦ by
        change (I.mapLinearMap A).baseChange (Localization.Away p)
            (ScalarLocalization.composition A _ p _ _ _ g f) =
          ScalarLocalization.composition A _ p _ _ _
            ((I.mapLinearMap A).baseChange (Localization.Away p) g)
            ((I.mapLinearMap A).baseChange (Localization.Away p) f)
        induction f using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | add f f' hf hf' => simp only [map_add, hf, hf']
        | tmul s f =>
          induction g using TensorProduct.induction_on with
          | zero => simp only [map_zero, LinearMap.zero_apply]
          | add g g' hg hg' => simp only [map_add, LinearMap.add_apply, hg, hg']
          | tmul t g => simp only [ScalarLocalization.composition_tmul, LinearMap.baseChange_tmul,
              Functor.coe_mapLinearMap, Functor.map_comp] }
  have hF : pbcRationalization X d p ⋙ F = I ⋙
      ScalarLocalization.localization A (WfCompleteCategory X d r a ha) p := by
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro M N f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact LinearMap.baseChange_tmul (I.mapLinearMap A) 1 f
  refine ⟨F, hF, ?_⟩
  intro G hG
  exact scalarLocalization_precomp_injective p G F (hG.trans hF.symm)

/-- The raw rational inclusion with its actual unchanged integral object function.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfConstructibleInclusion (p : A) :=
  (wfConstructibleInclusion_exists X d r a ha p).exists.choose

/-- Inclusion commutes with the same coefficient transport, normalized by identity on objects.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: both inclusions and both pullbacks act on the same ambient derived objects and
maps. Their integral composites agree after the faithful ambient inclusion. The unique
rational extension retains these object identities and sends every integral arrow to
itself tensored with one. Thus the displayed object equality is literal. -/
theorem wfConstructiblePullback_obj (p : A) (M : PbcRationalCategory X d p) :
    (wfAmbientRationalPullback X d r a ha e p).obj
        ((wfConstructibleInclusion X d r a ha p).obj M) =
      (wfConstructibleInclusion X d r a ha p).obj
        ((pbcRationalIsoPullback e d p).obj M) := by
  have hobj (K : PbcBoundedConstructibleComplete X d) :
      (wfConstructibleInclusion X d r a ha p).obj ⟨K⟩ =
        (ScalarLocalization.localization A (WfCompleteCategory X d r a ha) p).obj
          ((wfIntegralConstructibleInclusion X d r a ha).obj K) :=
    Functor.congr_obj (wfConstructibleInclusion_exists X d r a ha p).exists.choose_spec K
  rcases M with ⟨M⟩
  change (wfAmbientRationalPullback X d r a ha e p).obj
      ((wfConstructibleInclusion X d r a ha p).obj ⟨M⟩) =
    (wfConstructibleInclusion X d r a ha p).obj ⟨(pbcIsoIntegralPullback e.hom d).obj M⟩
  rw [hobj, hobj]
  apply congrArg (ScalarLocalization.mk (R := A) (p := p))
  apply ObjectProperty.FullSubcategory.ext
  rfl

end AlgebraicGeometry.Scheme

namespace WeilConjectures
open AlgebraicGeometry AlgebraicGeometry.Scheme
variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (X₀ : Over (Spec (CommRingCat.of D.k₀)))
  [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  (E : Padic.FiniteCoefficientFields c.l c.Qbar)

/-- The singleton generator is exactly the stipulated uniformizer ideal.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product).
Proof: the range of the constant function on Fin 1 is the singleton uniformizer, and
pbcIntegralDatum defines its ideal as the span of that singleton. -/
theorem wfUniformizer_generates :
    Ideal.span (Set.range (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)) =
      (pbcStageDatum.{u} c.l c.Qbar E).ideal := by
  rw [Set.range_const]
  change Ideal.span {pbcUniformizer c.l (pbcFiniteField c.l c.Qbar E)} = _
  rfl

/-- The actual ambient rational category at the finite coefficient field E.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
abbrev WfAmbient := WfAmbientRationalCategory (D.geometricFiber X₀).left
  (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
  (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- Completed tensor at E on arbitrary ambient objects, with the specified scalar ring.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
abbrev wfTensor := wfRationalTensor (D.geometricFiber X₀).left
  (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
  (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- Geometric Frobenius on this ambient category, using the coefficient-limit identification.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
abbrev wfAmbientFrobenius := wfAmbientRationalPullback (D.geometricFiber X₀).left
  (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
  (wfUniformizer_generates D c E) (D.geometricFrobenius X₀) (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- Inclusion of the node's Weil-complex carriers into the stipulated ambient category.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
abbrev wfWeilCarrier (K : WeilD D c X₀ E) : WfAmbient D c X₀ E :=
  (wfConstructibleInclusion (D.geometricFiber X₀).left
    (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
    (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)).obj K.carrier

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The given Weil isomorphism, transported by the faithful ambient coefficient inclusion.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfWeilStructure (K : WeilD D c X₀ E) :
    (wfAmbientFrobenius D c X₀ E).obj (wfWeilCarrier D c X₀ E K) ≅
      wfWeilCarrier D c X₀ E K :=
  eqToIso (wfConstructiblePullback_obj (D.geometricFiber X₀).left
    (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
    (wfUniformizer_generates D c E) (D.geometricFrobenius X₀)
    (pbcStageUniformizer.{u} c.l c.Qbar E) K.carrier) ≪≫
      (wfConstructibleInclusion (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) 1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
        (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)).mapIso K.str

attribute [local irreducible] wfWeilStructure

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Tensor Frobenius is mu followed by tensor of the two given Weil isomorphisms.
The output is ambient; restriction to an exact bifunctor of Weil complexes is separate.
Source: blueprint order 2107 (blueprint: def-wf-tensor-product). -/
def wfTensorFrobenius (K L : WeilD D c X₀ E) :
    (wfAmbientFrobenius D c X₀ E).obj
        ((wfTensor D c X₀ E).obj (wfWeilCarrier D c X₀ E K, wfWeilCarrier D c X₀ E L)) ≅
      (wfTensor D c X₀ E).obj (wfWeilCarrier D c X₀ E K, wfWeilCarrier D c X₀ E L) :=
  (wfRationalTensorPullback (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E)
    1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E) (wfUniformizer_generates D c E)
    (D.geometricFrobenius X₀) (pbcStageUniformizer.{u} c.l c.Qbar E)).app
      (wfWeilCarrier D c X₀ E K, wfWeilCarrier D c X₀ E L) ≪≫
    (wfTensor D c X₀ E).mapIso
      { hom := Prod.mkHom (wfWeilStructure D c X₀ E K).hom (wfWeilStructure D c X₀ E L).hom
        inv := Prod.mkHom (wfWeilStructure D c X₀ E K).inv (wfWeilStructure D c X₀ E L).inv
        hom_inv_id := by ext <;> exact Iso.hom_inv_id _
        inv_hom_id := by ext <;> exact Iso.inv_hom_id _ }

end WeilConjectures
