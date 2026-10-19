/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleDirectImageFiniteness
import Sheaf.AlgebraicGeometry.PullbackBoundedConstructible
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # Restriction of derived direct image to bounded constructibles

Source: Weil conjectures blueprint, sec-proper-base-change/sk-thm-properbasechange,
order 1302; Stacks Project, Tags 05TC, 08J5, 09AK and 09AL
(blueprint: prop-weil-pbc-restriction-direct-image).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The restriction uses the canonical shift comparison of ordinary K-injective direct
image. Source: Stacks Project, Section 07A5
(blueprint: prop-weil-pbc-restriction-direct-image). -/
noncomputable instance finiteCoefficientDerivedDirectImage_commShift
    {S T : Scheme.{u}} (f : S ⟶ T) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] :
    (finiteCoefficientDerivedDirectImage f Λ).CommShift ℤ :=
  inferInstanceAs ((finiteCoefficientModuleDirectImage f Λ).rightDerivedFunctor.CommShift ℤ)

/-- The ambient ordinary derived functor preserves distinguished triangles, with its
canonical shift comparison. Source: Stacks Project, Section 07A5
(blueprint: prop-weil-pbc-restriction-direct-image). -/
instance finiteCoefficientDerivedDirectImage_isTriangulated
    {S T : Scheme.{u}} (f : S ⟶ T) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] :
    (finiteCoefficientDerivedDirectImage f Λ).IsTriangulated :=
  inferInstanceAs ((finiteCoefficientModuleDirectImage f Λ).rightDerivedFunctor.IsTriangulated)

/-- The etale-origin bounded constructible property is triangulated in the actual finite
coefficient module category. Source: Stacks Project, Tags 09AL and 06UQ
(blueprint: prop-weil-pbc-restriction-direct-image).

Proof: finite coefficient rings are Noetherian. Constructible etale module sheaves
form a weak Serre class: refine the finitely many stratifications in a short exact
sequence, then trivialize the finite locally constant terms on etale covers, where
kernels, cokernels and extensions again have finite module values. The exact
comparison identifies bounded etale-origin complexes with bounded complexes having
constructible pro-etale cohomology (Tag 09AL). Shifts preserve this property, and the
long exact cohomology sequence shows it is closed under distinguished triangles.
The zero complex belongs to the property, so it is a triangulated object property. -/
theorem finiteCoefficientBoundedConstructible_isTriangulated
    (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    : letI : TopologicalSpace Λ := ⊥
      letI : DiscreteTopology Λ := ⟨rfl⟩
      (isBoundedConstructibleFiniteCoefficient T Λ).IsTriangulated := by
  let : TopologicalSpace Λ := ⊥
  let : DiscreteTopology Λ := ⟨rfl⟩
  exact isBoundedConstructibleFiniteCoefficient_isTriangulated T Λ

attribute [instance] finiteCoefficientBoundedConstructible_isTriangulated

private theorem etaleConstructible_iso
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    {E E' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (e : E ≅ E') (h : Scheme.IsConstructibleEtaleModuleSheaf E) :
    Scheme.IsConstructibleEtaleModuleSheaf E' := by
  have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf E).mp h
  exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf E').mpr
    (Scheme.IsConstructibleSheaf.of_iso e)

private theorem etaleConstructible_zero
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (h : IsZero E) :
    Scheme.IsConstructibleEtaleModuleSheaf E := by
  exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf E).mpr
    (Scheme.IsConstructibleSheaf.of_isZero h)

private theorem coefficientConstructible_iso
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    {F G : FiniteCoefficientModules X Λ} (e : F ≅ G)
    (h : IsConstructibleFiniteCoefficientSheaf X Λ F) :
    IsConstructibleFiniteCoefficientSheaf X Λ G := by
  obtain ⟨E, hE, ⟨i⟩⟩ := h
  exact ⟨E, hE, ⟨e.symm ≪≫ i⟩⟩

private theorem coefficientConstructible_zero
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    (F : FiniteCoefficientModules X Λ) (h : IsZero F) :
    IsConstructibleFiniteCoefficientSheaf X Λ F := by
  let : Zero (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := HasZeroObject.zero' _
  refine ⟨0, etaleConstructible_zero _ (isZero_zero _), ⟨?_⟩⟩
  exact h.iso ((finiteCoefficientComparison X Λ).map_isZero (isZero_zero _))

private theorem coefficientConstructible_single
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    (F : FiniteCoefficientModules X Λ)
    (h : IsConstructibleFiniteCoefficientSheaf X Λ F) :
    isBoundedConstructibleFiniteCoefficient X Λ
      ((DerivedCategory.singleFunctor (FiniteCoefficientModules X Λ) 0).obj F) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := h
  let L := (DerivedCategory.singleFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj E
  refine ⟨L, ⟨?_, 0, 0, le_rfl, ?_⟩, ⟨?_⟩⟩
  · intro j
    have h : Scheme.IsConstructibleEtaleModuleSheaf
        ((DerivedCategory.homologyFunctor _ j).obj L) := by
      by_cases hj : j = 0
      · subst j
        exact etaleConstructible_iso
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app E).symm hE
      · apply etaleConstructible_zero
        rcases lt_or_gt_of_ne hj with hj | hj
        · exact DerivedCategory.isZero_of_isGE L 0 j hj
        · exact DerivedCategory.isZero_of_isLE L 0 j hj
    obtain ⟨S, hS⟩ := h
    exact ⟨S, S.isConstructible_stratum, hS⟩
  · intro i hi
    rcases hi with hi | hi
    · exact DerivedCategory.isZero_of_isGE L 0 i hi
    · exact DerivedCategory.isZero_of_isLE L 0 i hi
  · exact ((finiteCoefficientComparison X Λ).mapDerivedCategorySingleFunctor 0).app E ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso e.symm

private theorem coefficientConstructible_cohomology
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    (K : FiniteCoefficientDerivedCategory X Λ)
    (h : isBoundedConstructibleFiniteCoefficient X Λ K) :
    DerivedCategory.TStructure.t.bounded K ∧
      ∀ j, IsConstructibleFiniteCoefficientSheaf X Λ
        ((DerivedCategory.homologyFunctor _ j).obj K) := by
  obtain ⟨L, ⟨hL, a, b, hab, hvan⟩, ⟨e⟩⟩ := h
  have hLb : DerivedCategory.TStructure.t.bounded L :=
    ⟨⟨a, (DerivedCategory.isGE_iff L a).mpr (fun i hi ↦ hvan i (Or.inl hi))⟩,
      ⟨b, (DerivedCategory.isLE_iff L b).mpr (fun i hi ↦ hvan i (Or.inr hi))⟩⟩
  constructor
  · exact DerivedCategory.TStructure.t.bounded.prop_of_iso e
      ((finiteCoefficientComparison X Λ).bounded_mapDerivedCategory_obj hLb)
  · intro j
    obtain ⟨S, _, hS⟩ := hL j
    refine ⟨(DerivedCategory.homologyFunctor _ j).obj L, ⟨S, hS⟩, ⟨?_⟩⟩
    exact (DerivedCategory.homologyFunctor _ j).mapIso e.symm ≪≫
      ((finiteCoefficientComparison X Λ).mapDerivedCategoryHomologyFunctorIso j).symm.app L

private theorem coefficientConstructible_of_cohomology
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    (K : FiniteCoefficientDerivedCategory X Λ)
    (hb : DerivedCategory.TStructure.t.bounded K)
    (h : ∀ j, IsConstructibleFiniteCoefficientSheaf X Λ
      ((DerivedCategory.homologyFunctor _ j).obj K)) :
    isBoundedConstructibleFiniteCoefficient X Λ K := by
  let P : ObjectProperty (FiniteCoefficientModules X Λ) :=
    IsConstructibleFiniteCoefficientSheaf X Λ
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ coefficientConstructible_iso e h⟩
  have : (isBoundedConstructibleFiniteCoefficient X Λ).IsClosedUnderIsomorphisms := by
    dsimp only [isBoundedConstructibleFiniteCoefficient]
    infer_instance
  exact DerivedCategory.prop_of_bounded _ P coefficientConstructible_single K hb h

private theorem coefficientImage_single_nonnegative
    {S T : Scheme.{u}} (f : S ⟶ T) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ]
    (F : FiniteCoefficientModules S Λ) :
    ((finiteCoefficientDerivedDirectImage f Λ).obj
      ((DerivedCategory.singleFunctor (FiniteCoefficientModules S Λ) 0).obj F)).IsGE 0 := by
  let : EnoughInjectives (FiniteCoefficientModules S Λ) :=
    EnoughInjectives.of_equivalence (finiteCoefficientRealization S Λ).asEquivalence.inverse
  exact (finiteCoefficientModuleDirectImage f Λ).isGE_rightDerivedFunctor_obj_singleFunctor F

private theorem constructibleAmplitude
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (Φ : DerivedCategory C ⥤ DerivedCategory D) [Φ.CommShift ℤ] [Φ.IsTriangulated]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] (c : ℤ)
    (hsingle : ∀ F, P F → DerivedCategory.homologyConcentratedIn 0 c
      (Φ.obj ((DerivedCategory.singleFunctor C 0).obj F))) (n : ℕ) :
    ∀ (a : ℤ) (K : DerivedCategory C), K.IsGE a → K.IsLE (a + n - 1) →
      (∀ q, a ≤ q → q < a + n → P ((DerivedCategory.homologyFunctor C q).obj K)) →
      DerivedCategory.homologyConcentratedIn a (a + n - 1 + c) (Φ.obj K) := by
  have hshift (F : C) (hF : P F) (q : ℤ) :
      DerivedCategory.homologyConcentratedIn q (q + c)
        (Φ.obj ((DerivedCategory.singleFunctor C q).obj F)) := by
    obtain ⟨hge, hle⟩ := hsingle F hF
    have := hge
    have := hle
    let e : (Φ.obj ((DerivedCategory.singleFunctor C 0).obj F))⟦-q⟧ ≅
        Φ.obj ((DerivedCategory.singleFunctor C q).obj F) :=
      (Φ.commShiftIso (-q)).symm.app _ ≪≫
        Φ.mapIso (((DerivedCategory.singleFunctors C).shiftIso (-q) q 0 (by lia)).app F)
    have : DerivedCategory.TStructure.t.IsGE
        ((Φ.obj ((DerivedCategory.singleFunctor C 0).obj F))⟦-q⟧) q :=
      DerivedCategory.TStructure.t.isGE_shift _ 0 (-q) q (by lia)
    have : DerivedCategory.TStructure.t.IsLE
        ((Φ.obj ((DerivedCategory.singleFunctor C 0).obj F))⟦-q⟧) (q + c) :=
      DerivedCategory.TStructure.t.isLE_shift _ c (-q) (q + c) (by lia)
    exact ⟨DerivedCategory.TStructure.t.isGE_of_iso e q,
      DerivedCategory.TStructure.t.isLE_of_iso e (q + c)⟩
  induction n with
  | zero =>
    intro a K hge hle _
    have := hge
    have : K.IsLE (a - 1) := by simpa using hle
    have hz := Φ.map_isZero (DerivedCategory.TStructure.t.isZero K (a - 1) a (by lia))
    exact ⟨DerivedCategory.TStructure.t.isGE_of_isZero hz a,
      DerivedCategory.TStructure.t.isLE_of_isZero hz _⟩
  | succ n ih =>
    intro a K hge hle hK
    let b : ℤ := a + n
    have := hge
    have := hle
    have : K.IsLE b :=
      DerivedCategory.TStructure.t.isLE_of_le K (a + ↑(n + 1) - 1) b (by dsimp [b]; lia)
    have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished b K
    have hmap := Φ.map_distinguished _ hT
    have hleft : DerivedCategory.homologyConcentratedIn a (a + n - 1 + c)
        (Φ.obj ((DerivedCategory.TStructure.t.triangleLTGE b).obj K).obj₁) := by
      refine ih a _ ?_ ?_ fun q hq hq' ↦ ?_
      · exact inferInstanceAs
          (DerivedCategory.TStructure.t.IsGE ((DerivedCategory.TStructure.t.truncLT b).obj K) a)
      · exact DerivedCategory.TStructure.t.isLE_truncLT_obj _ _ _ (by dsimp [b]; lia)
      · have := DerivedCategory.isIso_homologyFunctor_map_truncLTι_app K b q
          (by dsimp [b]; lia)
        exact P.prop_of_iso
          (asIso ((DerivedCategory.homologyFunctor C q).map
            ((DerivedCategory.TStructure.t.truncLTι b).app K))).symm
          (hK q hq (by lia))
    have : ((DerivedCategory.TStructure.t.triangleLTGE b).obj K).obj₃.IsLE b :=
      inferInstanceAs
        (DerivedCategory.TStructure.t.IsLE ((DerivedCategory.TStructure.t.truncGE b).obj K) b)
    have : ((DerivedCategory.TStructure.t.triangleLTGE b).obj K).obj₃.IsGE b := by
      infer_instance
    obtain ⟨F, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
      ((DerivedCategory.TStructure.t.triangleLTGE b).obj K).obj₃ b
    have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K b b le_rfl
    have hF : P F := P.prop_of_iso
      (asIso ((DerivedCategory.homologyFunctor C b).map
          ((DerivedCategory.TStructure.t.truncGEπ b).app K)) ≪≫
        (DerivedCategory.homologyFunctor C b).mapIso e ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C b).app F)
      (hK b (by dsimp [b]; lia) (by dsimp [b]; lia))
    obtain ⟨hgeF, hleF⟩ := hshift F hF b
    have := hgeF
    have := hleF
    have hright : DerivedCategory.homologyConcentratedIn b (b + c)
        (Φ.obj ((DerivedCategory.TStructure.t.triangleLTGE b).obj K).obj₃) :=
      ⟨DerivedCategory.TStructure.t.isGE_of_iso (Φ.mapIso e.symm) b,
        DerivedCategory.TStructure.t.isLE_of_iso (Φ.mapIso e.symm) (b + c)⟩
    obtain ⟨hgeL, hleL⟩ := hleft
    obtain ⟨hgeR, hleR⟩ := hright
    have := hgeL
    have := hleL
    have := hgeR
    have := hleR
    constructor
    · exact DerivedCategory.TStructure.t.isGE₂ _ hmap a hgeL
        (DerivedCategory.TStructure.t.isGE_of_ge
          (Φ.obj ((DerivedCategory.TStructure.t.triangleLTGE b).obj K).obj₃)
          a b (by dsimp [b]; lia))
    · exact DerivedCategory.TStructure.t.isLE₂ _ hmap _
        (DerivedCategory.TStructure.t.isLE_of_le
          (Φ.obj ((DerivedCategory.TStructure.t.triangleLTGE b).obj K).obj₁)
          (a + n - 1 + c) _ (by lia))
        (DerivedCategory.TStructure.t.isLE_of_le
          (Φ.obj ((DerivedCategory.TStructure.t.triangleLTGE b).obj K).obj₃)
          (b + c) _ (by dsimp [b]; lia))

/-- Under the specified FIN bound, ordinary derived direct image restricts, on all
objects and all morphisms, to an exact triangulated functor between the recorded full
bounded constructible subcategories. Cohomological intervals change from [a,b] to
[a,b+c], including the zero object when a>b.
Source: blueprint order 1302; Stacks Project, Tags 05TC, 08J5, 09AK and 09AL
(blueprint: prop-weil-pbc-restriction-direct-image).

Proof: the canonical coefficient structure is locally an isomorphism on constant
scalars. Direct image is additive and preserves kernels sectionwise, so its ordinary
right derived functor agrees on bounded below objects with the bounded below right
derived functor. Negative cohomology on a sheaf placed in degree zero therefore
vanishes (Tag 05TC). Finite-ring comparison identifies each constructible cohomology
sheaf of K with a constructible etale-origin sheaf (Tags 09AK and 09AL). FIN gives
constructibility of its higher direct images in nonnegative degrees and vanishing
above c, hence an image in degrees [0,c]. After a shift by -q, the interval is [q,q+c].

If a>b, K is acyclic and is zero in the localization, and its additive derived image
is zero. Otherwise use successive canonical truncation triangles from degree a to b
(Tag 08J5). The initial truncation is zero; each successive quotient is H^q(K)[-q].
Induction on these triangles, using the long exact cohomology sequence and the
triangulated closure of bounded constructibles, puts the image in [a,b+c] and makes
it bounded constructible. The last truncation is isomorphic to K. Finally restrict
the ambient functor to these full subcategories: its morphism maps are unchanged,
its shift isomorphisms restrict, and its images of distinguished triangles are
distinguished because this is true in the ambient category. Mathlib's lift of the
composite of the inclusion and ambient functor records precisely this restriction. -/
theorem restrictionDirectImage
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) (htorsion : IsAddTorsion (A ⧸ I))
    [hfinite : ∀ m : ℕ+, Finite (A ⧸ I ^ (m : ℕ))]
    (hperfect : ∀ m : ℕ+,
      @DerivedCategory.IsPerfectRingComplex A _ (HasDerivedCategory.standard _)
        ((@DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) _ _
          (HasDerivedCategory.standard _) 0).obj (ModuleCat.of A (A ⧸ I ^ (m : ℕ)))))
    (n : ℕ+) {S T : Scheme.{u}} [IsNoetherian T]
    (hdim : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (horder : ∀ (a : A ⧸ I ^ (n : ℕ)) (t : T),
      IsUnit (addOrderOf a : T.presheaf.stalk t))
    (f : S ⟶ T) (c : ℕ)
    (hfin : ConstructibleDirectImageFiniteness A I hI htorsion hperfect n hdim horder f c) :
    letI : TopologicalSpace (A ⧸ I ^ (n : ℕ)) := ⊥
    letI : DiscreteTopology (A ⧸ I ^ (n : ℕ)) := ⟨rfl⟩
    ∃ h : ∀ K : FiniteCoefficientBoundedConstructibleDerivedCategory S (A ⧸ I ^ (n : ℕ)),
      isBoundedConstructibleFiniteCoefficient T (A ⧸ I ^ (n : ℕ))
        ((finiteCoefficientDerivedDirectImage f (A ⧸ I ^ (n : ℕ))).obj K.obj),
      ((isBoundedConstructibleFiniteCoefficient T (A ⧸ I ^ (n : ℕ))).lift
        ((isBoundedConstructibleFiniteCoefficient S (A ⧸ I ^ (n : ℕ))).ι ⋙
          finiteCoefficientDerivedDirectImage f (A ⧸ I ^ (n : ℕ))) h).IsTriangulated ∧
      ∀ (K : FiniteCoefficientBoundedConstructibleDerivedCategory S (A ⧸ I ^ (n : ℕ)))
        (a b : ℤ),
        (∀ i : ℤ, (i < a ∨ b < i) → IsZero
          ((DerivedCategory.homologyFunctor
            (FiniteCoefficientModules S (A ⧸ I ^ (n : ℕ))) i).obj K.obj)) →
        ∀ i : ℤ, (i < a ∨ b + (c : ℤ) < i) → IsZero
          ((DerivedCategory.homologyFunctor
            (FiniteCoefficientModules T (A ⧸ I ^ (n : ℕ))) i).obj
              ((finiteCoefficientDerivedDirectImage f (A ⧸ I ^ (n : ℕ))).obj K.obj)) := by
  let Λ := A ⧸ I ^ (n : ℕ)
  let : TopologicalSpace Λ := ⊥
  let : DiscreteTopology Λ := ⟨rfl⟩
  let P : ObjectProperty (FiniteCoefficientModules S Λ) :=
    IsConstructibleFiniteCoefficientSheaf S Λ
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ coefficientConstructible_iso e h⟩
  let Φ := finiteCoefficientDerivedDirectImage f Λ
  have hsingle (F : FiniteCoefficientModules S Λ) (hF : P F) :
      DerivedCategory.homologyConcentratedIn 0 (c : ℤ)
        (Φ.obj ((DerivedCategory.singleFunctor _ 0).obj F)) := by
    refine ⟨coefficientImage_single_nonnegative f Λ F, ?_⟩
    exact (DerivedCategory.isLE_iff _ (c : ℤ)).mpr (fun i hi ↦ hfin.2 F hF i hi)
  have hsingleConstructible (F : FiniteCoefficientModules S Λ) (hF : P F) :
      isBoundedConstructibleFiniteCoefficient T Λ
        (Φ.obj ((DerivedCategory.singleFunctor _ 0).obj F)) := by
    obtain ⟨hge, hle⟩ := hsingle F hF
    apply coefficientConstructible_of_cohomology _ ⟨⟨0, hge⟩, ⟨c, hle⟩⟩
    intro j
    by_cases hj : 0 ≤ j
    · exact hfin.1 F hF j hj
    · apply coefficientConstructible_zero
      exact (DerivedCategory.isGE_iff _ 0).mp hge j (by lia)
  have : (isBoundedConstructibleFiniteCoefficient T Λ).IsClosedUnderIsomorphisms := by
    dsimp only [isBoundedConstructibleFiniteCoefficient]
    infer_instance
  let Q := (isBoundedConstructibleFiniteCoefficient T Λ).inverseImage Φ
  have h (K : FiniteCoefficientBoundedConstructibleDerivedCategory S Λ) :
      isBoundedConstructibleFiniteCoefficient T Λ (Φ.obj K.obj) := by
    obtain ⟨hb, hc⟩ := coefficientConstructible_cohomology K.obj K.property
    exact DerivedCategory.prop_of_bounded Q P hsingleConstructible K.obj hb hc
  refine ⟨h, inferInstance, ?_⟩
  intro K a b hK
  have hge : K.obj.IsGE a :=
    (DerivedCategory.isGE_iff _ a).mpr (fun i hi ↦ hK i (Or.inl hi))
  have hle : K.obj.IsLE b :=
    (DerivedCategory.isLE_iff _ b).mpr (fun i hi ↦ hK i (Or.inr hi))
  have := hge
  have := hle
  by_cases hab : a ≤ b
  · have heq : a + ((b - a + 1).toNat : ℤ) - 1 = b := by lia
    have hle' : K.obj.IsLE (a + ((b - a + 1).toNat : ℤ) - 1) := by
      simpa only [heq] using hle
    have hc := (coefficientConstructible_cohomology K.obj K.property).2
    have hbound := constructibleAmplitude Φ P (c : ℤ) hsingle
      (b - a + 1).toNat a K.obj hge hle' (fun q _ _ ↦ hc q)
    rw [heq] at hbound
    intro i hi
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff _ a).mp hbound.1 i hi
    · exact (DerivedCategory.isLE_iff _ (b + c)).mp hbound.2 i hi
  · have hz := Φ.map_isZero (DerivedCategory.TStructure.t.isZero K.obj b a (by lia))
    intro i _
    exact (DerivedCategory.homologyFunctor _ i).map_isZero hz

end AlgebraicGeometry.ProEtale
