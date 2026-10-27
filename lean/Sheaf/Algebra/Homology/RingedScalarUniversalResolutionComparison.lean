/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-! # Universal ringed-site scalar extension and normalized resolution comparisons

Source: Stacks Project, derived.tex, Tag 06XN (lemma-find-existence-computes),
Tag 05S9 and equation-everywhere; sites-cohomology.tex, Tag 06YY.
(blueprint: lem-trf-ringed-scalar-universal-resolution-comparison).

The auxiliary definitions package the explicit formulas of this node. In particular,
`resolutionCounitIso` is the inverse localized augmentation followed by the counit;
no comparison map or choice of a resolution is supplied as additional data.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe uA vA uD vD uB vB u v r wO wS
open CategoryTheory

namespace CategoryTheory.Functor

section Formulas

variable {A : Type uA} [Category.{vA} A]
  {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
  (Q : A ⥤ D) (W : MorphismProperty A) [Q.IsLocalization W]
  {F : A ⥤ B} (L : D ⥤ B) (ε : Q ⋙ L ⟶ F)

/-- The normalized computation on a resolving object is exactly
`L(Qq)⁻¹ ≫ ε_P`. Source: Stacks 06XN and equation-everywhere
(blueprint: lem-trf-ringed-scalar-universal-resolution-comparison). -/
def resolutionCounitIso {P X : A} (q : P ⟶ X) (hq : W q)
    (hε : IsIso (ε.app P)) : L.obj (Q.obj X) ≅ F.obj P :=
  letI : IsIso (Q.map q) := Localization.inverts Q W q hq
  letI := hε
  (L.mapIso (asIso (Q.map q))).symm ≪≫ asIso (ε.app P)

/-- The augmentation, arbitrary-square, identity and cocycle formulas, with every
comparison defined as `θ_q.symm ≪≫ θ_q'`.
Source: Stacks 06XN, equation-everywhere and sites-cohomology.tex 06YY
(blueprint: lem-trf-ringed-scalar-universal-resolution-comparison). -/
structure ResolutionCounitLaws (P : Set A) (hc : ∀ X ∈ P, IsIso (ε.app X)) : Prop where
  augmentation : ∀ (K X : A) (q : K ⟶ X) (hK : K ∈ P) (hq : W q),
    (resolutionCounitIso Q W L ε q hq (hc K hK)).hom ≫ F.map q = ε.app X
  square : ∀ (K X K' X' : A) (q : K ⟶ X) (q' : K' ⟶ X')
    (hK : K ∈ P) (hK' : K' ∈ P) (hq : W q) (hq' : W q')
    (a : X ⟶ X') (b : K ⟶ K'), q ≫ a = b ≫ q' →
      (resolutionCounitIso Q W L ε q hq (hc K hK)).hom ≫ F.map b =
        L.map (Q.map a) ≫ (resolutionCounitIso Q W L ε q' hq' (hc K' hK')).hom
  comparison_augmentation : ∀ (K K' X : A) (q : K ⟶ X) (q' : K' ⟶ X)
    (hK : K ∈ P) (hK' : K' ∈ P) (hq : W q) (hq' : W q'),
    ((resolutionCounitIso Q W L ε q hq (hc K hK)).symm ≪≫
      resolutionCounitIso Q W L ε q' hq' (hc K' hK')).hom ≫ F.map q' = F.map q
  identity : ∀ (K X : A) (q : K ⟶ X) (hK : K ∈ P) (hq : W q),
    (resolutionCounitIso Q W L ε q hq (hc K hK)).symm ≪≫
      resolutionCounitIso Q W L ε q hq (hc K hK) = Iso.refl (F.obj K)
  cocycle : ∀ (K₁ K₂ K₃ X : A) (q₁ : K₁ ⟶ X) (q₂ : K₂ ⟶ X) (q₃ : K₃ ⟶ X)
    (h₁ : K₁ ∈ P) (h₂ : K₂ ∈ P) (h₃ : K₃ ∈ P)
    (hq₁ : W q₁) (hq₂ : W q₂) (hq₃ : W q₃),
    ((resolutionCounitIso Q W L ε q₁ hq₁ (hc K₁ h₁)).symm ≪≫
        resolutionCounitIso Q W L ε q₂ hq₂ (hc K₂ h₂)) ≪≫
      ((resolutionCounitIso Q W L ε q₂ hq₂ (hc K₂ h₂)).symm ≪≫
        resolutionCounitIso Q W L ε q₃ hq₃ (hc K₃ h₃)) =
      (resolutionCounitIso Q W L ε q₁ hq₁ (hc K₁ h₁)).symm ≪≫
        resolutionCounitIso Q W L ε q₃ hq₃ (hc K₃ h₃)

/-- Universality and all resolution formulas, including their normalization for every
other universal pair. The test functor `H` is arbitrary.
Source: Stacks 05S9, 06XN and equation-everywhere
(blueprint: lem-trf-ringed-scalar-universal-resolution-comparison). -/
structure UniversalResolutionCounit (P : Set A) : Prop where
  universal : ∀ H : D ⥤ B,
    Function.Bijective (fun α : H ⟶ L ↦ whiskerLeft Q α ≫ ε)
  computes : ∀ K ∈ P, IsIso (ε.app K)
  laws : ResolutionCounitLaws Q W L ε P computes
  change_pair : ∀ (M : D ⥤ B) (η : Q ⋙ M ⟶ F),
    (∀ H : D ⥤ B, Function.Bijective (fun α : H ⟶ M ↦ whiskerLeft Q α ≫ η)) →
    ∃ hcM : ∀ K ∈ P, IsIso (η.app K),
      ResolutionCounitLaws Q W M η P hcM ∧
      ∃ i : L ≅ M,
        (whiskerLeft Q i.hom ≫ η = ε) ∧
        (∀ j : L ≅ M, whiskerLeft Q j.hom ≫ η = ε → j = i) ∧
        (∀ (K X : A) (q : K ⟶ X) (hK : K ∈ P) (hq : W q),
          resolutionCounitIso Q W L ε q hq (computes K hK) =
            i.app (Q.obj X) ≪≫ resolutionCounitIso Q W M η q hq (hcM K hK)) ∧
        (∀ (K K' X : A) (q : K ⟶ X) (q' : K' ⟶ X)
          (hK : K ∈ P) (hK' : K' ∈ P) (hq : W q) (hq' : W q'),
          (resolutionCounitIso Q W L ε q hq (computes K hK)).symm ≪≫
              resolutionCounitIso Q W L ε q' hq' (computes K' hK') =
            (resolutionCounitIso Q W M η q hq (hcM K hK)).symm ≪≫
              resolutionCounitIso Q W M η q' hq' (hcM K' hK'))

end Formulas

section Cochains

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  [HasDerivedCategory.{wO} A] [HasDerivedCategory.{wS} B]

/-- Re-express the homotopy counit on cochains using the existing quotient and
termwise-functor comparison isomorphisms.
Source: Stacks 06YY, the passage from `K(O)` to complexes
(blueprint: lem-trf-ringed-scalar-universal-resolution-comparison). -/
def scalarHomotopyCounitOnCochains (E : A ⥤ B) [E.Additive]
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ L ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  whiskerRight (DerivedCategory.quotientCompQhIso A).inv L ≫
    (associator (HomotopyCategory.quotient A (.up ℤ)) DerivedCategory.Qh L).hom ≫
    whiskerLeft (HomotopyCategory.quotient A (.up ℤ)) ε ≫
    ((associator _ _ _).symm ≪≫
      isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)).hom

end Cochains
end CategoryTheory.Functor

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  {O S : Sheaf J CommRingCat.{r}}
  [HasDerivedCategory.{wO}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J O))]
  [HasDerivedCategory.{wS}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S))]

/-- All K-flat objects of the homotopy category, represented using the recorded
independent-coefficient K-flat predicate. No flat-terms condition is imposed.
Source: Stacks 06YN, 06XN and the fixed-site case of 06YY
(blueprint: lem-trf-ringed-scalar-universal-resolution-comparison). -/
def ringedScalarKFlatObjects (R : Sheaf J CommRingCat.{r}) :
    Set (HomotopyCategory
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) (.up ℤ)) :=
  fun X ↦ ∃ P : CochainComplex
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P ∧
      (HomotopyCategory.quotient _ (.up ℤ)).obj P = X

/-- Universal scalar extension, with normalized comparisons for every K-flat resolution.
Source: Stacks Project, derived.tex, Tag 06XN (dual assertion), 05S9 and
 equation-everywhere; sites-cohomology.tex, Tag 06YY, fixed-site change of rings
(blueprint: lem-trf-ringed-scalar-universal-resolution-comparison).

The presentation `M` of lem-pur-derived-change-of-rings is arbitrary; its ordinary
extension `M.E` is fixed on objects and maps, and `F` carries Mathlib's canonical shift.

Proof:
1. Ordinary sheafified tensor extension is additive on presheaf tensor generators;
   sheafification preserves the addition and zero formulas. The module categories
   are abelian by def-weil-sheaf-of-modules-category. Apply
   lem-trf-additive-homotopy-triangulated to its termwise homotopy functor and
   lem-pur-homotopy-category-triangulated to Qh: their composite F is exact.
2. By lem-pc-kflat-resolution every complex has a K-flat resolution. Its extra
   flat-terms conclusion need not be required of other resolving objects. By
   lem-pur-change-of-rings-kflat-quasi-iso the actual extension sends every
   quasi-isomorphism between K-flat objects to a quasi-isomorphism, so Qh inverts it.
3. Apply lem-pur-left-derived-from-kflat-class to F and all K-flat objects.
   It gives an exact universal pair and invertible counits on that class. Its
   right-Kan property is exactly the displayed bijection for arbitrary H.
4. Universality gives unique counit-compatible maps between any two universal
   pairs, including lem-pur-derived-change-of-rings. Injectivity applied to their
   composites proves that they are inverse. Invertible counits on K-flat objects
   therefore transfer to every universal pair. Use quotientCompQhIso and
   mapHomotopyCategoryFactors to compare with the existing cochain model.
5. For q:P→X, Qh(q) is invertible. The defined theta is its inverse image under L
   followed by epsilon_P. Naturality at q gives theta_q followed by F(q)=epsilon_X.
6. For q followed by a = b followed by q', functoriality, naturality at b and
   cancellation of the two localized resolutions give the arbitrary-square formula.
7. Define c_ij as theta_i inverse followed by theta_j. Cancellation gives identity
   and the three-resolution cocycle. The augmentation formula gives compatibility
   with F(q_i) and F(q_j); no map between the two resolutions is chosen.
8. The unique counit-compatible isomorphism i:L≅M gives theta_L=i_X theta_M
   by naturality and the counit square. Consequently the c_ij agree in both pairs.
   All inverses are localized quasi-isomorphisms or counits on K-flat objects;
   neither flatness of the ring map nor boundedness is used. -/
theorem ringedScalar_universal_resolution_comparison (φ : O ⟶ S)
    (M : DerivedChangeOfRingsCochainModel.{u, v, r, wO, wS} φ) :
      (M.E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).IsTriangulated ∧
      (∀ X : HomotopyCategory
          (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J O)) (.up ℤ),
        ∃ (P : HomotopyCategory
            (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J O)) (.up ℤ))
          (q : P ⟶ X), P ∈ ringedScalarKFlatObjects O ∧
            HomotopyCategory.quasiIso _ (.up ℤ) q) ∧
      (∀ (P P' : HomotopyCategory
          (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J O)) (.up ℤ))
        (s : P ⟶ P'), P ∈ ringedScalarKFlatObjects O →
        P' ∈ ringedScalarKFlatObjects O → HomotopyCategory.quasiIso _ (.up ℤ) s →
          IsIso ((M.E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map s)) ∧
      ∃ (L : DerivedCategory
          (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J O)) ⥤
          DerivedCategory
            (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S)))
        (ε : DerivedCategory.Qh ⋙ L ⟶
          M.E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
        (∃ (_ : L.CommShift ℤ), L.IsTriangulated) ∧
        Functor.UniversalResolutionCounit DerivedCategory.Qh
          (HomotopyCategory.quasiIso _ (.up ℤ)) L ε (ringedScalarKFlatObjects O) ∧
        ∃ i : L ≅ M.T,
          (Functor.whiskerLeft DerivedCategory.Q i.hom ≫ M.ε =
            Functor.scalarHomotopyCounitOnCochains M.E L ε) ∧
          (∀ j : L ≅ M.T, Functor.whiskerLeft DerivedCategory.Q j.hom ≫ M.ε =
            Functor.scalarHomotopyCounitOnCochains M.E L ε → j = i) := by
  sorry

end SheafOfModules
