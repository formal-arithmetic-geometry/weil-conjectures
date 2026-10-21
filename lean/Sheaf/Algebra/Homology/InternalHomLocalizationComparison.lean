/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
public import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
public import Sheaf.CategoryTheory.RingedSiteLocalization
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.CategoryTheory.Localization.Adjunction
import all Sheaf.CategoryTheory.LocalizationInverseImageCoherence
import Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit
import all Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import all Sheaf.CategoryTheory.ClosedScalarHomComparison
import all Sheaf.Algebra.Homology.ScalarHomTensorCancellation
import all Sheaf.Algebra.Homology.ScalarHomOrdinaryTensorComparison
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Internal Hom and localization under sequential continuity

Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61--62,
conditional internal-sheaf localization argument (not the global Hom assertion);
Stacks Project, Tags 03CY, 03DB, 03ET, 06YY, 07A6 and 08J9
(blueprint: lem-sfb-internal-hom-localization-comparison).

All derived operations are the recorded, evaluation-normalized operations.
Sequential colimits are formed in complexes of module sheaves, before applying Q.
The functorial Hom representatives are the same ones as in the recorded internal Hom.
Exact filtered colimits are supplied by the Grothendieck-abelian module-sheaf theorem
on this small site; no independent exactness witness or stronger coefficient condition is needed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe c v r w

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures SheafOfModules
open CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open scoped ChangeOfRings

attribute [local instance] isMonoidal_W_independentCoefficients
attribute [local irreducible] SheafOfModules.monoidalCategory
  derivedInternalHomOfUniverses

namespace CategoryTheory
namespace LocalizationHomProof

universe u₁ v₁ u₂ v₂
variable {A : Type u₁} [Category.{v₁} A] {H : Aᵒᵖ × A ⥤ A}
  (S : CoefficientClosedStructure H)

private theorem uncurry_precomp {X Y K N : A} (f : X ⟶ Y)
    (t : Y ⟶ H.obj (op K, N)) :
    (S.transpose X K N).symm (f ≫ t) =
      S.tensor.map (Prod.mkHom f (𝟙 K)) ≫ (S.transpose Y K N).symm t := by
  simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    Prod.sectR, Functor.comp_obj] using
    (S.adjunction K).homEquiv_naturality_left_symm f t

private theorem unit_precomp_injective
    {B : Type u₂} [Category.{v₂} B] {F : A ⥤ B} {U : B ⥤ A}
    (adj : F ⊣ U) [U.Full] (X : A) (Y : B) :
    Function.Injective (fun f : U.obj (F.obj X) ⟶ U.obj Y ↦ adj.unit.app X ≫ f) := by
  intro f g h
  obtain ⟨f', rfl⟩ := U.map_surjective f
  obtain ⟨g', rfl⟩ := U.map_surjective g
  apply congrArg U.map
  apply (adj.homEquiv X Y).injective
  simpa only [Adjunction.homEquiv_unit] using h

private def closedComparison
    {B : Type u₂} [Category.{v₂} B] {I : Bᵒᵖ × B ⥤ B}
    (T : CoefficientClosedStructure I) (F : A ⥤ B)
    (μ : S.tensor ⋙ F ≅ F.prod F ⋙ T.tensor) (K L : A) :
    F.obj (H.obj (op K, L)) ⟶ I.obj (op (F.obj K), F.obj L) :=
  T.transpose _ _ _ (μ.inv.app (H.obj (op K, L), K) ≫ F.map (S.evaluation K L))

private theorem closedComparison_naturality
    {B : Type u₂} [Category.{v₂} B] {I : Bᵒᵖ × B ⥤ B}
    (T : CoefficientClosedStructure I) (F : A ⥤ B)
    (μ : S.tensor ⋙ F ≅ F.prod F ⋙ T.tensor)
    (K L K' L' : A) (f : K' ⟶ K) (g : L ⟶ L') :
    F.map (H.map (Prod.mkHom f.op g)) ≫ closedComparison S T F μ K' L' =
      closedComparison S T F μ K L ≫
        I.map (Prod.mkHom (F.map f).op (F.map g)) := by
  apply (T.transpose _ _ _).symm.injective
  rw [uncurry_precomp, ClosedScalarHom.uncurry_naturality]
  dsimp only [closedComparison]
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  let X := H.obj (op K, L)
  let X' := H.obj (op K', L')
  let t := H.map (Prod.mkHom f.op g)
  have h₁ := μ.inv.naturality (Prod.mkHom t (𝟙 K'))
  have h₂ := μ.inv.naturality (Prod.mkHom (𝟙 X) f)
  simp only [Functor.comp_map, Functor.prod_map, Functor.map_id] at h₁ h₂
  change T.tensor.map (Prod.mkHom (F.map t) (𝟙 (F.obj K'))) ≫
      (μ.inv.app (X', K') ≫ F.map (S.evaluation K' L')) =
    T.tensor.map (Prod.mkHom (𝟙 (F.obj X)) (F.map f)) ≫
      (μ.inv.app (X, K) ≫ F.map (S.evaluation K L)) ≫ F.map g
  calc
    _ = μ.inv.app (X, K') ≫ F.map
        (S.tensor.map (Prod.mkHom t (𝟙 K')) ≫ S.evaluation K' L') := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun z ↦ z ≫ F.map (S.evaluation K' L')) h₁
    _ = μ.inv.app (X, K') ≫ F.map
        (S.tensor.map (Prod.mkHom (𝟙 X) f) ≫ S.evaluation K L ≫ g) := by
      rw [ClosedScalarHom.evaluation_both]
    _ = _ := by
      simpa only [Functor.map_comp, Category.assoc] using
        (congrArg (fun z ↦ z ≫ F.map (S.evaluation K L) ≫ F.map g) h₂).symm

private def exact_adjunction
    {B : Type u₂} [Category.{v₂} B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) (U : B ⥤ A) [F.Additive] [U.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (adj : F ⊣ U) : F.mapDerivedCategory ⊣ U.mapDerivedCategory := by
  letI : CatCommSq (F.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (U.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q U.mapDerivedCategory :=
    ⟨U.mapDerivedCategoryFactors.symm⟩
  exact (adj.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso B (.up ℤ))
    F.mapDerivedCategory U.mapDerivedCategory

private theorem exact_adjunction_unit
    {B : Type u₂} [Category.{v₂} B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) (U : B ⥤ A) [F.Additive] [U.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (adj : F ⊣ U) (P : CochainComplex A ℤ) :
    (exact_adjunction F U adj).unit.app (DerivedCategory.Q.obj P) ≫
        U.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        U.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) := by
  have hu : (exact_adjunction F U adj).unit.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        U.mapDerivedCategoryFactors.inv.app _ ≫
        U.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app P) := by
    simp only [exact_adjunction, Adjunction.localization_unit_app]
    rfl
  rw [hu]
  simp only [Functor.comp_obj, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
  exact Category.comp_id _

private theorem triangle_comparison
    {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (T T' : Triangle D) (hT : T ∈ distTriang D) (hT' : T' ∈ distTriang D)
    (e₁ : T.obj₁ ≅ T'.obj₁) (e₂ : T.obj₂ ≅ T'.obj₂)
    (h : T.mor₁ ≫ e₂.hom = e₁.hom ≫ T'.mor₁) :
    ∃ e₃ : T.obj₃ ≅ T'.obj₃, T.mor₂ ≫ e₃.hom = e₂.hom ≫ T'.mor₂ := by
  obtain ⟨c, hc, hc'⟩ := Pretriangulated.complete_distinguished_triangle_morphism
    T T' hT hT' e₁.hom e₂.hom h
  let φ : T ⟶ T' :=
    { hom₁ := e₁.hom
      hom₂ := e₂.hom
      hom₃ := c
      comm₁ := h
      comm₂ := hc
      comm₃ := hc' }
  have : IsIso c := Pretriangulated.isIso₃_of_isIso₁₂ φ hT hT'
    (inferInstanceAs (IsIso e₁.hom)) (inferInstanceAs (IsIso e₂.hom))
  exact ⟨asIso c, hc⟩

universe w₁

private theorem sequential_colimit_comparison
    [Abelian A] [HasDerivedCategory.{w₁} A]
    [HasCountableCoproducts A] [HasFilteredColimitsOfSize.{0, 0} A]
    [AB5OfSize.{0, 0} A]
    (E E' : ℕ ⥤ CochainComplex A ℤ)
    (L : Cocone E) (hL : IsColimit L) (L' : Cocone E') (hL' : IsColimit L')
    (e : E ⋙ DerivedCategory.Q ≅ E' ⋙ DerivedCategory.Q) :
    ∃ β : DerivedCategory.Q.obj L.pt ≅ DerivedCategory.Q.obj L'.pt,
      ∀ n : ℕ, DerivedCategory.Q.map (L.ι.app n) ≫ β.hom =
        (e.app n).hom ≫ DerivedCategory.Q.map (L'.ι.app n) := by
  let Q := DerivedCategory.Q (C := A)
  let B := Cofan.mk (∐ fun n : ℕ ↦ E.obj n) (Sigma.ι (fun n : ℕ ↦ E.obj n))
  let B' := Cofan.mk (∐ fun n : ℕ ↦ E'.obj n) (Sigma.ι (fun n : ℕ ↦ E'.obj n))
  let u : B.pt ⟶ B.pt := Sigma.desc fun n ↦
    B.inj n - E.map (homOfLE (Nat.le_succ n)) ≫ B.inj (n + 1)
  let u' : B'.pt ⟶ B'.pt := Sigma.desc fun n ↦
    B'.inj n - E'.map (homOfLE (Nat.le_succ n)) ≫ B'.inj (n + 1)
  have hu (n : ℕ) : B.inj n ≫ u =
      B.inj n - E.map (homOfLE (Nat.le_succ n)) ≫ B.inj (n + 1) :=
    Sigma.ι_desc _ n
  have hu' (n : ℕ) : B'.inj n ≫ u' =
      B'.inj n - E'.map (homOfLE (Nat.le_succ n)) ≫ B'.inj (n + 1) :=
    Sigma.ι_desc _ n
  let q : B.pt ⟶ L.pt := Sigma.desc fun n ↦ L.ι.app n
  let q' : B'.pt ⟶ L'.pt := Sigma.desc fun n ↦ L'.ι.app n
  have hq (n : ℕ) : B.inj n ≫ q = L.ι.app n := Sigma.ι_desc _ n
  have hq' (n : ℕ) : B'.inj n ≫ q' = L'.ι.app n := Sigma.ι_desc _ n
  obtain ⟨p, hp, _, _, ⟨hB⟩, d, _, _, hT, _⟩ :=
    complex_colimit_homotopyColimit E B (coproductIsCoproduct _) L hL u hu q hq
  obtain ⟨p', hp', _, _, ⟨hB'⟩, d', _, _, hT', _⟩ :=
    complex_colimit_homotopyColimit E' B' (coproductIsCoproduct _) L' hL'
      u' hu' q' hq'
  let V := Cofan.mk (Q.obj B.pt) (fun n ↦ Q.map (B.inj n))
  let V' := Cofan.mk (Q.obj B'.pt) (fun n ↦ Q.map (B'.inj n))
  let l : Q.obj B.pt ⟶ Q.obj B'.pt :=
    hB.desc (Cofan.mk _ (fun n ↦ (e.app n).hom ≫ Q.map (B'.inj n)))
  let l' : Q.obj B'.pt ⟶ Q.obj B.pt :=
    hB'.desc (Cofan.mk _ (fun n ↦ (e.app n).inv ≫ Q.map (B.inj n)))
  have hl (n : ℕ) : Q.map (B.inj n) ≫ l =
      (e.app n).hom ≫ Q.map (B'.inj n) := hB.fac _ (Discrete.mk n)
  have hl' (n : ℕ) : Q.map (B'.inj n) ≫ l' =
      (e.app n).inv ≫ Q.map (B.inj n) := hB'.fac _ (Discrete.mk n)
  let b : Q.obj B.pt ≅ Q.obj B'.pt :=
    { hom := l
      inv := l'
      hom_inv_id := by
        apply hB.hom_ext
        rintro ⟨n⟩
        change Q.map (B.inj n) ≫ (l ≫ l') = Q.map (B.inj n) ≫ 𝟙 _
        rw [← Category.assoc, hl, Category.assoc, hl']
        simp only [Iso.hom_inv_id_assoc, Category.comp_id]
      inv_hom_id := by
        apply hB'.hom_ext
        rintro ⟨n⟩
        change Q.map (B'.inj n) ≫ (l' ≫ l) = Q.map (B'.inj n) ≫ 𝟙 _
        rw [← Category.assoc, hl', Category.assoc, hl]
        simp only [Iso.inv_hom_id_assoc, Category.comp_id] }
  have hb : Q.map u ≫ b.hom = b.hom ≫ Q.map u' := by
    apply hB.hom_ext
    rintro ⟨n⟩
    change Q.map (B.inj n) ≫ (Q.map u ≫ l) =
      Q.map (B.inj n) ≫ (l ≫ Q.map u')
    have hnat := e.hom.naturality (homOfLE (Nat.le_succ n))
    change Q.map (E.map (homOfLE (Nat.le_succ n))) ≫ (e.app (n + 1)).hom =
      (e.app n).hom ≫ Q.map (E'.map (homOfLE (Nat.le_succ n))) at hnat
    calc
      _ = (Q.map (B.inj n) - Q.map (E.map (homOfLE (Nat.le_succ n))) ≫
          Q.map (B.inj (n + 1))) ≫ l := by
        rw [← Category.assoc, ← Q.map_comp, hu, Q.map_sub, Q.map_comp]
      _ = (e.app n).hom ≫ (Q.map (B'.inj n) -
          Q.map (E'.map (homOfLE (Nat.le_succ n))) ≫
            Q.map (B'.inj (n + 1))) := by
        rw [Preadditive.sub_comp, Category.assoc, hl, hl,
          ← Category.assoc, hnat, Category.assoc, Preadditive.comp_sub]
      _ = (e.app n).hom ≫ Q.map (B'.inj n) ≫ Q.map u' := by
        simpa only [Q.map_sub, Q.map_comp, Category.assoc] using
          congrArg (fun z ↦ (e.app n).hom ≫ Q.map z) (hu' n).symm
      _ = _ := by rw [← Category.assoc, ← hl, Category.assoc]
  obtain ⟨β, hβ⟩ := triangle_comparison
    (Triangle.mk (Q.map u) (Q.map q)
      (d.inv ≫ (Q.mapTriangle.obj (CochainComplex.mappingCone.triangle u)).mor₃))
    (Triangle.mk (Q.map u') (Q.map q')
      (d'.inv ≫ (Q.mapTriangle.obj (CochainComplex.mappingCone.triangle u')).mor₃))
    hT hT' b b hb
  change Q.obj L.pt ≅ Q.obj L'.pt at β
  change Q.map q ≫ β.hom = b.hom ≫ Q.map q' at hβ
  refine ⟨β, ?_⟩
  intro n
  calc
    _ = Q.map (B.inj n) ≫ Q.map q ≫ β.hom := by
      simpa only [Q.map_comp, Category.assoc] using
        congrArg (fun z ↦ Q.map z ≫ β.hom) (hq n).symm
    _ = Q.map (B.inj n) ≫ b.hom ≫ Q.map q' := by
      exact congrArg (fun z ↦ Q.map (B.inj n) ≫ z) hβ
    _ = _ := by rw [← Category.assoc, hl, Category.assoc, ← Q.map_comp, hq']

/-- Construct a scalar-sequence cocone without unfolding its ambient category. -/
private def sequenceCocone (X Y : A) (s : X ⟶ X) (ι : ℕ → (X ⟶ Y))
    (h : ∀ n : ℕ, s ≫ ι (n + 1) = ι n) :
    Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ s)) where
  pt := Y
  ι := NatTrans.ofSequence ι (by
    intro n
    rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
    change s ≫ ι (n + 1) = ι n ≫ 𝟙 Y
    rw [Category.comp_id]
    exact h n)

private theorem id_square {X : A} {s t : X ⟶ X} (h : s = t) :
    s ≫ 𝟙 X = 𝟙 X ≫ t := by
  simpa only [Category.comp_id, Category.id_comp] using h

end LocalizationHomProof

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]

/-- Fixed functorial complex representatives of internal Hom from K. The source is
Q's chosen representative and the target uses exactly the existing K-injective functor.
Source: Stacks 08J7, 0A95; Bhatt--Scholze 6.8.12, conditional internal-sheaf version
(blueprint: lem-sfb-internal-hom-localization-comparison). -/
def localizationHomComplex (R : Sheaf J CommRingCat.{max c v r})
    (K : DerivedCategory (scalarModules J R)) :
    CochainComplex (scalarModules J R) ℤ ⥤ CochainComplex (scalarModules J R) ℤ :=
  coefficientHomResolution.{r, c, v} J R ⋙
    (homComplexFunctor (R := R)).obj (op (DerivedCategory.Q.objPreimage K))

/-- The canonical continuity comparison is induced by the Hom images of the colimit legs.
Taking Q afterwards means that being an isomorphism means being a quasi-isomorphism,
not an isomorphism of complexes. Source: Stacks 03DB and 08J9; Bhatt--Scholze 6.8.12
(blueprint: lem-sfb-internal-hom-localization-comparison). -/
def localizationHomContinuityMap (R : Sheaf J CommRingCat.{max c v r})
    (K : DerivedCategory (scalarModules J R))
    (D : ℕ ⥤ CochainComplex (scalarModules J R) ℤ) :
    DerivedCategory.Q.obj (colimit (D ⋙ localizationHomComplex.{c, v, r, w} J R K)) ⟶
      DerivedCategory.Q.obj ((localizationHomComplex.{c, v, r, w} J R K).obj (colimit D)) :=
  DerivedCategory.Q.map
    (colimit.post D (localizationHomComplex.{c, v, r, w} J R K))

/-- The displayed hypothesis: all sequential diagrams with a common termwise lower
bound have invertible evaluation-induced internal-Hom colimit comparison.
Source: Bhatt--Scholze 6.8.12, conditional internal-sheaf formulation
(blueprint: lem-sfb-internal-hom-localization-comparison). -/
def HasLocalizationHomContinuity (R : Sheaf J CommRingCat.{max c v r})
    (K : DerivedCategory (scalarModules J R)) : Prop :=
  ∀ D : ℕ ⥤ CochainComplex (scalarModules J R) ℤ,
    (∃ a : ℤ, ∀ n : ℕ, (D.obj n).IsStrictlyGE a) →
      IsIso (localizationHomContinuityMap.{c, v, r, w} J R K D)

variable {J}
  (M : ScalarHomModels.{c, v, r, w} J)
  {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)

/-- The actual canonical comparison: extend evaluation, use the inverse strong tensor
comparison, and transpose over S. No comparison arrow is supplied as a hypothesis.
Source: Stacks 07A4, 07A6 and 08J9; Bhatt--Scholze 6.8.14(2), conditional argument
(blueprint: lem-sfb-internal-hom-localization-comparison). -/
def localizationHomComparison (μ : ScalarHomTensorComparison M a)
    (K L : DerivedCategory (scalarModules J R)) :
    (M.scalar a).derived.obj ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
        (op K, L)) ⟶
      (derivedInternalHomOfUniverses.{c, v, r, w} J S).obj
        (op ((M.scalar a).derived.obj K), (M.scalar a).derived.obj L) :=
  (M.closed S).transpose _ ((M.scalar a).derived.obj K) ((M.scalar a).derived.obj L)
    (μ.iso.inv.app
      ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L), K) ≫
      (M.scalar a).derived.map ((M.closed R).evaluation K L))

/-- Restrict the actual comparison and apply the evaluation-normalized scalar-Hom
adjunction. This is the map identified with sequential continuity by the theorem.
Source: Stacks 07A6 and 08J9; Bhatt--Scholze 6.8.14(2), conditional argument
(blueprint: lem-sfb-internal-hom-localization-comparison). -/
def localizationHomRestrictedComparison
    (μ : ∀ {A B : Sheaf J CommRingCat.{max c v r}} (b : A ⟶ B),
      ScalarHomTensorComparison M b)
    (α : ScalarInternalHomAdjunction M μ)
    (K L : DerivedCategory (scalarModules J R)) :
    (scalarDerivedRestriction a).obj
        ((M.scalar a).derived.obj
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L))) ⟶
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
        (op K, (scalarDerivedRestriction a).obj ((M.scalar a).derived.obj L)) :=
  (scalarDerivedRestriction a).map (localizationHomComparison.{c, v, r, w} M a (μ a) K L) ≫
    (α.iso a).hom.app (op K, (M.scalar a).derived.obj L)

private def localizationRestrictedTensorPresheafIso (N : scalarModules J R) :
    N.val ⊗ ((scalarRestriction a).obj (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val ≅
    (PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map a).hom).obj
        (changeOfRingsPresheaf a N) := by
  refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
  · let ρ := (a.hom.app V).hom
    change ModuleCat.of (R.obj.obj V) (TensorProduct (R.obj.obj V) (N.val.obj V)
      ((ModuleCat.restrictScalars ρ).obj (ModuleCat.of (S.obj.obj V) (S.obj.obj V)))) ≅
      (ModuleCat.restrictScalars ρ).obj
        ((ModuleCat.extendScalars ρ).obj (N.val.obj V))
    exact (TensorProduct.comm (R.obj.obj V) (N.val.obj V)
      ((ModuleCat.restrictScalars ρ).obj (ModuleCat.of (S.obj.obj V)
        (S.obj.obj V)))).toModuleIso
  · intro V W f
    apply ModuleCat.hom_ext
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x b =>
        change S.obj.map f b ⊗ₜ[R.obj.obj W, (a.hom.app W).hom] N.val.map f x =
          changeOfRingsMap a N f (b ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x)
        exact (Classical.choose_spec (exists_changeOfRingsMap a N f) b x).symm

private def localizationRestrictedTensorIso (N : scalarModules J R) :
    (SheafOfModules.monoidalCategory R).tensorObj N
      ((scalarRestriction a).obj (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) ≅
      (scalarRestriction a).obj (changeOfRings a N) := by
  let _ := SheafOfModules.monoidalCategory R
  let F := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  exact tensorObjIsoSheafification N _ ≪≫
    F.mapIso (localizationRestrictedTensorPresheafIso.{c, v, r} a N) ≪≫
      ScalarHomCancellation.cancellationRestrictSheafifyIso
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)
        (changeOfRingsPresheaf a N)

attribute [local irreducible] ScalarHomCancellation.cancellationRestrictSheafifyIso
  ScalarHomCancellation.cancellationRestrictSheafifyHom

omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)]
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})] in
private theorem localizationRestrictionSheafification_unit
    {A B : Sheaf J RingCat.{max c v r}} (a₀ : A ⟶ B)
    (P : PresheafOfModules.{max c v r} B.obj) (V : Cᵒᵖ) (x : P.obj V) :
    (ScalarHomCancellation.cancellationRestrictSheafifyIso a₀ P).hom.val.app V
      (((PresheafOfModules.sheafificationAdjunction (𝟙 A.obj)).unit.app
        ((PresheafOfModules.restrictScalars a₀.hom).obj P)).app V x) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).unit.app P).app V x := by
  have h := (PresheafOfModules.sheafificationHomEquiv
    (P := (PresheafOfModules.restrictScalars a₀.hom).obj P)
    (F := (restrictScalars a₀).obj
      ((PresheafOfModules.sheafification (𝟙 B.obj)).obj P)) (𝟙 A.obj)).apply_symm_apply
      ((PresheafOfModules.restrictScalars a₀.hom).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).unit.app P))
  have h' := congrArg ((PresheafOfModules.toPresheaf A.obj).map) h
  rw [PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def] at h'
  have hx := congrArg (fun k ↦ k.app V x) h'
  unfold ScalarHomCancellation.cancellationRestrictSheafifyIso
  change (ScalarHomCancellation.cancellationRestrictSheafifyHom a₀ P).val.app V
    (((PresheafOfModules.sheafificationAdjunction (𝟙 A.obj)).unit.app
      ((PresheafOfModules.restrictScalars a₀.hom).obj P)).app V x) = _
  unfold ScalarHomCancellation.cancellationRestrictSheafifyHom
  exact hx

omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
private theorem localizationRestrictedTensorIso_pure
    (N : scalarModules J R) (V : Cᵒᵖ) (x : N.val.obj V) (b : S.obj.obj V) :
    (localizationRestrictedTensorIso.{c, v, r} a N).hom.val.app V
      (ScalarHomOrdinary.pure R N ((scalarRestriction a).obj (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) V x b) =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).unit.app
          (changeOfRingsPresheaf a N)).app V
            (b ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x) := by
  let B := (scalarRestriction a).obj (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
  let F := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let eP := localizationRestrictedTensorPresheafIso.{c, v, r} a N
  let c := ScalarHomCancellation.cancellationRestrictSheafifyIso
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) (changeOfRingsPresheaf a N)
  have he : (tensorObjIsoSheafification N B).inv ≫
      (localizationRestrictedTensorIso.{c, v, r} a N).hom = F.map eP.hom ≫ c.hom := by
    dsimp only [localizationRestrictedTensorIso, Iso.trans_hom, Functor.mapIso_hom]
    change (tensorObjIsoSheafification N B).inv ≫
      (tensorObjIsoSheafification N B).hom ≫ F.map eP.hom ≫ c.hom = _
    rw [Iso.inv_hom_id_assoc]
  have hn := congrArg (fun k ↦ k.app V (x ⊗ₜ[R.obj.obj V] b))
    (adj.unit.naturality eP.hom)
  have hh := congrArg (fun k ↦ k.val.app V
    ((adj.unit.app (N.val ⊗ B.val)).app V (x ⊗ₜ[R.obj.obj V] b))) he
  change (localizationRestrictedTensorIso.{c, v, r} a N).hom.val.app V
    (ScalarHomOrdinary.pure R N B V x b) = _ at hh
  rw [hh]
  change c.hom.val.app V ((F.map eP.hom).val.app V
    ((adj.unit.app (N.val ⊗ B.val)).app V (x ⊗ₜ[R.obj.obj V] b))) = _
  change (adj.unit.app ((PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map a).hom).obj
        (changeOfRingsPresheaf a N))).app V (eP.hom.app V (x ⊗ₜ[R.obj.obj V] b)) =
      (F.map eP.hom).val.app V
        ((adj.unit.app (N.val ⊗ B.val)).app V (x ⊗ₜ[R.obj.obj V] b)) at hn
  refine (congrArg (c.hom.val.app V) hn.symm).trans ?_
  exact localizationRestrictionSheafification_unit.{c, v, r}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) (changeOfRingsPresheaf a N) V
    (b ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x)

private theorem localizationHom_unit
    (μ : ∀ {A B : Sheaf J CommRingCat.{max c v r}} (b : A ⟶ B),
      ScalarHomTensorComparison M b)
    (α : ScalarInternalHomAdjunction M μ)
    (K L : DerivedCategory (scalarModules J R)) :
    (M.scalar a).adjunction.unit.app
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L)) ≫
      localizationHomRestrictedComparison M a μ α K L =
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom (𝟙 (op K)) ((M.scalar a).adjunction.unit.app L)) := by
  let X := (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L)
  let χ := localizationHomComparison M a (μ a) K L
  have hr := α.representing a X K ((M.scalar a).derived.obj L)
    ((M.scalar a).adjunction.unit.app X ≫ (scalarDerivedRestriction a).map χ)
  change _ = ((M.scalar a).adjunction.unit.app X ≫
    (scalarDerivedRestriction a).map χ) ≫
      (α.iso a).hom.app (op K, (M.scalar a).derived.obj L) at hr
  rw [Category.assoc] at hr
  change _ ≫ (_ ≫ _) = _
  rw [← hr]
  dsimp only [scalarHomBijection, Equiv.trans_apply]
  rw [← (M.scalar a).adjunction.homEquiv_unit]
  dsimp only [Functor.prod_obj, Functor.op_obj, Functor.id_obj]
  change (M.closed R).transpose X K _
    ((M.scalar a).adjunction.homEquiv _ _
      ((μ a).iso.hom.app (X, K) ≫
        ((M.closed S).transpose _ _ _).symm
          (((M.scalar a).adjunction.homEquiv X _).symm
            ((M.scalar a).adjunction.homEquiv X _ χ)) ≫ 𝟙 _)) = _
  rw [Equiv.symm_apply_apply]
  dsimp only [χ, localizationHomComparison]
  rw [Equiv.symm_apply_apply]
  simp only [X, Iso.hom_inv_id_app_assoc, Category.comp_id]
  rw [(M.scalar a).adjunction.homEquiv_unit, (M.scalar a).adjunction.unit_naturality]
  change (M.closed R).transpose X K _
    ((M.closed R).evaluation K L ≫ (M.scalar a).adjunction.unit.app L) = _
  let adj := (M.closed R).adjunction K
  have heval : adj.homEquiv X L (adj.counit.app L) = 𝟙 X := by
    calc
      _ = adj.homEquiv X L ((adj.homEquiv X L).symm (𝟙 X)) := by
        congr 1
        exact (adj.homEquiv_symm_id L).symm
      _ = _ := (adj.homEquiv X L).apply_symm_apply _
  change (adj.homEquiv X _)
    (adj.counit.app L ≫ (M.scalar a).adjunction.unit.app L) = _
  calc
    _ = adj.homEquiv X L (adj.counit.app L) ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom (𝟙 (op K)) ((M.scalar a).adjunction.unit.app L)) :=
      adj.homEquiv_naturality_right _ _
    _ = _ := by rw [heval, Category.id_comp]

private theorem localizationHom_isIso_of_restricted
    (μ : ∀ {A B : Sheaf J CommRingCat.{max c v r}} (b : A ⟶ B),
      ScalarHomTensorComparison M b)
    (α : ScalarInternalHomAdjunction M μ)
    (K L : DerivedCategory (scalarModules J R))
    (h : IsIso (localizationHomRestrictedComparison M a μ α K L)) :
    IsIso (localizationHomComparison M a (μ a) K L) := by
  exact α.conservative a _ ((isIso_comp_right_iff _
    ((α.iso a).hom.app (op K, (M.scalar a).derived.obj L))).mp h)

variable (R : Sheaf J CommRingCat.{max c v r})
  [HasSheafify J CommRingCat.{max c v r}]
  (s : (R.obj ⋙ forget CommRingCat).sections)

omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
private theorem localizationTensor_additive : (scalarLocalization R s).Additive :=
  (scalarLocalization_exact R s).1

attribute [local instance] localizationTensor_additive

private def localizationUnderlyingIso (N : scalarModules J R) :
    (scalarLocalization R s).obj N ≅
      (scalarRestriction (ringedLocalizationRingUnitOfUniverses R s)).obj
        ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).extension.obj N) := by
  let a := ringedLocalizationRingUnitOfUniverses R s
  let _ := SheafOfModules.monoidalCategory R
  let e := Classical.choose (ringedLocalizationRing_moduleComparisonOfUniverses R s)
  exact (ScalarHomOrdinary.tensorIsoSite R N
      (ringedSectionLocalizationOfUniverses R s)).symm ≪≫
    (MonoidalCategory.tensorIso (Iso.refl N) e.symm) ≪≫
      localizationRestrictedTensorIso.{c, v, r} a N ≪≫
        (scalarRestriction a).mapIso (eqToIso ((M.scalar a).extension_obj N)).symm

private theorem localizationUnderlyingIso_unit (N : scalarModules J R) :
    (scalarLocalizationUnit R s).app N ≫ (localizationUnderlyingIso M R s N).hom =
      (M.scalar (ringedLocalizationRingUnitOfUniverses R s)).ordinaryAdjunction.unit.app N := by
  let a := ringedLocalizationRingUnitOfUniverses R s
  let U := scalarRestriction a
  let e := Classical.choose (ringedLocalizationRing_moduleComparisonOfUniverses R s)
  have he := Classical.choose_spec (ringedLocalizationRing_moduleComparisonOfUniverses R s)
  apply (cancel_mono (U.map (eqToHom ((M.scalar a).extension_obj N)))).mp
  dsimp only [localizationUnderlyingIso, U, a, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom,
    eqToIso.hom, eqToIso.inv]
  simp only [Category.assoc, ← Functor.map_comp, eqToHom_trans, eqToHom_refl,
    Functor.map_id, Category.comp_id]
  apply SheafOfModules.hom_ext
  ext V x
  have he₁ : e.hom.val.app V
      (1 : (ringedLocalizationRingOfUniverses R s).obj.obj V) =
      (ringedSectionLocalizationUnitOfUniverses R s).val.app V (1 : R.obj.obj V) := by
    have h := he V (1 : ringedSectionLocalizationCarrierOfUniverses R s V)
    simp only [map_one] at h
    change e.hom.val.app V
      (1 : (ringedLocalizationRingOfUniverses R s).obj.obj V) =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
          (ringedSectionLocalizationPresheafOfUniverses R s)).app V
            ((1 : R.obj.obj V) • (1 : ringedSectionLocalizationCarrierOfUniverses R s V))
    rw [one_smul]
    exact h
  have he₁' : e.inv.val.app V
      ((ringedSectionLocalizationUnitOfUniverses R s).val.app V (1 : R.obj.obj V)) =
      (1 : (ringedLocalizationRingOfUniverses R s).obj.obj V) := by
    rw [← he₁]
    exact congrArg (fun f ↦ f.val.app V
      (1 : (ringedLocalizationRingOfUniverses R s).obj.obj V)) e.hom_inv_id
  have hη := (Classical.choose_spec (existsUnique_scalarLocalizationUnit R s)).1 N V x
  change (((scalarLocalizationUnit R s).app N).val.app V x) =
    siteSheafTensorTmul N (ringedSectionLocalizationOfUniverses R s) V x
      ((ringedSectionLocalizationUnitOfUniverses R s).val.app V (1 : R.obj.obj V)) at hη
  change (localizationRestrictedTensorIso.{c, v, r} a N).hom.val.app V
    (((SheafOfModules.monoidalCategory R).tensorHom (𝟙 N) e.inv).val.app V
      ((ScalarHomOrdinary.tensorIsoSite R N
        (ringedSectionLocalizationOfUniverses R s)).inv.val.app V
          (((scalarLocalizationUnit R s).app N).val.app V x))) =
    (eqToHom ((M.scalar a).extension_obj N)).val.app V
      (((M.scalar a).ordinaryAdjunction.unit.app N).val.app V x)
  rw [hη, ScalarHomOrdinary.tensorIsoSite_inv_pure, ScalarHomOrdinary.pure_map]
  simp only [SheafOfModules.id_val]
  rw [he₁', localizationRestrictedTensorIso_pure.{c, v, r}, (M.scalar a).ordinaryUnit]
  simp only [PresheafOfModules.id_app, ModuleCat.id_apply,
    ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  exact congrArg (fun f ↦ f.app V
    ((1 : (ringedLocalizationRingOfUniverses R s).obj.obj V) ⊗ₜ[R.obj.obj V,
      (a.hom.app V).hom] x))
    (PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRingOfUniverses R s)).obj) (changeOfRingsPresheaf a N))

private theorem localizationUnderlying_scalar_isIso (N : scalarModules J R) :
    IsIso (localizationScalar R s
      ((scalarRestriction (ringedLocalizationRingUnitOfUniverses R s)).obj
        ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).extension.obj N))) := by
  let i := localizationUnderlyingIso M R s N
  have : IsIso (localizationScalar R s ((scalarLocalization R s).obj N)) :=
    LocalizationSequence.colimit_scalar_isIso R s
      (LocalizationSequence.moduleSheafCocone R s N)
      (LocalizationSequence.moduleSheafCoconeIsColimit R s N)
  have h := LocalizationSequence.scalar_naturality R s i.hom
  have hi : IsIso (i.hom ≫ localizationScalar R s
      ((scalarRestriction (ringedLocalizationRingUnitOfUniverses R s)).obj
        ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).extension.obj N))) := by
    rw [← h]
    infer_instance
  exact (isIso_comp_left_iff i.hom _).mp hi

private theorem localizationUnderlyingIso_naturality
    {N N' : scalarModules J R} (f : N ⟶ N') :
    (scalarLocalization R s).map f ≫ (localizationUnderlyingIso M R s N').hom =
      (localizationUnderlyingIso M R s N).hom ≫
        (scalarRestriction (ringedLocalizationRingUnitOfUniverses R s)).map
          ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).extension.map f) := by
  let a := ringedLocalizationRingUnitOfUniverses R s
  have := localizationUnderlying_scalar_isIso M R s N'
  apply LocalizationSequence.colimit_hom_ext_zero R s
    (LocalizationSequence.moduleSheafCocone R s N)
    (LocalizationSequence.moduleSheafCoconeIsColimit R s N)
  rw [LocalizationSequence.moduleSheafCocone_zero]
  calc
    _ = f ≫ (scalarLocalizationUnit R s).app N' ≫
        (localizationUnderlyingIso M R s N').hom := by
      rw [← Category.assoc, ← (scalarLocalizationUnit R s).naturality f,
        Category.assoc, Functor.id_map]
    _ = f ≫ (M.scalar a).ordinaryAdjunction.unit.app N' := by
      rw [localizationUnderlyingIso_unit]
    _ = (M.scalar a).ordinaryAdjunction.unit.app N ≫
        (scalarRestriction a).map ((M.scalar a).extension.map f) :=
      (M.scalar a).ordinaryAdjunction.unit.naturality f
    _ = _ := by rw [← localizationUnderlyingIso_unit M R s N, Category.assoc]

private def localizationUnderlyingNatIso :
    scalarLocalization R s ≅
      (M.scalar (ringedLocalizationRingUnitOfUniverses R s)).extension ⋙
        scalarRestriction (ringedLocalizationRingUnitOfUniverses R s) :=
  NatIso.ofComponents (localizationUnderlyingIso M R s)
    (fun f ↦ localizationUnderlyingIso_naturality M R s f)

omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
private theorem localizationModuleLeg_naturality
    {N N' : scalarModules J R} (f : N ⟶ N') (n : ℕ) :
    f ≫ (LocalizationSequence.moduleSheafCocone R s N').ι.app n =
      (LocalizationSequence.moduleSheafCocone R s N).ι.app n ≫
        (scalarLocalization R s).map f := by
  have : IsIso (localizationScalar R s ((scalarLocalization R s).obj N')) :=
    LocalizationSequence.colimit_scalar_isIso R s
      (LocalizationSequence.moduleSheafCocone R s N')
      (LocalizationSequence.moduleSheafCoconeIsColimit R s N')
  have hstep (T : scalarModules J R) (k : ℕ) :
      localizationScalar R s T ≫
        (LocalizationSequence.moduleSheafCocone R s T).ι.app (k + 1) =
      (LocalizationSequence.moduleSheafCocone R s T).ι.app k := by
    simpa only [Functor.ofSequence_map_homOfLE_succ] using
      (LocalizationSequence.moduleSheafCocone R s T).w (homOfLE (Nat.le_succ k))
  induction n with
  | zero =>
      rw [LocalizationSequence.moduleSheafCocone_zero,
        LocalizationSequence.moduleSheafCocone_zero]
      exact (scalarLocalizationUnit R s).naturality f
  | succ n ih =>
      apply (cancel_mono
        (localizationScalar R s ((scalarLocalization R s).obj N'))).mp
      calc
        _ = f ≫ localizationScalar R s N' ≫
            (LocalizationSequence.moduleSheafCocone R s N').ι.app (n + 1) := by
          rw [Category.assoc,
            ← LocalizationSequence.scalar_naturality, ← Category.assoc]
        _ = f ≫ (LocalizationSequence.moduleSheafCocone R s N').ι.app n := by
          rw [hstep]
        _ = (LocalizationSequence.moduleSheafCocone R s N).ι.app n ≫
            (scalarLocalization R s).map f := ih
        _ = localizationScalar R s N ≫
            (LocalizationSequence.moduleSheafCocone R s N).ι.app (n + 1) ≫
              (scalarLocalization R s).map f := by rw [← hstep N n, Category.assoc]
        _ = _ := by
          rw [LocalizationSequence.scalar_naturality, Category.assoc]

private def localizationComplexScalar
    (P : CochainComplex (scalarModules J R) ℤ) : P ⟶ P where
  f i := localizationScalar R s (P.X i)
  comm' i j _ := LocalizationSequence.scalar_naturality R s (P.d i j)

omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
private theorem localizationComplexScalar_naturality
    {P P' : CochainComplex (scalarModules J R) ℤ} (f : P ⟶ P') :
    localizationComplexScalar.{c, v, r} R s P ≫ f =
      f ≫ localizationComplexScalar.{c, v, r} R s P' := by
  apply HomologicalComplex.hom_ext
  intro i
  exact LocalizationSequence.scalar_naturality R s (f.f i)

private theorem localizationResolution_scalar
    (P : CochainComplex (scalarModules J R) ℤ) :
    DerivedCategory.Q.map ((coefficientHomResolution.{r, c, v} J R).map
        (localizationComplexScalar.{c, v, r} R s P)) =
      DerivedCategory.Q.map (localizationComplexScalar.{c, v, r} R s
        ((coefficientHomResolution.{r, c, v} J R).obj P)) := by
  let : IsGrothendieckAbelian.{max c v r} (scalarModules J R) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r} J R).1
  let I := coefficientHomResolution.{r, c, v} J R
  let η := ringedSiteHomAugmentation.{c, v, r} J R
  have : QuasiIso (η.app P) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} _ P).2
  have : IsIso (DerivedCategory.Q.map (η.app P)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr inferInstance
  apply (cancel_epi (DerivedCategory.Q.map (η.app P))).mp
  have hη := η.naturality (localizationComplexScalar.{c, v, r} R s P)
  change localizationComplexScalar.{c, v, r} R s P ≫ η.app P =
    η.app P ≫ I.map (localizationComplexScalar.{c, v, r} R s P) at hη
  have h : η.app P ≫ I.map (localizationComplexScalar.{c, v, r} R s P) =
      η.app P ≫ localizationComplexScalar.{c, v, r} R s (I.obj P) :=
    hη.symm.trans (localizationComplexScalar_naturality.{c, v, r} R s (η.app P))
  have hQ := congrArg (fun f : P ⟶ I.obj P ↦ DerivedCategory.Q.map f) h
  simpa only [DerivedCategory.Q.map_comp] using hQ

omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
private theorem localizationComplexScalar_f
    (P : CochainComplex (scalarModules J R) ℤ) (i : ℤ) :
    (localizationComplexScalar.{c, v, r} R s P).f i =
      localizationScalar R s (P.X i) := by
  rfl

attribute [local irreducible] localizationComplexScalar

private def localizationComplexLeg
    (P : CochainComplex (scalarModules J R) ℤ) (n : ℕ) :
    P ⟶ ((scalarLocalization R s).mapHomologicalComplex (.up ℤ)).obj P where
  f i := (LocalizationSequence.moduleSheafCocone R s (P.X i)).ι.app n
  comm' i j _ := (localizationModuleLeg_naturality.{c, v, r} R s (P.d i j) n).symm

omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
private theorem localizationComplexLeg_f
    (P : CochainComplex (scalarModules J R) ℤ) (n : ℕ) (i : ℤ) :
    (localizationComplexLeg.{c, v, r} R s P n).f i =
      (LocalizationSequence.moduleSheafCocone R s (P.X i)).ι.app n := by
  rfl

attribute [local irreducible] localizationComplexLeg

omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
private theorem localizationComplexLeg_step
    (P : CochainComplex (scalarModules J R) ℤ) (n : ℕ) :
    localizationComplexScalar.{c, v, r} R s P ≫
        localizationComplexLeg.{c, v, r} R s P (n + 1) =
      localizationComplexLeg.{c, v, r} R s P n := by
  apply HomologicalComplex.hom_ext
  intro i
  simp only [HomologicalComplex.comp_f, localizationComplexLeg_f,
    localizationComplexScalar_f]
  change localizationScalar R s (P.X i) ≫
      (LocalizationSequence.moduleSheafCocone R s (P.X i)).ι.app (n + 1) =
    (LocalizationSequence.moduleSheafCocone R s (P.X i)).ι.app n
  simpa only [Functor.ofSequence_map_homOfLE_succ] using
    (LocalizationSequence.moduleSheafCocone R s (P.X i)).w
      (homOfLE (Nat.le_succ n))

private def localizationComplexCocone
    (P : CochainComplex (scalarModules J R) ℤ) :
    Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ P)
      (fun _ ↦ localizationComplexScalar.{c, v, r} R s P)) :=
  LocalizationHomProof.sequenceCocone P
    (((scalarLocalization R s).mapHomologicalComplex (.up ℤ)).obj P)
    (localizationComplexScalar.{c, v, r} R s P)
    (localizationComplexLeg.{c, v, r} R s P)
    (localizationComplexLeg_step.{c, v, r} R s P)

omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
private theorem localizationComplexCocone_ι_f
    (P : CochainComplex (scalarModules J R) ℤ) (n : ℕ) (i : ℤ) :
    ((localizationComplexCocone.{c, v, r} R s P).ι.app n).f i =
      (LocalizationSequence.moduleSheafCocone R s (P.X i)).ι.app n := by
  change (localizationComplexLeg.{c, v, r} R s P n).f i = _
  exact localizationComplexLeg_f.{c, v, r} R s P n i

private def localizationComplexCoconeIsColimit
    (P : CochainComplex (scalarModules J R) ℤ) :
    IsColimit (localizationComplexCocone.{c, v, r} R s P) := by
  refine HomologicalComplex.isColimitOfEval
    (C := scalarModules J R) (c := ComplexShape.up ℤ)
    (Functor.ofSequence (X := fun _ : ℕ ↦ P)
      (fun _ ↦ localizationComplexScalar.{c, v, r} R s P))
    (localizationComplexCocone.{c, v, r} R s P) (fun i ↦ ?_)
  let V := HomologicalComplex.eval (scalarModules J R) (.up ℤ) i
  let T := Functor.ofSequence (X := fun _ : ℕ ↦ P)
    (fun _ ↦ localizationComplexScalar.{c, v, r} R s P)
  let D := Functor.ofSequence (X := fun _ : ℕ ↦ P.X i)
    (fun _ ↦ localizationScalar R s (P.X i))
  let τ : D ⟶ T ⋙ V := NatTrans.ofSequence (fun _ ↦ 𝟙 _) (by
    intro n
    simp only [D, T, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ]
    change localizationScalar R s (P.X i) ≫ 𝟙 _ =
      𝟙 _ ≫ (localizationComplexScalar.{c, v, r} R s P).f i
    rw [localizationComplexScalar_f, Category.comp_id, Category.id_comp])
  let e : D ≅ T ⋙ V := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro n m f
    exact τ.naturality f)
  apply (IsColimit.precomposeHomEquiv e
    (V.mapCocone (localizationComplexCocone.{c, v, r} R s P))).toFun
  apply IsColimit.ofIsoColimit (LocalizationSequence.moduleSheafCoconeIsColimit R s (P.X i))
  refine Cocone.ext (Iso.refl ((scalarLocalization R s).obj (P.X i))) ?_
  intro n
  change (LocalizationSequence.moduleSheafCocone R s (P.X i)).ι.app n ≫ 𝟙 _ =
    𝟙 _ ≫ (localizationComplexLeg.{c, v, r} R s P n).f i
  rw [localizationComplexLeg_f, Category.comp_id, Category.id_comp]

omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
private theorem localizationHomObj_scalar (N N' : scalarModules J R) :
    SheafOfModules.homObjMap (𝟙 N) (localizationScalar R s N') =
      localizationScalar R s (SheafOfModules.homObj (R := R) N N') := by
  apply SheafOfModules.hom_ext
  ext U φ : 3
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext m
  change (s.val (op W.unop.left) : R.obj.obj (op W.unop.left)) • (φ.app W m) =
    (((s.val U : R.obj.obj U) • φ).app W) m
  rw [PresheafOfModules.smul_app]
  erw [ModuleCat.comp_apply, PresheafOfModules.sectionsSMul_app_apply,
    PresheafOfModules.overSections_coe_apply]
  change (s.val (op W.unop.left) : R.obj.obj (op W.unop.left)) • (φ.app W m) =
    R.obj.map W.unop.hom.op (s.val U) • (φ.app W m)
  have hs := s.property W.unop.hom.op
  change R.obj.map W.unop.hom.op (s.val U) = s.val (op W.unop.left) at hs
  exact congrArg (fun a : R.obj.obj (op W.unop.left) ↦ a • (φ.app W m)) hs.symm

omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
private theorem localizationHomComplex_scalar
    (P I : CochainComplex (scalarModules J R) ℤ) :
    ((homComplexFunctor (R := R)).obj (op P)).map
        (localizationComplexScalar.{c, v, r} R s I) =
      localizationComplexScalar.{c, v, r} R s (homComplex (R := R) P I) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply homComplex_hom_ext
  intro p q hpq
  rw [homComplexFunctor_obj_map_f_π]
  simp only [localizationComplexScalar_f]
  change homComplexπ P I n p q hpq ≫
      SheafOfModules.homObjMap (𝟙 (P.X p)) (localizationScalar R s (I.X q)) =
    localizationScalar R s ((homComplex (R := R) P I).X n) ≫
      homComplexπ P I n p q hpq
  rw [localizationHomObj_scalar.{c, v, r} R s (P.X p) (I.X q),
    LocalizationSequence.scalar_naturality R s (homComplexπ P I n p q hpq)]


omit [HasSheafify J CommRingCat.{max c v r}] in
private theorem localizationHom_map_eq_of_Q_eq
    (P I I' : CochainComplex (scalarModules J R) ℤ) [I'.IsKInjective]
    (f g : I ⟶ I') (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    DerivedCategory.Q.map (((homComplexFunctor (R := R)).obj (op P)).map f) =
      DerivedCategory.Q.map (((homComplexFunctor (R := R)).obj (op P)).map g) := by
  let t := RingedHomUniverses.ordinaryComparison.{c, v, r, w} J R
  have : IsIso (t.app (op P, I')) := by
    change IsIso ((RingedHomUniverses.ordinaryComparison.{c, v, r, w} J R).app (op P, I'))
    rw [RingedHomUniverses.ordinaryComparison_app]
    exact RingedHomUniverses.comparison_isIso_of_kInjective.{c, v, r, w} J R P I'
  apply (cancel_mono (t.app (op P, I'))).mp
  have hf := t.naturality (Prod.mkHom (𝟙 (op P)) f)
  have hg := t.naturality (Prod.mkHom (𝟙 (op P)) g)
  dsimp only [Functor.comp_map, RingedHomUniverses.ordinaryBifunctor,
    Functor.uncurry_obj_map, Functor.prod_map, Functor.op_map] at hf hg
  simp only [Functor.map_id, NatTrans.id_app, Category.id_comp, unop_id, op_id] at hf hg
  change DerivedCategory.Q.map (((homComplexFunctor (R := R)).obj (op P)).map f) ≫
      t.app (op P, I') = t.app (op P, I) ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P))) (DerivedCategory.Q.map f)) at hf
  change DerivedCategory.Q.map (((homComplexFunctor (R := R)).obj (op P)).map g) ≫
      t.app (op P, I') = t.app (op P, I) ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P))) (DerivedCategory.Q.map g)) at hg
  rw [hf, hg, h]

private theorem localizationHomComplex_transition
    (K : DerivedCategory (scalarModules J R))
    (P : CochainComplex (scalarModules J R) ℤ) :
    DerivedCategory.Q.map ((localizationHomComplex.{c, v, r, w} J R K).map
        (localizationComplexScalar.{c, v, r} R s P)) =
      DerivedCategory.Q.map (localizationComplexScalar.{c, v, r} R s
        ((localizationHomComplex.{c, v, r, w} J R K).obj P)) := by
  let : IsGrothendieckAbelian.{max c v r} (scalarModules J R) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r} J R).1
  have : ((coefficientHomResolution.{r, c, v} J R).obj P).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v r} _ P
  change DerivedCategory.Q.map (((homComplexFunctor (R := R)).obj
      (op (DerivedCategory.Q.objPreimage K))).map
        ((coefficientHomResolution.{r, c, v} J R).map
          (localizationComplexScalar.{c, v, r} R s P))) = _
  rw [localizationHom_map_eq_of_Q_eq.{c, v, r, w} R (DerivedCategory.Q.objPreimage K) _ _ _ _
    (localizationResolution_scalar.{c, v, r, w} R s P), localizationHomComplex_scalar]
  rfl

private def localizationHomResolutionIso
    (K : DerivedCategory (scalarModules J R))
    (P : CochainComplex (scalarModules J R) ℤ) :
    DerivedCategory.Q.obj ((localizationHomComplex.{c, v, r, w} J R K).obj P) ≅
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
        (op K, DerivedCategory.Q.obj P) :=
  (coefficientHomResolutionIso.{r, c, v, w} J R
    (DerivedCategory.Q.objPreimage K) P).symm ≪≫
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).mapIso
        ((DerivedCategory.Q.objObjPreimageIso K).symm.op.prod (Iso.refl _))

omit [HasSheafify J CommRingCat.{max c v r}] in
private theorem localizationHomResolutionIso_naturality
    (K : DerivedCategory (scalarModules J R))
    {P P' : CochainComplex (scalarModules J R) ℤ} (f : P ⟶ P') :
    DerivedCategory.Q.map ((localizationHomComplex.{c, v, r, w} J R K).map f) ≫
        (localizationHomResolutionIso.{c, v, r, w} R K P').hom =
      (localizationHomResolutionIso.{c, v, r, w} R K P).hom ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom (𝟙 (op K)) (DerivedCategory.Q.map f)) := by
  let H := derivedInternalHomOfUniverses.{c, v, r, w} J R
  have hn := (RingedHomUniverses.resolutionComparison.{c, v, r, w} J R).inv.naturality
    (Prod.mkHom (𝟙 (op (DerivedCategory.Q.objPreimage K))) f)
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.id_map, Functor.id_obj, Functor.op_map,
    RingedHomUniverses.ordinaryBifunctor, Functor.uncurry_obj_map,
    RingedHomUniverses.resolutionComparison, NatIso.ofComponents_inv_app] at hn
  simp only [Functor.map_id, NatTrans.id_app, Category.id_comp, unop_id, op_id] at hn
  change DerivedCategory.Q.map ((localizationHomComplex.{c, v, r, w} J R K).map f) ≫
      (coefficientHomResolutionIso.{r, c, v, w} J R
        (DerivedCategory.Q.objPreimage K) P').inv =
    (coefficientHomResolutionIso.{r, c, v, w} J R
      (DerivedCategory.Q.objPreimage K) P).inv ≫ H.map
        (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage K))))
          (DerivedCategory.Q.map f)) at hn
  dsimp only [localizationHomResolutionIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  apply congrArg (fun z ↦
    (coefficientHomResolutionIso.{r, c, v, w} J R
      (DerivedCategory.Q.objPreimage K) P).inv ≫ z)
  rw [← H.map_comp, ← H.map_comp]
  apply congrArg (fun f :
      (op (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage K)), DerivedCategory.Q.obj P) ⟶
        (op K, DerivedCategory.Q.obj P') ↦ H.map f)
  ext <;> simp


-- The resolution and scalar-action lemmas above supply the interface below.
attribute [local irreducible] localizationHomComplex

private theorem localizationHom_continuity_telescope
    (K : DerivedCategory (scalarModules J R))
    (hK : HasLocalizationHomContinuity.{c, v, r, w} J R K)
    (P : CochainComplex (scalarModules J R) ℤ) (b : ℤ) [P.IsStrictlyGE b] :
    let H := localizationHomComplex.{c, v, r, w} J R K
    let D := Functor.ofSequence (X := fun _ : ℕ ↦ P)
      (fun _ ↦ localizationComplexScalar.{c, v, r} R s P)
    ∃ β : DerivedCategory.Q.{w}.obj (localizationComplexCocone.{c, v, r} R s (H.obj P)).pt ≅
        DerivedCategory.Q.{w}.obj (H.obj (colimit D)),
      ∀ n : ℕ,
        DerivedCategory.Q.{w}.map ((localizationComplexCocone.{c, v, r} R s (H.obj P)).ι.app n) ≫
          β.hom = DerivedCategory.Q.{w}.map (H.map (colimit.ι D n)) := by
  let A := scalarModules J R
  let : IsGrothendieckAbelian.{max c v r} A :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r} J R).1
  have : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink.{0, 0, max c v r, max c v r} A
  have : AB5OfSize.{0, 0} A := AB5OfSize_shrink.{0, 0, max c v r, max c v r} A
  let H := localizationHomComplex.{c, v, r, w} J R K
  let D := Functor.ofSequence (X := fun _ : ℕ ↦ P)
    (fun _ ↦ localizationComplexScalar.{c, v, r} R s P)
  let T := Functor.ofSequence (X := fun _ : ℕ ↦ H.obj P)
    (fun _ ↦ localizationComplexScalar.{c, v, r} R s (H.obj P))
  let τ : T ⋙ DerivedCategory.Q.{w} ⟶ (D ⋙ H) ⋙ DerivedCategory.Q.{w} :=
    NatTrans.ofSequence
      (fun _ ↦ 𝟙 (DerivedCategory.Q.{w}.obj (H.obj P))) (by
      intro n
      simp only [T, D, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ]
      change DerivedCategory.Q.{w}.map
          (localizationComplexScalar.{c, v, r} R s (H.obj P)) ≫ 𝟙 _ =
        𝟙 _ ≫ DerivedCategory.Q.{w}.map
          (H.map (localizationComplexScalar.{c, v, r} R s P))
      exact LocalizationHomProof.id_square
        (localizationHomComplex_transition.{c, v, r, w} R s K P).symm)
  let e : T ⋙ DerivedCategory.Q.{w} ≅ (D ⋙ H) ⋙ DerivedCategory.Q.{w} :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro n m f
      exact τ.naturality f)
  obtain ⟨β, hβ⟩ := LocalizationHomProof.sequential_colimit_comparison (A := A)
    T (D ⋙ H) (localizationComplexCocone.{c, v, r} R s (H.obj P))
      (localizationComplexCoconeIsColimit.{c, v, r} R s (H.obj P))
      (colimit.cocone (D ⋙ H)) (colimit.isColimit (D ⋙ H)) e
  have hcont : IsIso (localizationHomContinuityMap.{c, v, r, w} J R K D) :=
    hK D ⟨b, fun _ ↦ by change P.IsStrictlyGE b; infer_instance⟩
  refine ⟨β ≪≫ asIso (localizationHomContinuityMap.{c, v, r, w} J R K D), ?_⟩
  intro n
  have hleg : DerivedCategory.Q.{w}.map
      ((localizationComplexCocone.{c, v, r} R s (H.obj P)).ι.app n) ≫ β.hom =
      DerivedCategory.Q.{w}.map (colimit.ι (D ⋙ H) n) := by
    have hn := hβ n
    change DerivedCategory.Q.{w}.map
        ((localizationComplexCocone.{c, v, r} R s (H.obj P)).ι.app n) ≫ β.hom =
      𝟙 (DerivedCategory.Q.{w}.obj (H.obj P)) ≫
        DerivedCategory.Q.{w}.map (colimit.ι (D ⋙ H) n) at hn
    exact hn.trans (Category.id_comp _)
  change DerivedCategory.Q.{w}.map _ ≫
    (β.hom ≫ DerivedCategory.Q.{w}.map (colimit.post D H)) = _
  rw [← Category.assoc, hleg, ← DerivedCategory.Q.{w}.map_comp, colimit.ι_post]

omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
private theorem localizationRestriction_full :
    (scalarRestriction (ringedLocalizationRingUnitOfUniverses R s)).Full where
  map_surjective {N N'} f :=
    (localization_restrictScalars_fullyFaithful R s N N' f).exists

omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
private theorem localizationRestriction_faithful :
    (scalarRestriction (ringedLocalizationRingUnitOfUniverses R s)).Faithful where
  map_injective {N N'} {f g} h := by
    obtain ⟨k, _, hk⟩ := localization_restrictScalars_fullyFaithful R s N N'
      ((scalarRestriction (ringedLocalizationRingUnitOfUniverses R s)).map f)
    exact (hk f rfl).trans (hk g h.symm).symm

private theorem localizationExtension_exact :
    PreservesFiniteLimits
        (M.scalar (ringedLocalizationRingUnitOfUniverses R s)).extension ∧
      PreservesFiniteColimits
        (M.scalar (ringedLocalizationRingUnitOfUniverses R s)).extension := by
  let a := ringedLocalizationRingUnitOfUniverses R s
  let E := (M.scalar a).extension
  let U := scalarRestriction a
  have : U.Full := localizationRestriction_full.{c, v, r} R s
  have : U.Faithful := localizationRestriction_faithful.{c, v, r} R s
  have : PreservesFiniteLimits (scalarLocalization R s) :=
    (scalarLocalization_exact R s).2.1
  have : PreservesFiniteColimits (scalarLocalization R s) :=
    (scalarLocalization_exact R s).2.2
  have : PreservesFiniteLimits (E ⋙ U) :=
    preservesFiniteLimits_of_natIso (localizationUnderlyingNatIso M R s)
  have : PreservesFiniteColimits (E ⋙ U) :=
    preservesFiniteColimits_of_natIso (localizationUnderlyingNatIso M R s)
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves E U,
    preservesFiniteColimits_of_reflects_of_preserves E U⟩


private def localizationExtensionComparison :
    let a := ringedLocalizationRingUnitOfUniverses R s
    let E := (M.scalar a).extension
    letI := (M.scalar a).extension_additive
    letI := (localizationExtension_exact M R s).1
    letI := (localizationExtension_exact M R s).2
    (M.scalar a).derived ≅ E.mapDerivedCategory := by
  let a := ringedLocalizationRingUnitOfUniverses R s
  let E := (M.scalar a).extension
  have : E.Additive := (M.scalar a).extension_additive
  have : PreservesFiniteLimits E := (localizationExtension_exact M R s).1
  have : PreservesFiniteColimits E := (localizationExtension_exact M R s).2
  exact Adjunction.leftAdjointUniq (M.scalar a).adjunction
    (LocalizationHomProof.exact_adjunction E (scalarRestriction a)
      (M.scalar a).ordinaryAdjunction)

private def localizationUnderlyingComplexIso
    (P : CochainComplex (scalarModules J R) ℤ) :
    letI := (M.scalar (ringedLocalizationRingUnitOfUniverses R s)).extension_additive
    (localizationComplexCocone.{c, v, r} R s P).pt ≅
      ((scalarRestriction (ringedLocalizationRingUnitOfUniverses R s)).mapHomologicalComplex
        (.up ℤ)).obj
          (((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).extension.mapHomologicalComplex
            (.up ℤ)).obj P) := by
  let a := ringedLocalizationRingUnitOfUniverses R s
  have : (M.scalar a).extension.Additive := (M.scalar a).extension_additive
  exact (NatIso.mapHomologicalComplex (localizationUnderlyingNatIso M R s) (.up ℤ)).app P ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl
      ((M.scalar a).extension ⋙ scalarRestriction a)) (.up ℤ)).symm.app P

private theorem localizationUnderlyingComplexIso_unit
    (P : CochainComplex (scalarModules J R) ℤ) :
    letI := (M.scalar (ringedLocalizationRingUnitOfUniverses R s)).extension_additive
    (localizationComplexCocone.{c, v, r} R s P).ι.app 0 ≫
        (localizationUnderlyingComplexIso M R s P).hom =
      (Adjunction.mapHomologicalComplex (.up ℤ)
        (M.scalar (ringedLocalizationRingUnitOfUniverses R s)).ordinaryAdjunction).unit.app P := by
  have := (M.scalar (ringedLocalizationRingUnitOfUniverses R s)).extension_additive
  apply HomologicalComplex.hom_ext
  intro i
  rw [HomologicalComplex.comp_f, localizationComplexCocone_ι_f.{c, v, r} R s P 0 i]
  change (LocalizationSequence.moduleSheafCocone R s (P.X i)).ι.app 0 ≫
      (localizationUnderlyingIso M R s (P.X i)).hom = _
  rw [LocalizationSequence.moduleSheafCocone_zero]
  exact localizationUnderlyingIso_unit M R s (P.X i)

private def localizationUnderlyingDerivedIso
    (P : CochainComplex (scalarModules J R) ℤ) :
    DerivedCategory.Q.obj (localizationComplexCocone.{c, v, r} R s P).pt ≅
      (scalarDerivedRestriction (ringedLocalizationRingUnitOfUniverses R s)).obj
        ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).derived.obj
          (DerivedCategory.Q.obj P)) := by
  let a := ringedLocalizationRingUnitOfUniverses R s
  let E := (M.scalar a).extension
  let U := scalarRestriction a
  have : E.Additive := (M.scalar a).extension_additive
  have : PreservesFiniteLimits E := (localizationExtension_exact M R s).1
  have : PreservesFiniteColimits E := (localizationExtension_exact M R s).2
  exact DerivedCategory.Q.mapIso (localizationUnderlyingComplexIso M R s P) ≪≫
    (U.mapDerivedCategoryFactors.app ((E.mapHomologicalComplex (.up ℤ)).obj P)).symm ≪≫
    U.mapDerivedCategory.mapIso (E.mapDerivedCategoryFactors.app P).symm ≪≫
    U.mapDerivedCategory.mapIso ((localizationExtensionComparison M R s).app
      (DerivedCategory.Q.obj P)).symm

private theorem localizationUnderlyingDerivedIso_unit
    (P : CochainComplex (scalarModules J R) ℤ) :
    DerivedCategory.Q.map ((localizationComplexCocone.{c, v, r} R s P).ι.app 0) ≫
        (localizationUnderlyingDerivedIso M R s P).hom =
      (M.scalar (ringedLocalizationRingUnitOfUniverses R s)).adjunction.unit.app
        (DerivedCategory.Q.obj P) := by
  let a := ringedLocalizationRingUnitOfUniverses R s
  let E := (M.scalar a).extension
  let U := scalarRestriction a
  have : E.Additive := (M.scalar a).extension_additive
  have : PreservesFiniteLimits E := (localizationExtension_exact M R s).1
  have : PreservesFiniteColimits E := (localizationExtension_exact M R s).2
  let e := localizationExtensionComparison M R s
  apply (cancel_mono (U.mapDerivedCategory.map (e.hom.app
    (DerivedCategory.Q.obj P)))).mp
  apply (cancel_mono (U.mapDerivedCategory.map
    (E.mapDerivedCategoryFactors.hom.app P))).mp
  apply (cancel_mono (U.mapDerivedCategoryFactors.hom.app
    ((E.mapHomologicalComplex (.up ℤ)).obj P))).mp
  have hunit := Adjunction.unit_leftAdjointUniq_hom_app (M.scalar a).adjunction
    (LocalizationHomProof.exact_adjunction E U (M.scalar a).ordinaryAdjunction)
    (DerivedCategory.Q.obj P)
  change (M.scalar a).adjunction.unit.app (DerivedCategory.Q.obj P) ≫
      U.mapDerivedCategory.map (e.hom.app (DerivedCategory.Q.obj P)) =
      (LocalizationHomProof.exact_adjunction E U (M.scalar a).ordinaryAdjunction).unit.app
        (DerivedCategory.Q.obj P) at hunit
  have hR : (M.scalar a).adjunction.unit.app (DerivedCategory.Q.obj P) ≫
      U.mapDerivedCategory.map (e.hom.app (DerivedCategory.Q.obj P)) ≫
      U.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app P) ≫
      U.mapDerivedCategoryFactors.hom.app
        ((E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        (((M.scalar a).ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).unit.app P) := by
    rw [← Category.assoc, hunit]
    exact LocalizationHomProof.exact_adjunction_unit E U
      (M.scalar a).ordinaryAdjunction P
  simp only [Category.assoc]
  rw [hR]
  dsimp only [localizationUnderlyingDerivedIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Functor.mapIso_hom]
  change DerivedCategory.Q.map ((localizationComplexCocone.{c, v, r} R s P).ι.app 0) ≫
      (DerivedCategory.Q.map (localizationUnderlyingComplexIso M R s P).hom ≫
        U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        U.mapDerivedCategory.map (E.mapDerivedCategoryFactors.inv.app P) ≫
        U.mapDerivedCategory.map (e.inv.app (DerivedCategory.Q.obj P))) ≫
      U.mapDerivedCategory.map (e.hom.app (DerivedCategory.Q.obj P)) ≫
      U.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app P) ≫
      U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) = _
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app]
  erw [Functor.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  exact congrArg (fun f : P ⟶ _ ↦ DerivedCategory.Q.map f)
    (localizationUnderlyingComplexIso_unit M R s P)

include M in
private theorem localizationDerivedRestriction_full :
    (scalarDerivedRestriction (ringedLocalizationRingUnitOfUniverses R s)).Full := by
  let a := ringedLocalizationRingUnitOfUniverses R s
  let E := (M.scalar a).extension
  let U := scalarRestriction a
  have : U.Full := localizationRestriction_full.{c, v, r} R s
  have : U.Faithful := localizationRestriction_faithful.{c, v, r} R s
  have : E.Additive := (M.scalar a).extension_additive
  have : PreservesFiniteLimits E := (localizationExtension_exact M R s).1
  have : PreservesFiniteColimits E := (localizationExtension_exact M R s).2
  have : U.PreservesKInjectiveComplexes :=
    (M.scalar a).ordinaryAdjunction.preservesKInjectiveComplexes
  have : IsGrothendieckAbelian.{max c v r}
      (scalarModules J (ringedLocalizationRingOfUniverses R s)) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r} J
      (ringedLocalizationRingOfUniverses R s)).1
  let hff : U.rightDerivedFunctor.FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful _
  exact (hff.ofIso U.rightDerivedFunctorIsoMapDerivedCategory).full

private theorem localizationHom_unique
    (μ : ∀ {A B : Sheaf J CommRingCat.{max c v r}} (b : A ⟶ B),
      ScalarHomTensorComparison M b)
    (α : ScalarInternalHomAdjunction M μ)
    (K L : DerivedCategory (scalarModules J R))
    (b : (scalarDerivedRestriction (ringedLocalizationRingUnitOfUniverses R s)).obj
        ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).derived.obj
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L))) ⟶
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
        (op K, (scalarDerivedRestriction (ringedLocalizationRingUnitOfUniverses R s)).obj
          ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).derived.obj L)))
    (hb : (M.scalar (ringedLocalizationRingUnitOfUniverses R s)).adjunction.unit.app
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L)) ≫ b =
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom (𝟙 (op K))
          ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).adjunction.unit.app L))) :
    b = localizationHomRestrictedComparison M (ringedLocalizationRingUnitOfUniverses R s)
      μ α K L := by
  let a := ringedLocalizationRingUnitOfUniverses R s
  have : (scalarDerivedRestriction a).Full := localizationDerivedRestriction_full M R s
  apply (cancel_mono ((α.iso a).inv.app (op K, (M.scalar a).derived.obj L))).mp
  apply LocalizationHomProof.unit_precomp_injective (M.scalar a).adjunction
    ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L))
    ((derivedInternalHomOfUniverses.{c, v, r, w} J
      (ringedLocalizationRingOfUniverses R s)).obj
      (op ((M.scalar a).derived.obj K), (M.scalar a).derived.obj L))
  simpa only [Category.assoc] using congrArg
    (fun z ↦ z ≫ (α.iso a).inv.app (op K, (M.scalar a).derived.obj L))
    (hb.trans (localizationHom_unit M a μ α K L).symm)

private theorem localizationHom_iso_on_Q
    (K : DerivedCategory (scalarModules J R))
    (hK : HasLocalizationHomContinuity.{c, v, r, w} J R K)
    (P : CochainComplex (scalarModules J R) ℤ) (b : ℤ) [P.IsStrictlyGE b] :
    let a := ringedLocalizationRingUnitOfUniverses R s
    let H := derivedInternalHomOfUniverses.{c, v, r, w} J R
    let UF := (M.scalar a).derived ⋙ scalarDerivedRestriction a
    ∃ β : UF.obj (H.obj (op K, DerivedCategory.Q.obj P)) ≅
        H.obj (op K, UF.obj (DerivedCategory.Q.obj P)),
      (M.scalar a).adjunction.unit.app (H.obj (op K, DerivedCategory.Q.obj P)) ≫
        β.hom = H.map (Prod.mkHom (𝟙 (op K))
          ((M.scalar a).adjunction.unit.app (DerivedCategory.Q.obj P))) := by
  let a := ringedLocalizationRingUnitOfUniverses R s
  let H := derivedInternalHomOfUniverses.{c, v, r, w} J R
  let UF := (M.scalar a).derived ⋙ scalarDerivedRestriction a
  let Γ := localizationHomComplex.{c, v, r, w} J R K
  let D := Functor.ofSequence (X := fun _ : ℕ ↦ P)
    (fun _ ↦ localizationComplexScalar.{c, v, r} R s P)
  let : IsGrothendieckAbelian.{max c v r} (scalarModules J R) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r} J R).1
  have : HasColimitsOfSize.{0, 0} (scalarModules J R) :=
    hasColimitsOfSizeShrink.{0, 0, max c v r, max c v r} (scalarModules J R)
  let eC : colimit D ≅ (localizationComplexCocone.{c, v, r} R s P).pt :=
    colimit.isoColimitCocone
      ⟨localizationComplexCocone.{c, v, r} R s P,
        localizationComplexCoconeIsColimit.{c, v, r} R s P⟩
  let eD : DerivedCategory.Q.obj (colimit D) ≅ UF.obj (DerivedCategory.Q.obj P) :=
    DerivedCategory.Q.mapIso eC ≪≫ localizationUnderlyingDerivedIso M R s P
  have hD : DerivedCategory.Q.map (colimit.ι D 0) ≫ eD.hom =
      (M.scalar a).adjunction.unit.app (DerivedCategory.Q.obj P) := by
    dsimp only [eD, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← DerivedCategory.Q.map_comp]
    rw [show colimit.ι D 0 ≫ eC.hom =
        (localizationComplexCocone.{c, v, r} R s P).ι.app 0 from
      colimit.isoColimitCocone_ι_hom _ _]
    exact localizationUnderlyingDerivedIso_unit M R s P
  obtain ⟨t, ht⟩ := localizationHom_continuity_telescope.{c, v, r, w} R s K hK P b
  let eH := localizationHomResolutionIso.{c, v, r, w} R K P
  let eT := localizationUnderlyingDerivedIso M R s (Γ.obj P)
  let β := (UF.mapIso eH).symm ≪≫ eT.symm ≪≫ t ≪≫
    localizationHomResolutionIso.{c, v, r, w} R K (colimit D) ≪≫
      H.mapIso ((Iso.refl (op K)).prod eD)
  refine ⟨β, ?_⟩
  have hη := (M.scalar a).adjunction.unit.naturality eH.inv
  dsimp only [Functor.id_map, Functor.comp_map] at hη
  change eH.inv ≫ (M.scalar a).adjunction.unit.app
      (DerivedCategory.Q.obj (Γ.obj P)) =
    (M.scalar a).adjunction.unit.app (H.obj (op K, DerivedCategory.Q.obj P)) ≫
      UF.map eH.inv at hη
  have hT : (M.scalar a).adjunction.unit.app (DerivedCategory.Q.obj (Γ.obj P)) ≫
      eT.inv = DerivedCategory.Q.map
        ((localizationComplexCocone.{c, v, r} R s (Γ.obj P)).ι.app 0) := by
    rw [← localizationUnderlyingDerivedIso_unit M R s (Γ.obj P)]
    simp only [eT, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  dsimp only [β, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.comp_map]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← Category.assoc, ← hη]
  simp only [Category.assoc]
  rw [← Category.assoc ((M.scalar a).adjunction.unit.app
    (DerivedCategory.Q.obj (Γ.obj P))) eT.inv, hT]
  rw [← Category.assoc (DerivedCategory.Q.map
    ((localizationComplexCocone.{c, v, r} R s (Γ.obj P)).ι.app 0)) t.hom, ht 0]
  rw [← Category.assoc (DerivedCategory.Q.map (Γ.map (colimit.ι D 0)))
    (localizationHomResolutionIso.{c, v, r, w} R K (colimit D)).hom,
    localizationHomResolutionIso_naturality.{c, v, r, w} R K (colimit.ι D 0)]
  simp only [Category.assoc]
  change eH.inv ≫ eH.hom ≫
      H.map (Prod.mkHom (𝟙 (op K)) (DerivedCategory.Q.map (colimit.ι D 0))) ≫
        H.map ((Iso.refl (op K)).prod eD).hom = _
  rw [Iso.inv_hom_id_assoc, ← H.map_comp]
  apply congrArg (fun f : (op K, DerivedCategory.Q.obj P) ⟶
      (op K, UF.obj (DerivedCategory.Q.obj P)) ↦ H.map f)
  apply Prod.hom_ext
  · change 𝟙 (op K) ≫ 𝟙 (op K) = 𝟙 (op K)
    exact Category.id_comp _
  · change DerivedCategory.Q.map (colimit.ι D 0) ≫ eD.hom = _
    exact hD

/-- Under precisely the displayed sequential continuity assumption, scalar localization
commutes with ambient derived internal Hom for a bounded-below second input.
The restricted isomorphism is characterized by its zeroth telescope leg (the scalar
unit); uniqueness records the identification of the actual derived map, rather than
only a selection of an isomorphism between its endpoints. Naturality is in both inputs.
All auxiliary presentations are the already existing normalized models, which exist
by scalarInternalHomAdjunction_exists and impose no extra mathematical hypothesis.

Source: Bhatt--Scholze 6.8.12 and 6.8.14(2), pp. 61--62, conditional internal-sheaf
argument; Stacks 03CY, 03DB, 03ET, 06YY, 07A6 and 08J9
(blueprint: lem-sfb-internal-hom-localization-comparison).

Proof:
1. Mathlib supplies a strictly bounded-below complex P and L ≅ Q(P). The scalar
sequence on P has the common termwise lower bound required by continuity.
2. Identify restricted ordinary extension with the existing exact tensor
localization. Fully faithful restriction reflects finite limits and colimits,
so extension is exact. Localize its termwise ordinary adjunction through Q. Uniqueness
of left adjoints identifies its derived extension with the recorded one, compatibly
with units by the explicit formula for the unit of a localized adjunction.
3. Ordinary restriction is fully faithful. Exact extension implies that restriction
preserves K-injectives, so its derived functor is full. Fullness and the adjunction
hom equivalence make precomposition with the unit injective on maps into U(N).
4. Assemble the normalized scalar module colimit cocones degreewise. They are
colimits for arbitrary complexes. Identify their tensor-localization targets with
ordinary restricted extension using the localized ring/module comparison and
restriction of sheafification. Check the zeroth leg and pass to derived categories
using the normalized adjunction comparison of step 2.
5. Naturality of the K-injective augmentation gives Q(I(s)) = Q(s_I). The ordinary
Hom comparison is natural and invertible at K-injective targets, so it gives the
corresponding equality after applying the Hom complex and Q. The scalar Hom tower
and the Hom of the scalar input tower are therefore isomorphic after Q. Their
colimits fit into distinguished telescope triangles. Compare the coproduct terms
and complete the square to a morphism of triangles; its third map is an isomorphism
and preserves every cocone leg. Compose with the assumed continuity comparison.
The resolution comparison and step 4 identify this with an isomorphism beta whose
composite with the unit is Hom(K, eta_L).
6. Evaluation normalization of the scalar-Hom adjunction shows that the actual
restricted comparison satisfies the same unit equation. The injectivity of step 3
identifies it with beta.
7. Conservativity of restriction gives invertibility of the comparison over S.
Naturality follows by transposing the naturality square for extended evaluation;
it transports invertibility from Q(P) to L and gives the final two-variable square. -/
theorem internalHom_localization_comparison
    (μ : ∀ {A B : Sheaf J CommRingCat.{max c v r}} (b : A ⟶ B),
      ScalarHomTensorComparison M b)
    (α : ScalarInternalHomAdjunction M μ)
    (K L : DerivedCategory (scalarModules J R))
    (hK : HasLocalizationHomContinuity.{c, v, r, w} J R K)
    (hL : ∃ n : ℤ, L.IsGE n) :
    IsIso (localizationHomComparison.{c, v, r, w} M (ringedLocalizationRingUnitOfUniverses R s)
      (μ (ringedLocalizationRingUnitOfUniverses R s)) K L) ∧
    IsIso (localizationHomRestrictedComparison.{c, v, r, w} M
      (ringedLocalizationRingUnitOfUniverses R s) μ α K L) ∧
    (M.scalar (ringedLocalizationRingUnitOfUniverses R s)).adjunction.unit.app
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L)) ≫
      localizationHomRestrictedComparison.{c, v, r, w} M
          (ringedLocalizationRingUnitOfUniverses R s) μ α K L =
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom (𝟙 (op K))
            ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).adjunction.unit.app L)) ∧
    (∀ b :
        (scalarDerivedRestriction (ringedLocalizationRingUnitOfUniverses R s)).obj
          ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).derived.obj
            ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L))) ⟶
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
          (op K, (scalarDerivedRestriction (ringedLocalizationRingUnitOfUniverses R s)).obj
            ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).derived.obj L)),
      (M.scalar (ringedLocalizationRingUnitOfUniverses R s)).adjunction.unit.app
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L)) ≫ b =
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom (𝟙 (op K))
            ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).adjunction.unit.app L)) →
      b = localizationHomRestrictedComparison.{c, v, r, w} M
        (ringedLocalizationRingUnitOfUniverses R s) μ α K L) ∧
    ∀ (K' L' : DerivedCategory (scalarModules J R))
      (_hK' : HasLocalizationHomContinuity.{c, v, r, w} J R K') (_hL' : ∃ n : ℤ, L'.IsGE n)
      (f : K' ⟶ K) (g : L ⟶ L'),
      (M.scalar (ringedLocalizationRingUnitOfUniverses R s)).derived.map
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).map (Prod.mkHom f.op g)) ≫
        localizationHomComparison.{c, v, r, w} M (ringedLocalizationRingUnitOfUniverses R s)
          (μ (ringedLocalizationRingUnitOfUniverses R s)) K' L' =
      localizationHomComparison.{c, v, r, w} M (ringedLocalizationRingUnitOfUniverses R s)
          (μ (ringedLocalizationRingUnitOfUniverses R s)) K L ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J
          (ringedLocalizationRingOfUniverses R s)).map
            (Prod.mkHom
              ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).derived.map f).op
              ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).derived.map g)) := by
  let a := ringedLocalizationRingUnitOfUniverses R s
  let S := ringedLocalizationRingOfUniverses R s
  let F := (M.scalar a).derived
  let H := derivedInternalHomOfUniverses.{c, v, r, w} J R
  let H' := derivedInternalHomOfUniverses.{c, v, r, w} J S
  have hnat (A B A' B' : DerivedCategory (scalarModules J R))
      (f : A' ⟶ A) (g : B ⟶ B') :
      F.map (H.map (Prod.mkHom f.op g)) ≫
          localizationHomComparison M a (μ a) A' B' =
        localizationHomComparison M a (μ a) A B ≫
          H'.map (Prod.mkHom (F.map f).op (F.map g)) := by
    exact LocalizationHomProof.closedComparison_naturality
      (M.closed R) (M.closed S) F (μ a).iso A B A' B' f g
  obtain ⟨n, hn⟩ := hL
  have : L.IsGE n := hn
  obtain ⟨P, hP, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE L n
  have : P.IsStrictlyGE n := hP
  obtain ⟨β, hβ⟩ := localizationHom_iso_on_Q M R s K hK P n
  have heq := localizationHom_unique M R s μ α K (DerivedCategory.Q.obj P) β.hom hβ
  have hβiso : IsIso (localizationHomRestrictedComparison M a μ α K
      (DerivedCategory.Q.obj P)) := by
    rw [← heq]
    infer_instance
  have : IsIso (localizationHomComparison M a (μ a) K
      (DerivedCategory.Q.obj P)) :=
    localizationHom_isIso_of_restricted M a μ α K _ hβiso
  let t := H'.map (Prod.mkHom (F.map (𝟙 K)).op (F.map e.hom))
  have : IsIso t := by
    dsimp only [t]
    simp only [Functor.map_id, op_id]
    change IsIso ((H'.mapIso
      ((Iso.refl (op (F.obj K))).prod (F.mapIso e))).hom)
    infer_instance
  have : IsIso (F.map (H.map (Prod.mkHom (𝟙 K).op e.hom))) := by
    change IsIso ((F.mapIso (H.mapIso ((Iso.refl (op K)).prod e))).hom)
    infer_instance
  have hc : IsIso (localizationHomComparison M a (μ a) K L ≫ t) := by
    rw [← hnat K L K (DerivedCategory.Q.obj P) (𝟙 K) e.hom]
    infer_instance
  have hχ : IsIso (localizationHomComparison M a (μ a) K L) :=
    (isIso_comp_right_iff _ t).mp hc
  refine ⟨hχ, ?_, localizationHom_unit M a μ α K L,
    localizationHom_unique M R s μ α K L, ?_⟩
  · dsimp only [localizationHomRestrictedComparison]
    infer_instance
  · intro K' L' _ _ f g
    exact hnat K L K' L' f g

end CategoryTheory

