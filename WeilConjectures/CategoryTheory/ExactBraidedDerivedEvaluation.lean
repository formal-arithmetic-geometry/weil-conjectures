/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.AdaptedBraidedLocalization
import all WeilConjectures.Algebra.Homology.HomotopyCategory.BraidedCochainNormalization

/-! # Exact braided derived evaluation using simultaneous flat resolutions

Source: Stacks Project, Tags 06YS, 06YT, 06YU and 0FPT.
(blueprint: lem-zl-exact-braided-derived-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.Functor

universe a b ha hb wa wb
variable {B : Type a} [Category.{ha} B] [Abelian B]
  [IsGrothendieckAbelian.{ha} B] [HasColimitsOfSize.{0, 0} B]
  [MonoidalCategory B] [MonoidalClosed B] [MonoidalPreadditive B] [SymmetricCategory B]
  [Abelian.HasFunctorialFlatResolution B] [HasDerivedCategory.{wa} B]
  {E : Type b} [Category.{hb} E] [Abelian E]
  [IsGrothendieckAbelian.{hb} E] [HasColimitsOfSize.{0, 0} E]
  [MonoidalCategory E] [MonoidalClosed E] [MonoidalPreadditive E] [SymmetricCategory E]
  [Abelian.HasFunctorialFlatResolution E] [HasDerivedCategory.{wb} E]

/-- Exact, cocontinuous, flat-preserving braided functors induce braided derived functors.
Their canonical localization factorization is monoidal for the ordinary cochain lift.
No assumption of preservation of every K-flat complex is made.

Source: Stacks Project, Tags 06YS, 06YT, 06YU and 0FPT
(blueprint: lem-zl-exact-braided-derived-evaluation).

Proof: use the full subcategory of complexes that are K-flat and whose images are
K-flat. Functorial flat-term resolutions belong to this subcategory: the functor
preserves flat terms and the countable colimits used in their construction. These
functorial resolutions give a left derivability structure. Both localization tensorators
are invertible on this subcategory. The adapted braided localization theorem therefore
constructs the strong braided structure and proves the monoidal factorization equation,
including its unit. -/
theorem exactBraidedDerivedEvaluation
    (G : B ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesColimitsOfSize.{0, 0} G] [G.PreservesFlat] (m : G.Braided) :
    letI := RingedDerivedNative.derivedSymmetric (A := B)
    letI := RingedDerivedNative.derivedSymmetric (A := E)
    ∃ n : G.mapDerivedCategory.Braided, letI := m; letI := n
      letI := Functor.mapCochainComplexMonoidal G
      NatTrans.IsMonoidal G.mapDerivedCategoryFactors.hom := by
  letI := m
  letI := RingedDerivedNative.derivedSymmetric (A := B)
  letI := RingedDerivedNative.derivedSymmetric (A := E)
  letI := OplaxMonoidal.cochainBraided G
  let W := HomologicalComplex.quasiIso B (.up ℤ)
  let S : ObjectProperty (CochainComplex B ℤ) := W.kFlat ⊓
    (HomologicalComplex.quasiIso E (.up ℤ)).kFlat.inverseImage
      (G.mapHomologicalComplex (.up ℤ))
  let Φ := LocalizerMorphism.ofEq (F := S.ι) (W₂ := W) rfl
  have : HasExactColimitsOfShape ℤ B := by
    have := AB5OfSize_of_univLE.{0, 0, ha, ha} B
    infer_instance
  have : HasExactColimitsOfShape ℤ E := by
    have := AB5OfSize_of_univLE.{0, 0, hb, hb} E
    infer_instance
  have (X : E) : PreservesColimitsOfShape ℤ ((curriedTensor E).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y) (by intros; simp [curriedTensor]))
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution B).some.reduced
  have hρ (P : CochainComplex B ℤ) : S (Λ.resolutionFunctor.obj P) :=
    ⟨Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le P,
      G.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ
        ObjectProperty.flat.essImage_ι_le P⟩
  have : Φ.functor.Full := inferInstanceAs S.ι.Full
  have : Φ.functor.Faithful := inferInstanceAs S.ι.Faithful
  have : Φ.IsInduced := ⟨rfl⟩
  have : Φ.IsLeftDerivabilityStructure :=
    Φ.isLeftDerivabilityStructure_of_functorial_resolutions
      (ρ := ObjectProperty.lift S Λ.resolutionFunctor hρ) Λ.resolutionNatTrans
      (fun P ↦ by
        change HomologicalComplex.quasiIso B (.up ℤ) _
        rw [HomologicalComplex.mem_quasiIso_iff]
        exact Λ.quasiIso_resolutionNatTrans_app P) rfl
  have : IsIso (LaxMonoidal.ε (DerivedCategory.Q (C := B))) :=
    RingedDerivedNative.localization_isIso_ε
  have : IsIso (LaxMonoidal.ε (DerivedCategory.Q (C := E))) :=
    RingedDerivedNative.localization_isIso_ε
  letI : (DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B).LaxBraided :=
    RingedDerivedNative.localizationLaxBraided
  letI : (DerivedCategory.Q : CochainComplex E ℤ ⥤ DerivedCategory E).LaxBraided :=
    RingedDerivedNative.localizationLaxBraided
  have hmodels (X : DerivedCategory B) :
      ∃ P, S P ∧ Nonempty (DerivedCategory.Q.obj P ≅ X) := by
    let P := DerivedCategory.Q.objPreimage X
    have : QuasiIso (Λ.resolutionNatTrans.app P) := Λ.quasiIso_resolutionNatTrans_app P
    exact ⟨Λ.resolutionFunctor.obj P, hρ P,
      ⟨asIso (DerivedCategory.Q.map (Λ.resolutionNatTrans.app P)) ≪≫
        DerivedCategory.Q.objObjPreimageIso X⟩⟩
  have hQ (P R : CochainComplex B ℤ) (hR : S R) :
      IsIso (LaxMonoidal.μ DerivedCategory.Q P R) :=
    RingedDerivedNative.localization_isIso_mu P R
      (Or.inr ((HomotopyCategory.kFlat_quotient_obj_iff R).2 hR.1))
  have hL (P : CochainComplex E ℤ) (R : CochainComplex B ℤ) (hR : S R) :
      IsIso (LaxMonoidal.μ DerivedCategory.Q P
        ((G.mapHomologicalComplex (.up ℤ)).obj R)) :=
    RingedDerivedNative.localization_isIso_mu P _
      (Or.inr ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hR.2))
  exact adaptedBraidedLocalization DerivedCategory.Q DerivedCategory.Q
    (G.mapHomologicalComplex (.up ℤ)) G.mapDerivedCategory
    G.mapDerivedCategoryFactors W S hmodels hQ hL

end CategoryTheory.Functor
