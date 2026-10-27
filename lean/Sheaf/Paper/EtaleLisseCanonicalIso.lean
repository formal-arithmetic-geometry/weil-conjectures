/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E8
-/
module

public import Sheaf.Paper.EtaleFiniteFreeHomLocalIdentity
public import Sheaf.Paper.EtalePerfectHomRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHom
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
import Sheaf.Paper.FiniteCoefficientFlatModel
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic

/-! # Canonical lisse coefficient-Hom isomorphism

This is the comparison-and-descent step of the lisse Hom reduction. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures
attribute [local instance] lisseHomModuleDerivedCategory
attribute [local implicit_reducible] finiteHomEtaleCategory

/-- The coefficient-Hom comparison type is definitionally the type of the canonical arrow,
so invertibility transfers along a heterogeneous equality.
Source: comparison domain (blueprint: lem-coef-etale-lisse-canonical-iso). -/
private theorem canonical_isIso_of_heq (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) {n m : ℕ} (h : m ≤ n) (K N : finiteHomEtale l E T n)
    (v : LisseHomComparisonType
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1)))
      (finiteHomQuotient l E h) T K N)
    (hv : HEq v (etaleFiniteHomCanonical l E T h K N)) (hiso : IsIso v) :
    IsIso (etaleFiniteHomCanonical l E T h K N) := by
  obtain rfl : v = etaleFiniteHomCanonical l E T h K N := eq_of_heq hv
  exact hiso

attribute [local irreducible] _root_.DerivedCategory instCategoryDerivedCategory
attribute [local irreducible] Sheaf.monoidalCategory Sheaf.braidedCategory
  Sheaf.symmetricCategory
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  _root_.DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution
attribute [local irreducible] Functor.rightAdjoint Functor.leftAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Etale.rightDerivedUpperShriek Etale.rightDerivedLowerShriek
  Etale.upperStar Etale.lowerStar Etale.derivedHom _root_.DerivedCategory.monoidalClosed
  ProEtale.pbcFixedScalarExtension Etale.derivedTensor
  Padic.coefficientExtensionAbsoluteValue Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionIdeal
  coefficientBaseChangeHom finiteHomEtaleData finiteHomEtaleClosed finiteHomEtaleTensor
  finiteHomEtaleClosedGeneral finiteHomEtaleRightAdjunctionGeneral finiteHomDerivedBraiding


private theorem lisseBounded_iff (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (K : Etale.DerivedCategoryModule A T) :
    Etale.DerivedCategory.isBoundedConstructible A T K ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K := by
  constructor
  · rintro ⟨hc, a, b, hab, hb⟩
    refine ⟨(_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded K).1
      ⟨a, b, ?_, ?_⟩, ?_⟩
    · exact (_root_.DerivedCategory.isGE_iff K a).2 fun q hq ↦ hb q (.inl hq)
    · exact (_root_.DerivedCategory.isLE_iff K b).2 fun q hq ↦ hb q (.inr hq)
    · intro q
      exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc q)
  · rintro ⟨hb, hc⟩
    obtain ⟨a, b, ha, hb⟩ :=
      (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded K).2 hb
    refine ⟨fun q ↦ (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (hc q), min a b, b, min_le_right _ _, ?_⟩
    intro q hq
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff K a).1 ha q (lt_of_lt_of_le hq (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff K b).1 hb q hq

private theorem predicate_of_canonical_witnesses
    {α α' : Sort v} {β β' : Sort w} (c : α') (d : β')
    (P : α → β → Prop) (x : α) (y : β)
    (hx : HEq x c) (hy : HEq y d)
    (h : ∃ (a : α) (b : β), @HEq α a α' c ∧ @HEq β b β' d ∧ P a b) : P x y := by
  obtain ⟨a, b, ha, hb, hp⟩ := h
  have hax : a = x := eq_of_heq (ha.trans hx.symm)
  have hby : b = y := eq_of_heq (hb.trans hy.symm)
  subst a
  subst b
  exact hp

private theorem iso_of_square
    {C₁ C₂ C₃ C₄ : Type v} [Category.{w} C₁] [Category.{w} C₂]
    [Category.{w} C₃] [Category.{w} C₄]
    (H₁ : C₁ᵒᵖ × C₁ ⥤ C₁) (H₂ : C₂ᵒᵖ × C₂ ⥤ C₂)
    (H₃ : C₃ᵒᵖ × C₃ ⥤ C₃) (H₄ : C₄ᵒᵖ × C₄ ⥤ C₄)
    (F : C₁ ⥤ C₂) (G : C₃ ⥤ C₄) (R : C₁ ⥤ C₃) (S : C₂ ⥤ C₄)
    (σ : F ⋙ S ≅ R ⋙ G)
    (χ : ∀ K N : C₁, R.obj (H₁.obj (op K, N)) ⟶ H₃.obj (op (R.obj K), R.obj N))
    (ψ : ∀ K N : C₂, S.obj (H₂.obj (op K, N)) ⟶ H₄.obj (op (S.obj K), S.obj N))
    (K N : C₁)
    (vT : F.obj (H₁.obj (op K, N)) ⟶ H₂.obj (op (F.obj K), F.obj N))
    (vU : G.obj (H₃.obj (op (R.obj K), R.obj N)) ⟶
      H₄.obj (op (G.obj (R.obj K)), G.obj (R.obj N)))
    (hs : LisseHomRestrictionSquare H₁ H₂ H₃ H₄ F G R S σ χ ψ K N vT vU)
    [IsIso vU] : IsIso (S.map vT) := by
  have := hs.1
  have := hs.2.1
  have : IsIso (S.map vT ≫ ψ (F.obj K) (F.obj N) ≫
      H₄.map (Prod.mkHom (σ.inv.app K).op (σ.hom.app N))) := by
    rw [← hs.2.2]
    infer_instance
  have : IsIso (H₄.map (Prod.mkHom (σ.inv.app K).op (σ.hom.app N))) := by
    exact H₄.map_isIso (Iso.prod ((σ.app K).symm.op) (σ.app N)).hom
  have : IsIso (ψ (F.obj K) (F.obj N) ≫
      H₄.map (Prod.mkHom (σ.inv.app K).op (σ.hom.app N))) :=
    IsIso.comp_isIso' hs.2.1 inferInstance
  exact IsIso.of_isIso_comp_right (S.map vT)
    (ψ (F.obj K) (F.obj N) ≫ H₄.map (Prod.mkHom (σ.inv.app K).op (σ.hom.app N)))

private theorem iso_of_coordinates
    {C : Type*} [Category C] {X Y Z : C} (v : X ⟶ Y) (s : X ⟶ Z) (t : Y ⟶ Z)
    [IsIso s] [IsIso t] (h : v ≫ t = s) : IsIso v := by
  have : IsIso (v ≫ t) := by rw [h]; infer_instance
  exact IsIso.of_isIso_comp_right v t

private theorem comparison_isIso_of_local
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A]
    (φ : A →+* B)
    (v : ∀ (T : Scheme.{u}) (K N : Etale.DerivedCategoryModule A T),
      LisseHomComparisonType A B φ T K N)
    (hloc : ∀ T K N, LisseHomLocalFreeCalculationRing A B φ T K N (v T K N))
    (S : Scheme.{u})
    (K N : Etale.DerivedCategoryModule A S)
    (htriv : ∃ V : Scheme.Cover.{u} Scheme.etalePrecoverage S, ∀ i : V.I₀,
      ∃ r : ℕ, Nonempty ((L(Etale.upperStar (ModuleCat.{u + 1} A) (V.f i))).obj K ≅
        (_root_.DerivedCategory.singleFunctor _ 0).obj
          ((lisseHomConstantFunctor A (V.X i)).obj (ModuleCat.of A (Fin r → A)))))
    (hNbc : Etale.DerivedCategory.isBoundedConstructible A S N)
    (a b : ℤ) (hab : a ≤ b)
    (hNtor : Etale.DerivedCategory.hasTorAmplitudeIn A S a b N)
    (hres : ∀ (U : Scheme.{u}) (f : U ⟶ S) [Etale f],
      LisseHomRestrictionCompatibilityRing A B φ S U f
        K N
        (v S K N)
        (v U (L(Etale.upperStar (ModuleCat.{u + 1} A) f).obj
          K)
          (L(Etale.upperStar (ModuleCat.{u + 1} A) f).obj N))) :
    IsIso (v S K N) := by
  obtain ⟨V, hV⟩ := htriv
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} A)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} B)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  apply Etale.DerivedCategory.isIso_of_isIso_leftDerivedUpperStar_map_of_cover
    (A := ModuleCat.{u + 1} B) V
  intro i
  let U := V.X i
  let f := V.f i
  have : Etale f := V.map_prop i
  let F := L(Etale.upperStar (ModuleCat.{u + 1} A) f)
  obtain ⟨r, ⟨eK⟩⟩ := hV i
  have hNu := Etale.boundedConstructible_leftDerivedUpperStar
    (ModuleCat.{u + 1} A) f ((lisseBounded_iff A S N).1 hNbc)
  have hNut := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
    (Etale.torAmplitudeIn_leftDerivedUpperStar (ModuleCat.{u + 1} A) f _ _
      (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 hNtor))
  obtain ⟨P, hP, ⟨eP⟩⟩ :=
    (Etale.hasTorAmplitudeIn_iff_exists_flatModel A _ _ hab
      (F.obj N) hNu).1 hNut
  obtain ⟨_, hs, ht, he⟩ := hloc U (F.obj K) (F.obj N) r eK P a b hP eP
  have := hs
  have := ht
  have : IsIso (v U (F.obj K) (F.obj N)) :=
    iso_of_coordinates (v U (F.obj K) (F.obj N)) _ _ he
  exact iso_of_square _ _ _ _ _ _ _ _ _ _ _ K N _ _ (hres U f)




/-- The canonical coefficient-Hom arrow is invertible after a finite-free etale cover.
Source: thm-coef-finite-hom, proof paragraphs 2--3
(blueprint: lem-coef-etale-lisse-canonical-iso).

Proof: choose the finite-free cover of the dualizable first input.  The finite-free
coordinate calculation identifies the comparison with evaluation on every member of
the cover.  The restriction square transports this identity to the cover's etale
pullbacks.  The second input is replaced by its bounded flat model, so the coordinate
maps are isomorphisms.  Conservativity of geometric stalks then makes the comparison
an isomorphism globally.  This is strictly the comparison component; the local
calculation and restriction predicates are supplied separately by the two lower
lemmas imported above. -/
theorem etaleLisseCanonicalIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    [Finite (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))]
    (m : ℕ) (hmn : m ≤ n)
    (S : Scheme.{u}) (K N : finiteHomEtale l E S n)
    (hKdual : IsDualizable K)
    (htrivK : ∃ V : Scheme.Cover.{u} Scheme.etalePrecoverage S, ∀ i : V.I₀,
      ∃ r : ℕ, Nonempty
        ((L(Etale.upperStar (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) (V.f i))).obj K ≅
          (_root_.DerivedCategory.singleFunctor _ 0).obj
            ((lisseHomConstantFunctor
              (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) (V.X i)).obj
                (ModuleCat.of
                  (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
                  (Fin r → ULift.{u + 1, u}
                    (Padic.coefficientExtensionRing l E (n + 1)))))))
    (hNbc : Etale.DerivedCategory.isBoundedConstructible
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) S N)
    (c d : ℤ) (hcd : c ≤ d)
    (hNtor : Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) S c d N) :
    IsIso (etaleFiniteHomCanonical l E S hmn K N) := by
  let v : ∀ (T : Scheme.{u}) (K N : finiteHomEtale l E T n), LisseHomComparisonType
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1)))
      (finiteHomQuotient l E hmn) T K N :=
    fun T K N ↦ (etaleFiniteFreeHomLocalIdentity l E T hmn K N).choose
  have hv : ∀ (T : Scheme.{u}) (K N : finiteHomEtale l E T n),
      HEq (v T K N) (etaleFiniteHomCanonical l E T hmn K N) := fun T K N ↦
    (etaleFiniteFreeHomLocalIdentity l E T hmn K N).choose_spec.1
  exact canonical_isIso_of_heq l E S hmn K N _ (hv S K N)
    (comparison_isIso_of_local _ _ (finiteHomQuotient l E hmn) v
      (fun T K N ↦ (etaleFiniteFreeHomLocalIdentity l E T hmn K N).choose_spec.2)
      S K N htrivK hNbc c d hcd hNtor
      (fun U f _ ↦ predicate_of_canonical_witnesses _ _ _ _ _ (hv _ _ _) (hv _ _ _)
        (etalePerfectHomRestriction l E S U f hmn K N hKdual)))

end WeilConjectures
