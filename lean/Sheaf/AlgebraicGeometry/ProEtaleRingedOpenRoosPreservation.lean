/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q76
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenExtensionProducts
import Sheaf.AlgebraicGeometry.ProEtaleProductsExact
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit

/-!
# Ringed pro-etale open extension preserves products and Roos triangles

Source: Bhatt--Scholze, Lemma 6.1.13, ringed product/Roos refinement;
Stacks Project, Tags 09AH, 09AG, 09BN, 09BP, 015F and 08TC
(blueprint: lem-sf-ringed-open-roos-preservation).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The termwise derived extension by zero, using the localized presentation of
`U` with coefficients `(proEtaleModuleCoefficients R).over U`. The equivalence with
modules over the actual inverse-image ring is supplied by `proEtale_ringed_open_closed`.
Exactness and additivity here are extracted from that theorem, not additional assumptions.

Source: Stacks Project, Tags 09AH, 09BN and 015F
(blueprint: lem-sf-ringed-open-roos-preservation). -/
abbrev proEtaleRingedOpenDerived {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    [HasDerivedCategory.{v}
      (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R))] :=
  let h := (proEtale_ringed_open_closed i U hU R).choose_spec.2.choose_spec.choose_spec
  letI : PreservesFiniteLimits (proEtaleRingedExtensionByZero U R) := h.2.2.2.2.1
  letI : PreservesFiniteColimits (proEtaleRingedExtensionByZero U R) := h.2.2.2.2.2.1
  letI : (proEtaleRingedExtensionByZero U R).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  letI : PreservesBinaryBiproducts (proEtaleRingedExtensionByZero U R) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  letI : (proEtaleRingedExtensionByZero U R).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  (proEtaleRingedExtensionByZero U R).mapDerivedCategory

/-- Exact functors preserving products preserve them after localization when the
products in both abelian categories are exact. Choose representatives and use the
localized product cones and the exact-functor factorization isomorphism.
Source: Stacks, Derived Categories, lemma-products and Tag 015F. -/
private theorem derived_preserves_products
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (I : Type*) [HasProductsOfShape I A] [HasProductsOfShape I B]
    [HasExactLimitsOfShape (Discrete I) A] [HasExactLimitsOfShape (Discrete I) B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape (Discrete I) F] :
    PreservesLimitsOfShape (Discrete I) F.mapDerivedCategory := by
  let Q : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  have : PreservesLimitsOfShape (Discrete I) (F.mapHomologicalComplex (.up ℤ)) := by
    apply HomologicalComplex.preservesLimitsOfShape_of_eval
    intro n
    exact inferInstanceAs
      (PreservesLimitsOfShape (Discrete I) (HomologicalComplex.eval A (.up ℤ) n ⋙ F))
  have : PreservesLimitsOfShape (Discrete I) (Q ⋙ F.mapDerivedCategory) :=
    preservesLimitsOfShape_of_natIso F.mapDerivedCategoryFactors.symm
  have hrep (K : I → CochainComplex A ℤ) :
      PreservesLimit (Discrete.functor (fun i ↦ Q.obj (K i))) F.mapDerivedCategory := by
    apply preservesLimit_of_preserves_limit_cone (DerivedCategory.isLimitFanQ K)
    exact (isLimitMapConeFanMkEquiv F.mapDerivedCategory _ _).symm
      (isLimitFanMkObjOfIsLimit (Q ⋙ F.mapDerivedCategory) K _ (productIsProduct K))
  have (K : I → DerivedCategory A) :
      PreservesLimit (Discrete.functor K) F.mapDerivedCategory := by
    let K' : I → CochainComplex A ℤ := fun i ↦ Q.objPreimage (K i)
    let : PreservesLimit (Discrete.functor (fun i ↦ Q.obj (K' i)))
        F.mapDerivedCategory := hrep K'
    exact preservesLimit_of_iso_diagram F.mapDerivedCategory
      (Discrete.natIso (F := Discrete.functor fun i ↦ Q.obj (K' i))
        (G := Discrete.functor K) fun i ↦ Q.objObjPreimageIso (K i.as))
  exact preservesLimitsOfShape_of_discrete F.mapDerivedCategory

attribute [local irreducible] proEtaleRingedExtensionByZero

/-- Canonical countable products and Roos triangles are preserved by the exact
ringed open extension on ordinary unbounded derived categories. `phi.hom` is the
canonical product comparison, normalized on every projection. The displayed transition
identity uses arbitrary derived transition maps, and the last arrow uses the canonical
shift comparison. No boundedness, constructibility or constant-coefficient assumption
is made; neither quasi-compactness nor quasi-separatedness of `X` is needed.

Source: Bhatt--Scholze, Lemma 6.1.13, ringed product/Roos refinement;
Stacks Project, Tags 09BP, 015F and 08TC
(blueprint: lem-sf-ringed-open-roos-preservation).

Proof plan:
1. Apply `proEtaleRingedExtensionByZero_products` to countable module-sheaf families.
   Its projection-normalized comparison is natural in the family maps.
2. Choose complexes representing the derived objects and apply this comparison in
   every degree. Naturality makes it an isomorphism of complexes. The theorem
   `ProEt.products_derived` identifies termwise products with derived products and
   their projections on both sites (transporting the open site through localization).
   Exactness from `proEtale_ringed_open_closed` and `Functor.mapDerivedCategory`
   localizes the comparison to `phi`, with the stated projection normalization.
3. Project the transition comparison to `n`. Both paths are `J(pr_n)` minus
   `J(pr_(n+1))` followed by `J(d_n)`, by additivity and functoriality of `J`.
   Product uniqueness gives the equality. Likewise the first arrow's components
   are `J(c followed by pr_n)`. This requires no strict representative of the tower.
4. Apply the triangulated functor `J` to the original distinguished triangle.
   Transport its middle objects by `phi` and its shifted object by `J.commShiftIso 1`.
   Step 3 identifies the middle arrow with the new tower transition. The last arrow
   is `phi.inv` followed by `J(delta)` and the shift comparison. Invariance of
   distinguished triangles under isomorphism gives the asserted Roos triangle. -/
theorem proEtaleRingedOpenDerived_products_roos {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    [HasDerivedCategory.{v}
      (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R))] :
    ∃ (_ : HasCountableProducts (DerivedCategory
        (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U))))
      (_ : HasCountableProducts (DerivedCategory
        (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R)))),
      ∀ C : ℕ → DerivedCategory
          (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U)),
        ∃ phi : (proEtaleRingedOpenDerived i U hU R).obj (∏ᶜ C) ≅
            ∏ᶜ (fun n ↦ (proEtaleRingedOpenDerived i U hU R).obj (C n)),
          phi.hom = piComparison (proEtaleRingedOpenDerived i U hU R) C ∧
          (∀ n : ℕ, phi.hom ≫
              Pi.π (fun m ↦ (proEtaleRingedOpenDerived i U hU R).obj (C m)) n =
            (proEtaleRingedOpenDerived i U hU R).map (Pi.π C n)) ∧
          ∀ d : ∀ n : ℕ, C (n + 1) ⟶ C n,
            (proEtaleRingedOpenDerived i U hU R).map (towerTransitionEndomorphism d) ≫
                phi.hom =
              phi.hom ≫ towerTransitionEndomorphism
                (fun n ↦ (proEtaleRingedOpenDerived i U hU R).map (d n)) ∧
            ∀ (L : DerivedCategory
                (ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U)))
              (c : L ⟶ ∏ᶜ C) (delta : ∏ᶜ C ⟶ L⟦(1 : ℤ)⟧),
              IsDerivedLimitTriangle d L c delta →
                IsDerivedLimitTriangle
                    (fun n ↦ (proEtaleRingedOpenDerived i U hU R).map (d n))
                    ((proEtaleRingedOpenDerived i U hU R).obj L)
                    ((proEtaleRingedOpenDerived i U hU R).map c ≫ phi.hom)
                    (phi.inv ≫ (proEtaleRingedOpenDerived i U hU R).map delta ≫
                      ((proEtaleRingedOpenDerived i U hU R).commShiftIso (1 : ℤ)).hom.app L) ∧
                ∀ n : ℕ,
                  (proEtaleRingedOpenDerived i U hU R).map c ≫ phi.hom ≫
                      Pi.π (fun m ↦ (proEtaleRingedOpenDerived i U hU R).obj (C m)) n =
                    (proEtaleRingedOpenDerived i U hU R).map (c ≫ Pi.π C n) := by
  classical
  -- Work on the localized module site, without changing coefficient presentations.
  let A := ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U)
  let B := ringedSiteModules.{u + 1} (proEtaleModuleCoefficients R)
  let : Abelian A := inferInstance
  let : Abelian B := inferInstance
  let : HasCountableProducts A := inferInstance
  let : HasCountableProducts B := inferInstance
  let F := proEtaleRingedExtensionByZero U R
  let h := (proEtale_ringed_open_closed i U hU R).choose_spec.2.choose_spec.choose_spec
  let : PreservesFiniteLimits F := h.2.2.2.2.1
  let : PreservesFiniteColimits F := h.2.2.2.2.2.1
  let : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  let : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  let : F.Additive := Functor.additive_of_preservesBinaryBiproducts _
  let aj := (proEtale_ringed_open_closed i U hU R).choose_spec.2.choose_spec.choose
  have (M : A) : IsIso (aj.unit.app M) := h.2.1 M
  have : IsIso aj.unit := NatIso.isIso_of_isIso_app _
  let : F.Full := aj.fullyFaithfulLOfIsIsoUnit.full
  let : F.Faithful := aj.fullyFaithfulLOfIsIsoUnit.faithful
  -- The sheaf theorem is indexed in the coefficient universe.
  have hpres (M : ULift.{u + 1} ℕ → A) :
      PreservesLimit (Discrete.functor M) F := by
    let := (proEtaleRingedExtensionByZero_products U R _ M).1
    exact PreservesProduct.of_iso_comparison F M
  let : PreservesLimitsOfShape (Discrete (ULift.{u + 1} ℕ)) F :=
    preservesLimitsOfShape_of_discrete F
  let : PreservesLimitsOfShape (Discrete ℕ) F :=
    preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) F
  let : HasExactLimitsOfShape (Discrete ℕ) B :=
    ProEt.products_exact.{u, 0, 0} X (proEtaleModuleCoefficients R) ℕ
  -- Full faithfulness reflects finite colimits, hence exactness of products.
  let : HasExactLimitsOfShape (Discrete ℕ) A :=
    HasExactLimitsOfShape.domain_of_functor (Discrete ℕ) F
  let := SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
    ((ProEt.topology X).over U) ((proEtaleModuleCoefficients R).over U)
  let := SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
    (ProEt.topology X) (proEtaleModuleCoefficients R)
  let J := proEtaleRingedOpenDerived i U hU R
  let : J.Additive := inferInstance
  let : J.CommShift ℤ := inferInstance
  let : J.IsTriangulated := inferInstance
  let : PreservesLimitsOfShape (Discrete ℕ) J := derived_preserves_products ℕ F
  have hA : HasCountableProducts (DerivedCategory A) :=
    ⟨fun I _ ↦ DerivedCategory.hasLimitsOfShape_discrete A I⟩
  have hB : HasCountableProducts (DerivedCategory B) :=
    ⟨fun I _ ↦ DerivedCategory.hasLimitsOfShape_discrete B I⟩
  refine ⟨hA, hB, ?_⟩
  intro C
  let e := PreservesProduct.iso J C
  have he (n : ℕ) : e.hom ≫ Pi.π (fun m ↦ J.obj (C m)) n = J.map (Pi.π C n) :=
    piComparison_comp_π J C n
  refine ⟨e, rfl, he, ?_⟩
  intro d
  -- Check the transition endomorphism on every product projection.
  have hc : J.map (towerTransitionEndomorphism d) ≫ e.hom =
      e.hom ≫ towerTransitionEndomorphism (fun n ↦ J.map (d n)) := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, he, towerTransitionEndomorphism, Functor.map_sub,
      Preadditive.sub_comp, Preadditive.comp_sub, Category.comp_id,
      towerProductShift, Pi.lift_π]
    rw [← Category.assoc, he]
    simp only [← J.map_comp, Pi.lift_π, Category.id_comp]
  refine ⟨hc, ?_⟩
  intro L c delta ht
  refine ⟨?_, ?_⟩
  · apply Pretriangulated.isomorphic_distinguished _ (J.map_distinguished _ ht)
    refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm ?_ ?_ ?_
    · change (J.map c ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ J.map c
      simp
    · change towerTransitionEndomorphism (fun n ↦ J.map (d n)) ≫ e.inv =
        e.inv ≫ J.map (towerTransitionEndomorphism d)
      apply (cancel_epi e.hom).1
      rw [← Category.assoc, ← hc]
      simp
    · change (e.inv ≫ J.map delta ≫ (J.commShiftIso (1 : ℤ)).hom.app L) ≫
        (shiftFunctor _ (1 : ℤ)).map (𝟙 _) =
          e.inv ≫ (J.map delta ≫ (J.commShiftIso (1 : ℤ)).hom.app L)
      simp
  · intro n
    rw [he, ← J.map_comp]

end AlgebraicGeometry.Scheme
