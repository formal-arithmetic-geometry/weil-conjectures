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
import Sheaf.AlgebraicGeometry.ProEtaleProductsDerived

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
  sorry

end AlgebraicGeometry.Scheme
