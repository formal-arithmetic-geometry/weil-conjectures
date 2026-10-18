/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.AlgebraicGeometry.ProperHypercover
public import Sheaf.AlgebraicGeometry.TotalEtaleAugmentationAdjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import Sheaf.AlgebraicGeometry.PhSchemeSite
import Sheaf.Paper.SiteHypercoverDerivedDescent
import Sheaf.CategoryTheory.Sites.GeometricMorphism
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.PhEtaleTorsionComparison
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import Sheaf.CategoryTheory.RingedCoefficientRestrictionCounit
import Sheaf.TraceFormula.SimplicialPhEtaleSquare
import Sheaf.TraceFormula.TotalSiteDerivedComponents

/-!
# Universal torsion étale descent for proper hypercovers

Source: Stacks Project, `spaces-simplicial.tex`, Tag 0DHL and the section
`section-proper-hypercovering-spaces`, including its explicit scheme specialization
(blueprint: lem-trf-proper-hypercover-etale-descent).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Proper hypercovers have proper augmentations and universally give torsion étale
cohomological descent with the ordinary derived-unit normalization.
Source: Stacks Project, Tag 0DHL and `section-proper-hypercovering-spaces`
(blueprint: lem-trf-proper-hypercover-etale-descent).

Proof:
1. Induct on the degree. The proper-face matching object is an equalizer between finite
products of lower terms over the base. Their structure morphisms are proper, and the
compatibility equalizer is closed because these products are separated. Composing its
proper structure map with the assumed proper matching arrow proves termwise properness.
2. Pullback to `Y` commutes with each matching limit by its representing universal property.
The matching arrows are therefore the base changes of the original arrows and remain
proper and surjective, including degree zero with matching object `Y`.
3. First forget to torsion abelian coefficients. The proper-surjective matching arrows
are ph covers, so `lem-trf-site-hypercover-derived-descent` gives the actual derived unit
on the ph site after pulling back a base complex to that site.
4. Form the simplicial ph/étale square of `lem-trf-simplicial-ph-etale-square`. Its exact
inverse images identify the pullbacks of the complex in every degree; torsion and the
bounded-below condition are preserved.
5. Apply `lem-trf-ph-etale-torsion-comparison` on each component. By
`lem-trf-total-site-derived-components`, these are the restrictions of the total comparison
unit. Component restriction is exact and conservative, so this unit is invertible.
6. The composite-unit identity of `lem-sfb-derived-composition-adjunction-normalization`
identifies the composite of the étale unit with this comparison unit and the corresponding
composite of the ph unit and the base comparison unit. The other three units are invertible,
so the specified étale unit is invertible.
7. Use `lem-pe-constant-left-module-inverse-image` and
`lem-pur-ringed-coefficient-restriction-counit` for the constant `Λ` sheaves and `ℤ → Λ`.
Transpose the forgotten module unit under the abelian adjunction. The counit equation,
naturality, and the triangle identity identify this transpose with the inverse-image
coefficient comparison, hence identify the actual module and abelian units.
8. Scalar forgetting is exact by `lem-weil-pbc-module-sheaves-colimits-forgetful` and
conservative on cohomology. Since `mΛ = 0`, its cohomology is torsion. The abelian result
and the preceding unit identity therefore prove the module unit is invertible.
9. For any `Y → X`, repeat steps 3–8 on the base-changed hypercover provided by step 2,
with an arbitrary bounded-below complex on `Y`. This proves the universal assertion,
without requiring that this complex be pulled back from `X`. -/
theorem isProper_and_universal_etale_descent_of_isProperHypercover
    {X : Scheme.{u}} (U : SimplicialObject (Over X)) (hU : IsProperHypercover U) :
    (∀ n : ℕ, IsProper (U.obj (op (SimplexCategory.mk n))).hom) ∧
      (∀ (Y : Scheme.{u}) (f : Y ⟶ X), IsProperHypercover (U ⋙ Over.pullback f)) ∧
      (∀ (Λ : Type (u + 1)) [CommRing Λ] (m : ℕ), 1 ≤ m → (m : Λ) = 0 →
        (∀ L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
          IsIso ((totalEtaleAugmentationAdjunction U Λ).derivedPlus.unit.app L)) ∧
        (∀ (Y : Scheme.{u}) (f : Y ⟶ X)
          (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
          IsIso ((totalEtaleAugmentationAdjunction (U ⋙ Over.pullback f) Λ).derivedPlus.unit.app
            L))) := by
  sorry

end AlgebraicGeometry
