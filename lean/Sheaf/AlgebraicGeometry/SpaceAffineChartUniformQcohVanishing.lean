/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q87
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceGlobalSectionsAmplitude
import Sheaf.AlgebraicGeometry.AlgebraicSpaceHigherDirectImageQuasiCoherent
import Sheaf.AlgebraicGeometry.SpaceAffineBaseHigherImageSections
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.CategoryTheory.Sites.ModuleDerivedEvaluationSlice
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison

/-! # Uniform quasi-coherent vanishing over affine étale charts

Source: Stacks Project, Cohomology of Spaces, Tags 073G and 08EX;
Derived Categories of Spaces, Tag 08FA, proof of (2)
(blueprint: lem-sfb-space-affine-chart-uniform-qcoh-vanishing).

Sections are taken on the actual enlarged-site object `X ×_Y V`. Right derivation
uses all module sheaves on the equivalent small affine model, in section universe `u`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

attribute [instance] SheafOfModules.isGrothendieckAbelian

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The additive functor `F_V(M) = M̃(X ×_Y V)`, forgetting the ring action.
Extension is the normalized inverse of restriction from the enlarged étale site.
Source: Stacks, Tags 03G1, 03H7 and 08FA, proof of (2)
(blueprint: lem-sfb-space-affine-chart-uniform-qcoh-vanishing). -/
def affineChartModuleSections (f : X ⟶ Y) (V : Y.EtaleSite) :
    X.Modules ⥤ AddCommGrpCat.{u} :=
  (smallEnlargedModuleEquivalence.{u, u} X).inverse ⋙
    SheafOfModules.toSheaf X.enlargedStructureSheaf ⋙
    sheafToPresheaf X.enlargedEtaleTopology AddCommGrpCat.{u} ⋙
    (evaluation X.EnlargedEtaleSiteᵒᵖ AddCommGrpCat.{u}).obj
      (op ((enlargedBaseChange f).obj ((enlargedSchemeInclusion Y).obj V)))

/-- The specified extension-and-evaluation functor is additive.
Source: Stacks, Tags 03H7 and 08FA, proof of (2)
(blueprint: lem-sfb-space-affine-chart-uniform-qcoh-vanishing).
Proof: restriction of modules to scheme objects is additive and an equivalence.
Its inverse preserves sums of morphisms, since they can be checked after faithful
restriction. Underlying additive sheaves and section evaluation preserve sums
sectionwise, so their composite does too. -/
@[instance] theorem affineChartModuleSections_additive (f : X ⟶ Y) (V : Y.EtaleSite) :
    (affineChartModuleSections f V).Additive := by
  sorry

/-- Additivity is retained when the same section functor is expressed on the small model.
Source: Stacks, Tags 039Z and 08FA, proof of (2)
(blueprint: lem-sfb-space-affine-chart-uniform-qcoh-vanishing).
Proof: small-model restriction is sectionwise additive and an equivalence. Its inverse
is additive by faithfulness of restriction. Compose with the additive extension-and-
evaluation functor above. Thus the right derived functor below is computed by applying
this precise functor to an injective resolution in all small-model module sheaves. -/
@[instance] theorem smallAffineChartModuleSections_additive
    (f : X ⟶ Y) (V : Y.EtaleSite) :
    (X.smallModuleEquivalence.inverse ⋙ affineChartModuleSections f V).Additive := by
  sorry

/-- There is one positive bound for module-injective derived evaluation on every affine
étale chart, for every quasi-coherent coefficient. No separation of `Y` is assumed.
Source: Stacks, Tags 073G and 08EX; Tag 08FA, proof of (2)
(blueprint: lem-sfb-space-affine-chart-uniform-qcoh-vanishing).

Proof:
1. Choose one surjective affine étale atlas `T → Y`. The affine-test hypothesis makes
   `Z = X ×_Y T` quasi-compact. Base change of the quasi-compact relative diagonal
   makes `Z → T` quasi-separated; since `T` is affine, `Z` is quasi-separated.
   Use lem-sfb-qc-space-affine-etale-atlas, lem-sfb-space-quasicompact-affine-tests,
   lem-weil-pbc-affine-scheme-qcqs, lem-sfb-space-qcqs-source-products and
   lem-trf-space-fibre-products-etale-covers. This does not require `Y` quasi-separated.
2. Apply lem-sfb-space-global-sections-amplitude to this one `Z`, obtaining `c ≥ 0`.
   Set `N = c + 1`. For every quasi-coherent `Q`, apply its bound to `Q[0]`.
   The module resolution comparison lem-sfb-module-resolution-derived-presheaf-comparison
   and lem-weil-pbc-bounded-below-injectives-kinjective identify the section complexes,
   so `H^p(Z,Q) = 0` for `p ≥ N`.
3. By lem-sfb-space-higher-direct-image-quasi-coherent and
   lem-sfb-space-affine-base-higher-image-sections, `R^p g_* Q` is quasi-coherent on
   the affine scheme `T` with zero sections. The equivalence
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence and the counit of
   lem-weil-pbc-affine-tilde-gamma-adjunction imply that this sheaf is zero.
4. Restrict a quasi-coherent `M` to `Z` using lem-sfb-space-module-pullback-quasicoherent.
   By lem-sfb-space-higher-image-etale-restriction, the restriction of `R^p f_* M` to
   `T` is zero. Every chart of `Y` pulls back this surjective étale cover, so sheaf
   separatedness gives `R^p f_* M = 0`.
5. For an arbitrary affine étale `V → Y`, apply the same restriction comparison to
   `W = X ×_Y V`. Its projection to `V` is qcqs by step 1. Tag 08EX, stated by
   lem-sfb-space-affine-base-higher-image-sections, identifies `H^p(W,M|_W)` with
   sections of the now zero higher direct image. The bound preceded both `V` and `M`.
6. The equivalence lem-trf-space-enlarged-etale-ringed-site-model preserves injective
   resolutions by lem-weil-pbc-equivalence-injective-resolutions. Apply
   lem-pe-ringed-site-derived-evaluation-slice and
   lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison to identify derived
   module evaluation at `W` with `H^p(W,M|_W)`. Restriction to the small affine model
   is another module equivalence and preserves the same injective computation.
   No underlying additive sheaf of an injective module is assumed injective.
   Empty spaces and zero coefficients have zero section complexes. Since `N ≥ 1`,
   natural degrees cover exactly the integer degrees asserted in the node. -/
theorem affineChartModuleSections_uniform_vanishing (f : X ⟶ Y)
    (hYqc : IsQuasiCompact Y.obj)
    (hfqc : IsQuasiCompactPresheafMap f.hom.hom)
    (hfqs : IsQuasiCompactPresheafMap (diagonalPresheafMap f.hom.hom)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ (V : Y.EtaleSite), IsAffine (Y.etaleForget.obj V) →
      ∀ (M : X.Modules), M.IsQuasicoherent → ∀ p : ℕ, N ≤ p →
        IsZero (((X.smallModuleEquivalence.inverse ⋙
          affineChartModuleSections f V).rightDerived p).obj
            (X.smallModuleRestriction.obj M)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
