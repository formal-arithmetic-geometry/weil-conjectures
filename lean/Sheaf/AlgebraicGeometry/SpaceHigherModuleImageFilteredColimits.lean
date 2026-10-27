/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Filtered.Basic

import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.AlgebraicGeometry.SpaceChartLimitEnlargedSections
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover

/-! # Higher module direct images preserve filtered colimits

Source: Stacks Project, Cohomology of Algebraic Spaces, Tag 07U6
(lemma-colimit-cohomology), with Cohomology on Sites, Tag 03FD
(blueprint: lem-sfb-space-higher-module-image-filtered-colimits).

Injective resolutions are taken in all module sheaves on the existing equivalent small
ringed model. Both the input and output of the higher-image functor are the original
module categories. The comparison is the unique map induced by the colimit legs.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The nonnegative higher direct image in all structure-module sheaves, transported
through actual restriction to the small affine ringed model.
Source: Stacks, Tags 03G8, 03FD and 07U6
(blueprint: lem-sfb-space-higher-module-image-filtered-colimits).
The specified direct image is conjugated by the existing restriction equivalences.
Mathlib's right derived functor applies it to injective resolutions. The explicit
resolution instance comes from the Grothendieck property of small-site module sheaves.
Equivalences preserve injectives and cohomology, so this computes the original R^p f_*.
No quasi-coherence condition is imposed. -/
def moduleHigherDirectImage {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (p : ℕ) : X.Modules ⥤ Y.Modules :=
  X.smallModuleRestriction ⋙
    (@Functor.rightDerived X.SmallModules _ Y.SmallModules _ _
      (@InjectiveResolution.instHasInjectiveResolutions X.SmallModules _ _
        (@IsGrothendieckAbelian.enoughInjectives _ _ _
          (SheafOfModules.isGrothendieckAbelian X.smallStructureRings)))
      _ (smallModuleDirectImage f) _ p) ⋙ Y.smallModuleEquivalence.inverse

/-- For a qcqs algebraic-space morphism, every nonnegative module higher direct image
commutes with filtered colimits. The source and target colimits are represented by
arbitrary colimit cocones `c` and `d`; their canonical comparison is `hd.desc` applied
to the image cocone, whose j-th leg is R^p f_* of `c.ι.app j`.
Source: Stacks, Cohomology of Algebraic Spaces, Tag 07U6; Cohomology on Sites, Tag 03FD
(blueprint: lem-sfb-space-higher-module-image-filtered-colimits).

Proof:
1. Use lem-trf-space-enlarged-etale-ringed-site-model and
lem-trf-space-chart-limit-enlarged-sections to identify the specified chart-limit
module direct image with that of the enlarged ringed site. Equivalences preserve
colimits, injectives and derived images. The nodes lem-weil-pbc-ring-sheaves-grothendieck,
lem-sp-grothendieck-enough-injectives and lem-weil-pbc-site-sheaves-enough-injectives
supply the module and abelian resolutions.
2. By lem-weil-pbc-module-sheaves-colimits-forgetful, forgetting scalars identifies
the module colimit with the abelian sheaf colimit, retaining every coprojection.
3. Restriction to a slice preserves colimits: the forgetful functor from the slice
is left adjoint to product with its defining object. Both functors are continuous.
Apply lem-weil-pbc-adjoint-continuous-restriction-adjunction and
lem-weil-pbc-left-adjoint-preserves-colimits, using
lem-trf-space-enlarged-site-scheme-density, lem-trf-space-chartwise-etale-permanence
and def-pur-localized-ringed-site.
4. For an affine etale V over Y, W = X times_Y V is quasi-compact by hqc.
For affine schemes T and T' over W, T times_V T' is affine. Its pullback along
the relative diagonal of f is T times_W T', quasi-compact by hqs. Thus W is qcqs;
no absolute finiteness assumption on X or Y is used.
5. Apply lem-weil-pbc-cohomology-over-object-localization and
lem-sfb-space-cohomology-filtered-colimit to W and the restricted abelian sheaves.
The natural module/abelian comparison of
lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison identifies this with
the module cohomology comparison, including its normalization in degree zero.
Naturality preserves the maps induced by all coprojections; forgotten injectives
need not be injective.
6. By lem-trf-space-enlarged-site-scheme-density and lem-a1-space-affine-etale-cover,
every enlarged target object has an affine etale cover. Apply
lem-sfb-ringed-site-higher-image-colimit-criterion using step 5 on each such affine.
It gives an isomorphism of module sheaves. Its composite with each colimit leg is
the higher direct image of the corresponding original leg, so uniqueness of the
colimit factorization identifies it with the displayed map `hd.desc`. -/
theorem isIso_moduleHigherDirectImage_filteredColimit
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hqc : MapIsQuasiCompact f.hom.hom)
    (hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (J : Type u) [SmallCategory J] [IsFiltered J]
    (M : J ⥤ X.Modules) (p : ℕ) (c : Cocone M) (hc : IsColimit c)
    (d : Cocone (M ⋙ moduleHigherDirectImage f p)) (hd : IsColimit d) :
    IsIso (hd.desc ((moduleHigherDirectImage f p).mapCocone c)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
