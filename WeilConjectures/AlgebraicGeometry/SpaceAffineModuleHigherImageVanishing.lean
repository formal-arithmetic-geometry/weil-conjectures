/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ChartwiseEtalePermanence
import WeilConjectures.AlgebraicGeometry.SmallEnlargedEtaleModules
import WeilConjectures.AlgebraicGeometry.SpaceChartLimitEnlargedSections
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.AlgebraicGeometry.SiteHigherDirectImageSheafifiedPresheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Affine algebraic-space module higher direct images vanish

Source: Stacks Project, Cohomology of Algebraic Spaces, Tag 073H;
Cohomology on Sites, Tags 03FD and 072W
(blueprint: lem-sfb-space-affine-module-higher-image-vanishing).

Right derived functors are computed in ALL structure-module sheaves, using the
existing small affine ringed model and its specified restriction equivalence.
The result is transported back to the original target module category. The explicit
injective-resolution instance is obtained from the small model's Grothendieck property;
no existence of resolutions or finiteness assumption is imposed on the spaces.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Positive module higher direct images of a quasi-coherent module along an affine
morphism of algebraic spaces vanish, without Noetherian or finiteness assumptions.

Source: Stacks Project, Cohomology of Algebraic Spaces, Tag 073H, with the module/abelian
comparison of Cohomology on Sites, Tag 03FD, and the higher-image formula, Tag 072W
(blueprint: lem-sfb-space-affine-module-higher-image-vanishing).

The small-model equivalence is actual restriction to affine etale charts. Conjugating
`moduleDirectImage a` by it gives `smallModuleDirectImage a`. Its right derived functor
is computed by injective resolutions in the full module category, and its output is
transported back by the target equivalence. This is the original module higher image.
`q : ℕ` with `0 < q` ranges over exactly the positive integers of the source.

Proof:
1. By lem-weil-pbc-ring-sheaves-grothendieck and lem-sp-grothendieck-enough-injectives,
choose a module injective resolution of M. By def-sp-injective-resolutions and the exact
forgetful functor of lem-weil-pbc-module-sheaves-colimits-forgetful, forgetting gives an
exact abelian resolution. The small model transports these same resolutions without
changing the module section universe; abelian sheaves also have enough injectives by
lem-weil-pbc-site-sheaves-enough-injectives.
2. For a target etale chart T, representability gives a scheme U_T = V times_W T.
Use lem-trf-space-chartwise-etale-permanence,
lem-trf-space-enlarged-etale-ringed-site-model and
lem-trf-space-chart-limit-enlarged-sections to identify direct-image sections with
sections on U_T, with their prescribed scalar restriction. Thus forgetting the module
image complex gives the abelian image of the forgotten resolution.
3. By lem-sc-injective-module-abelian-acyclic-zariski, each injective module term has
zero positive abelian cohomology on every U_T. Apply
lem-weil-pbc-site-higher-direct-image-sheafified-presheaf and
def-weil-pbc-sheafification: every forgotten term is abelian-direct-image acyclic.
4. Apply the acyclic-resolution criterion lemma-weil-pbc-leray-acyclicity to the
forgotten resolution. The node def-sp-injective-resolutions and
lem-weil-pbc-exact-functor-complex-cohomology identify the underlying abelian sheaf of
the module higher image with the abelian higher image of the underlying sheaf. This
uses acyclicity; forgetting need not preserve injectives.
5. The node lem-sfb-space-affine-higher-direct-image-vanishing makes the latter higher image
zero, since a is affine and M is quasi-coherent. Faithfulness of the exact forgetful
functor in lem-weil-pbc-module-sheaves-colimits-forgetful reflects the zero identity,
so the module higher image is zero. Transport through the small-model equivalence
retains this zero object in W.Modules. -/
theorem isZero_moduleHigherDirectImage_of_affine
    {S : Scheme.{u}} {V W : AlgebraicSpace S} (a : V ⟶ W)
    (ha : IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left) a.hom.hom)
    (M : V.Modules) (hM : M.IsQuasicoherent) (q : ℕ) (hq : 0 < q) :
    IsZero (W.smallModuleEquivalence.inverse.obj
      ((@Functor.rightDerived V.SmallModules _ W.SmallModules _ _
        (@InjectiveResolution.instHasInjectiveResolutions V.SmallModules _ _
          (@IsGrothendieckAbelian.enoughInjectives _ _ _
            (SheafOfModules.isGrothendieckAbelian V.smallStructureRings)))
        _ (smallModuleDirectImage a) _ q).obj (V.smallModuleRestriction.obj M))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
