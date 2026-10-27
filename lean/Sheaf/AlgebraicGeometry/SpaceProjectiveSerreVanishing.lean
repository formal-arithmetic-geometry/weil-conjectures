/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.SpaceProjectiveTwist
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.NoetherianAffineAtlasRelation
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.ProjectiveSpaceTwistGluedIdentification
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import Sheaf.AlgebraicGeometry.RelativeSerreVanishing
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Projective Serre vanishing over an algebraic space

Source: Stacks Project, Cohomology of Algebraic Spaces, Tag 08AQ,
lemma-kill-by-twisting (blueprint: lem-sfb-space-projective-serre-vanishing).

The projective space and its twist are the canonical base-change constructions.
Their small-model module realizations use the existing restriction equivalence;
higher images are right derived in all module sheaves, using injective resolutions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Extend the existing positive tensor powers by the structure module in degree zero.
This uses the existing small-model sheaf tensor, with no change of coefficient universe.
Source: Stacks, Modules on Sites, Section 03EK, and Tag 08AQ
(blueprint: lem-sfb-space-projective-serre-vanishing). -/
def projectiveSerreTensorPower {S : Scheme.{u}} (X : AlgebraicSpace S) (L : X.SmallModules) :
    ℕ → X.SmallModules
  | 0 => SheafOfModules.unit X.smallStructureRings
  | d + 1 => SheafOfModules.positiveTensorPower X.smallStructureSheaf L (d + 1)
      (Nat.zero_lt_succ d)

/-- Serre vanishing for a closed immersion into projective space over a Noetherian space.
The three hypotheses hln, hqc and hqs mean locally Noetherian charts, quasi-compactness
of the point space, and quasi-compactness of the absolute diagonal, respectively.
The two conditions on F are exactly quasi-coherence and coherence on every scheme chart.
The structure map f is the composite of the immersion and the specified projection.
The right derived functor is in all modules on the equivalent small ringed model;
transporting its value back gives the higher image on the original small etale site.
Source: Stacks, Tag 08AQ, lemma-kill-by-twisting
(blueprint: lem-sfb-space-projective-serre-vanishing).

Proof:
1. Choose an affine surjective etale atlas U -> Y, by
   lem-sfb-qc-space-affine-etale-atlas. The Noetherian affine-atlas relation theorem
   makes U a Noetherian scheme. For the empty base take the empty atlas and bound zero.
2. Base change the immersion to U. By the fibre-product lemma it is a scheme closed
   immersion into P^n_U. Projective space is proper, and so is the composite with a
   closed immersion. Thus the map to U is quasi-compact and separated.
3. Restrict F to its coherent Zariski module on X_U. The Zariski/etale equivalence
   preserves pullback and line modules. The glued-twist identification identifies the
   fixed standard twist with the graded S(1) twist. The projective-ample-invertible
   lemma makes its restriction invertible and ample over every affine open of U.
4. Apply lem-pc-relative-kill-by-twisting on this one Noetherian affine atlas. It
   supplies a single integer bound for all positive degrees; increase it to max(0,e).
5. For d above this bound, pullback-tensor compatibility identifies the restricted
   F tensor L^d with the scheme twist. The higher-image etale-restriction comparison
   and the scheme etale/Zariski higher-image comparison identify the restricted
   higher image with the zero sheaf obtained in step 4.
6. Every test T -> Y has the surjective etale cover T times_Y U. Sections of the
   higher image restrict to zero there, hence are zero by sheaf separatedness.
   Thus the higher image is zero, with the same bound for every positive degree. -/
theorem exists_isZero_projective_higherDirectImage_twist
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (hln : ∀ T : Y.EtaleSite, IsLocallyNoetherian (Y.etaleForget.obj T))
    (hqc : CompactSpace (Point Y.obj.obj))
    (hqs : IsAbsolutelyQuasiSeparated Y)
    (n : ℕ) (i : X ⟶ projectiveSpaceOver Y n)
    (hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom)
    (F : X.Modules) (hF : F.IsQuasicoherent)
    (hFc : ∀ T : X.EtaleSite,
      RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
        ((X.schemeRestriction T).obj F)) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ q : ℕ, 0 < q →
      IsZero (Y.smallModuleEquivalence.inverse.obj
        ((@Functor.rightDerived X.SmallModules _ Y.SmallModules _ _
          (@InjectiveResolution.instHasInjectiveResolutions X.SmallModules _ _
            (@IsGrothendieckAbelian.enoughInjectives _ _ _
              (SheafOfModules.isGrothendieckAbelianOfUniverses.{u, u, u, u}
                X.smallEtaleModelTopology X.smallStructureRings)))
          _ (smallModuleDirectImage (i ≫ projectiveSpaceProjection Y n)) _ q).obj
            (X.smallModuleRestriction.obj F ⊗
              projectiveSerreTensorPower X (X.smallModuleRestriction.obj
                ((moduleTensorPullback i).obj (projectiveSpaceTwistOne Y n))) d))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
