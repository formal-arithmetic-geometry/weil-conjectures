/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap

/-! # Restriction property of module cohomology maps

Source: Stacks Project, Cohomology of Sheaves, Section 01F7, Remark 01FB.
(blueprint: lem-weil-pbc-module-cohomology-fmap-basic-restriction).
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
/-- Restriction property of the cohomology map induced by an h-map.
Source: Stacks Project, Cohomology of Sheaves, Tags 01F9, 01FA, 01FB;
Derived Categories, Tags 013P, 013S, 05TG.
(blueprint: lem-weil-pbc-module-cohomology-fmap-basic-restriction).

Proof (agent argument specialized from the parent node):
1. Both restriction and tensor pullback are left adjoint to pushforward along j.
   Uniqueness of left adjoints gives kappa and the unit equation
   rho followed by j_*(kappa) = eta. This applies to the chosen tensor adjunction too.
2. Choose injective resolutions I of G|_U and I' of j^*G, and J, J2 of G. Lift the
   identity of G from J to J2. The derived-functor comparison identifies the two source
   cohomologies, allowing both lifted unit maps to be computed from J.
3. Lift kappa^{-1} from I' to I, obtaining c. Its induced sections homology map computes
   H^p(kappa^{-1}). The auxiliary target K of the rho construction is bounded below
   injective, hence K-injective. Precomposition with the quasi-isomorphism lambda' in
   the eta construction is bijective on homotopy classes into K. Obtain e from its
   auxiliary complex K' to K with lambda' followed by e homotopic to j_*(c) followed
   by lambda. Sections and homology give the corresponding equality of vertical maps.
4. Precompose e followed after the lifted eta map with the augmentation of J. The unit
   equation, the equation for c on augmentations, and the preceding homotopy identify
   this composite with the lifted rho map. Uniqueness up to homotopy after the
   quasi-isomorphic augmentation of J then identifies the two horizontal maps on
   sections homology.
5. Cancel the invertible vertical sections homology maps. The defining formula for
   moduleCohomologyFMap now gives rho^* = eta^* followed by H^p(kappa^{-1}). Compose
   with H^p(kappa) and use functoriality and the inverse equations of kappa to obtain
   the displayed equality. No independence or functoriality theorem for h-maps is used.
-/
theorem moduleCohomologyFMap_basic_restriction {Y : Scheme.{u}}
    (G : SheafOfModules.{u} Y.ringCatSheaf) (p : ℕ) :
    ∀ (U : Y.Opens),
      ∃ κ : (restrictFunctor U.ι).obj G ≅ (tensorPullback U.ι).obj G,
        moduleCohomologyFMap U.ι ((restrictAdjunction U.ι).unit.app G) p ≫
            (forget₂ _ AddCommGrpCat).map
              (((U : Scheme).toRingedSpace.moduleCohomology p).map κ.hom) =
          moduleCohomologyFMap U.ι
            ((Classical.choose (exists_tensorPullbackAdjunction U.ι)).unit.app G) p := by
  sorry

end AlgebraicGeometry.Scheme.Modules
