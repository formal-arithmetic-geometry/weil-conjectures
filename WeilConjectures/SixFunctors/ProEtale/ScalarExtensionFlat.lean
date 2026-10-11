/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.FlatExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.FlatModuleCat

/-!
# Extension of scalars of pro-étale sheaves preserves flatness

For a finite free algebra `S` over a Noetherian ring `R`, extension of scalars
`S ⊗_R - : Sh(X_proét, R) ⥤ Sh(X_proét, S)` sends flat sheaves to flat sheaves
(`AlgebraicGeometry.ProEtale.preservesFlat_sheafExtendScalars`), by the relation criterion
`CategoryTheory.Sheaf.flat_presheafToSheaf_obj_comp_extendScalars`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] [Algebra R S] (X : Scheme.{u})

/-- An `R`-algebra `S`, as an `R`-module, is `S` with the `R`-module structure obtained by
restricting scalars along `algebraMap R S`. -/
noncomputable def _root_.ModuleCat.restrictScalarsAlgebraMapSelfLinearEquiv :
    S ≃ₗ[R] (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) where
  toFun s := s
  invFun s := s
  map_add' _ _ := rfl
  map_smul' r s := Algebra.smul_def r s
  left_inv _ := rfl
  right_inv _ := rfl

set_option synthInstance.maxHeartbeats 400000 in
-- the instances `WEqualsLocallyBijective` and `HasSheafCompose` on the small pro-étale sites
-- take long to synthesize
/-- Extension of scalars along a finite free algebra over a Noetherian ring preserves flat
pro-étale sheaves. -/
instance preservesFlat_sheafExtendScalars [Nontrivial R] [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Finite R S] [Module.Free R S] :
    (sheafExtendScalars (algebraMap R S) X).PreservesFlat where
  flat_obj hF := Sheaf.flat_presheafToSheaf_obj_comp_extendScalars (algebraMap R S)
    ((Module.finBasis R S).map ModuleCat.restrictScalarsAlgebraMapSelfLinearEquiv) hF

end AlgebraicGeometry.ProEtale
