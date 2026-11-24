/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # Affine coherent sheaves have associated-module presentations

## References

* Stacks Project, Tags 01IB and 01XZ
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Transport the affine tilde counit along the canonical affine chart (Stacks, Tags 01IB and 01XZ).
-/
theorem affine_coherent_tilde_presentation
    {X : Scheme.{u}} [IsNoetherian X] [IsAffine X] (H : CoherentModules X) :
    ∃ P : ModuleCat.{u} Γ(X, ⊤),
      Nonempty ((tilde.functor Γ(X, ⊤) ⋙
        Scheme.Modules.pullback X.isoSpec.hom).obj P ≅ H.obj) := by
  have hH := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    X H.obj).mp H.property
  have : H.obj.IsQuasicoherent := hH.1
  let M := H.obj.restrict X.isoSpec.inv
  have : M.IsQuasicoherent := inferInstance
  let P := (moduleSpecΓFunctor (R := Γ(X, ⊤))).obj M
  let e : (tilde.functor Γ(X, ⊤)).obj P ≅ M := asIso M.fromTildeΓ
  refine ⟨P, ⟨?_⟩⟩
  exact ((Scheme.Modules.restrictFunctorIsoPullback X.isoSpec.hom).app _).symm ≪≫
    (Scheme.Modules.restrictFunctor X.isoSpec.hom).mapIso e ≪≫
    ((Scheme.Modules.restrictFunctorComp X.isoSpec.hom X.isoSpec.inv).app H.obj).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr X.isoSpec.hom_inv_id).app H.obj ≪≫
    (Scheme.Modules.restrictFunctorId (X := X)).app H.obj

end AlgebraicGeometry
