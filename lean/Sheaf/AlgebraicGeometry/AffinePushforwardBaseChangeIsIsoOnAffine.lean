module

public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false

/-- Affine-local section computation for affine pushforward base change.
The map on sections over every affine open is bijective by identifying all four schemes
with spectra of rings and computing the canonical tensor-product map.
(blueprint: lem-weil-pbc-affine-pushforward-base-change-app-bijective)
Proof: Restrict the cartesian square to an affine open, identify it with spectra of rings,
and calculate the map as the canonical tensor-product isomorphism. -/
theorem affinePushforward_baseChange_app_bijective {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [IsAffineHom f]
    (F : X.Modules) [F.IsQuasicoherent] :
    ∀ V : S'.Opens, IsAffineOpen V →
      Function.Bijective ((moduleBaseChangeMap f f' g g' sq.w F).app V) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
