/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-!
# Pushforward and restriction to an open subscheme of the base

Let `g : T' ⟶ T` be an open immersion and let `f' : X' ⟶ T'` and `g' : X' ⟶ X` be the base change
of `f : X ⟶ T` along `g`. Then restricting the pushforward `f_* M` to `T'` is the pushforward of
the restriction of `M` to `X'`: both have sections `Γ(M, f⁻¹(g(W))) = Γ(M, g'(f'⁻¹(W)))` over an
open `W` of `T'`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.pushforwardRestrictIso`: the isomorphism
  `(f_* M)|_{T'} ≅ f'_* (M|_{X'})`, natural in `M`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X T X' T' : Scheme.{u}} (f : X ⟶ T) (g : T' ⟶ T) [IsOpenImmersion g] (g' : X' ⟶ X)
  [IsOpenImmersion g'] (f' : X' ⟶ T') (sq : IsPullback g' f' f g)

include sq in
/-- In a cartesian square whose horizontal maps `g'` and `g` are open immersions, the ring maps
`Γ(T', W) ⟶ Γ(T, g(W)) ⟶ Γ(X, f⁻¹(g(W)))` and `Γ(T', W) ⟶ Γ(X', f'⁻¹(W)) ⟶ Γ(X, g'(f'⁻¹(W)))`
agree, the opens `f⁻¹(g(W))` and `g'(f'⁻¹(W))` of `X` being equal. -/
lemma IsOpenImmersion.appIso_inv_app_map_eq_of_isPullback (W : T'.Opens) :
    (g.appIso W).inv ≫ f.app (g ''ᵁ W) ≫ X.presheaf.map (eqToHom
      (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback sq.flip W)).op =
      f'.app W ≫ (g'.appIso (f' ⁻¹ᵁ W)).inv := by
  rw [IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq f' g (g' ≫ f) sq.w W]
  simp only [Category.assoc, Scheme.Hom.comp_app]
  congr 2
  rw [← cancel_mono (g'.appIso _).hom, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, Scheme.Hom.appIso_hom, Scheme.Hom.naturality_assoc]
  simp [eqToHom_map, eqToHom_unop, eqToHom_op]

namespace Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- **Pushforward commutes with restriction to an open subscheme of the base.** For the base
change `f' : X' ⟶ T'`, `g' : X' ⟶ X` of `f : X ⟶ T` along an open immersion `g : T' ⟶ T`, the
restriction of `f_* M` to `T'` is `f'_* (M|_{X'})`, naturally in `M`. -/
noncomputable def pushforwardRestrictIso :
    pushforward f ⋙ restrictFunctor g ≅ restrictFunctor g' ⋙ pushforward f' :=
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardCongr₂ _ (NatIso.ofComponents (fun W ↦ eqToIso
      (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback sq.flip W))
        (fun _ ↦ rfl)) (by
      ext W x
      exact congr($(IsOpenImmersion.appIso_inv_app_map_eq_of_isPullback f g g' f' sq W.unop) x))
    ≪≫ (SheafOfModules.pushforwardComp _ _).symm

instance (f : X ⟶ T) [IsOpenImmersion f] : PreservesFiniteColimits (restrictFunctor f) :=
  have := (restrictAdjunction f).leftAdjoint_preservesColimits.{0, 0}
  inferInstance

instance (f : X ⟶ T) [IsOpenImmersion f] : PreservesFiniteLimits (restrictFunctor f) :=
  inferInstance

instance (f : X ⟶ T) [IsOpenImmersion f] : (restrictFunctor f).Additive :=
  Functor.additive_of_preserves_binary_products _

end Scheme.Modules

end AlgebraicGeometry
