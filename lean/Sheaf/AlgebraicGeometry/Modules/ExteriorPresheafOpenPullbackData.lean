module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf

/-! Component data for exterior presheaf pullback. -/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Component isomorphisms and their naturality for the exterior presheaf pullback.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
(blueprint: lem-sc-exterior-presheaf-open-pullback-data).

The component map sends a pure wedge to the wedge of the corresponding restricted
sections, using the canonical ring isomorphism on sections.  Its inverse uses the
inverse ring isomorphism.  The exterior-power universal property proves that these
maps are linear and inverse, while the defining restriction formula proves naturality.
-/
theorem exteriorPresheaf_open_pullback_data {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) :
    ∃ (app : ∀ V : U.toScheme.Opensᵒᵖ,
      ((PresheafOfModules.pullback.{v} U.ι.toRingCatSheafHom.hom).obj
        (exteriorSheafPresheaf M n)).obj V ≅
        (exteriorSheafPresheaf (M.restrict U.ι) n).obj V),
      ∀ {V W : U.toScheme.Opensᵒᵖ} (f : V ⟶ W),
        ((PresheafOfModules.pullback.{v} U.ι.toRingCatSheafHom.hom).obj
          (exteriorSheafPresheaf M n)).map f ≫
            (ModuleCat.restrictScalars
              ((U.toScheme.ringCatSheaf.obj.map f).hom)).map (app W).hom =
          (app V).hom ≫ (exteriorSheafPresheaf (M.restrict U.ι) n).map f := by
  sorry

end AlgebraicGeometry.Scheme.Modules
