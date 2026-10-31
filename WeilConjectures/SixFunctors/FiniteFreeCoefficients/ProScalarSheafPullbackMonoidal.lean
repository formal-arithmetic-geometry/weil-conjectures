/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.ProScalarPullbackCochainData
import WeilConjectures.CategoryTheory.Sites.SheafAdjunctionUnitProjection
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import WeilConjectures.CategoryTheory.Monoidal.Conjugate

/-! # The monoidal ordinary scalar/pullback comparison on the pro-etale site

Source: Stacks Tags 07A4 and 07A7. The direct-image/restriction comparison is
objectwise the identity and is monoidal. Its conjugate through the two monoidal
composite adjunctions is therefore monoidal as well.
(blueprint: new-sf-pro-scalar-sheaf-pullback-monoidal). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
attribute [local irreducible] ProEtale.upperStar

/-- The ordinary pro-etale scalar/pullback comparison preserves the oplax tensor maps.
Source: Stacks 07A4 and 07A7.
Proof: the sheaf pushforward/compose comparison is monoidal. Inversion preserves
monoidality, and conjugation along the two monoidal composite adjunctions takes
that inverse to the displayed ordinary scalar/pullback comparison.
(blueprint: new-sf-pro-scalar-sheaf-pullback-monoidal). -/
theorem pro_scalar_sheaf_pullback_monoidal
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Y X : Scheme.{u}} (f : Y ⟶ X)
    (M N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (pro_scalar_sheaf_pullback_iso φ f).hom.app (M ⊗ N) ≫
        (finiteVerdierOrdinaryExtension (Scheme.ProEt.topology Y) φ).map
          (Functor.OplaxMonoidal.δ (ProEtale.upperStar (ModuleCat.{u + 1} A) f) M N) ≫
        Functor.OplaxMonoidal.δ
          (finiteVerdierOrdinaryExtension (Scheme.ProEt.topology Y) φ)
          ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).obj M)
          ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).obj N) =
      (ProEtale.upperStar (ModuleCat.{u + 1} B) f).map
          (Functor.OplaxMonoidal.δ
            (finiteVerdierOrdinaryExtension (Scheme.ProEt.topology X) φ) M N) ≫
        Functor.OplaxMonoidal.δ (ProEtale.upperStar (ModuleCat.{u + 1} B) f)
          ((finiteVerdierOrdinaryExtension (Scheme.ProEt.topology X) φ).obj M)
          ((finiteVerdierOrdinaryExtension (Scheme.ProEt.topology X) φ).obj N) ≫
        ((pro_scalar_sheaf_pullback_iso φ f).hom.app M ⊗ₘ
          (pro_scalar_sheaf_pullback_iso φ f).hom.app N) := by
  simpa only [Functor.OplaxMonoidal.comp_δ, Category.assoc] using
    (NatTrans.IsMonoidal.δ_comp_tensorHom
      (pro_scalar_sheaf_pullback_iso φ f).hom M N).symm

end WeilConjectures.FiniteFreeCoefficients
