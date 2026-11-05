/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedLocalIsomorphismSheaf
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedMorphismSheafComparison
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
public import WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Source-site evaluation of local derived isomorphisms

The local Isom presheaf formed using the small sites of source schemes is naturally
isomorphic to the presheaf formed using slice sites. This supplies canonical evaluation
on affine weakly contractible pro-etale objects, with no local-existence hypothesis.

Source: Stacks Project, Tags 09BV and 0F63; localization of the etale and pro-etale sites.
(blueprint: def-weil-pbc-source-derived-isomorphism-evaluation).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
universe u₀ u₁ u₂ u₃ u₄ v₀ v₁ v₂ v₃ v₄
namespace CategoryTheory.Functor
variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Category.{v₃} C₃] [Category.{v₄} C₄]
  [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory C₃] [HasDerivedCategory C₄]
  (Rv : C₀ ⥤ C₁) (Sv : C₁ ⥤ C₂) (Lv : C₀ ⥤ C₂)
  (Rw : C₀ ⥤ C₃) (Sw : C₃ ⥤ C₄) (Lw : C₀ ⥤ C₄)
  (M : C₃ ⥤ C₁) (L : C₄ ⥤ C₂)
  [Rv.Additive] [Sv.Additive] [Lv.Additive] [Rw.Additive]
  [Sw.Additive] [Lw.Additive] [M.Additive] [L.Additive]
  [PreservesFiniteLimits Rv] [PreservesFiniteColimits Rv]
  [PreservesFiniteLimits Sv] [PreservesFiniteColimits Sv]
  [PreservesFiniteLimits Lv] [PreservesFiniteColimits Lv]
  [PreservesFiniteLimits Rw] [PreservesFiniteColimits Rw]
  [PreservesFiniteLimits Sw] [PreservesFiniteColimits Sw]
  [PreservesFiniteLimits Lw] [PreservesFiniteColimits Lw]
  [PreservesFiniteLimits M] [PreservesFiniteColimits M]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (ev : Rv ⋙ Sv ≅ Lv) (ew : Rw ⋙ Sw ≅ Lw)
  (β : Rv ≅ Rw ⋙ M) (α : M ⋙ Sv ≅ Sw ⋙ L) (δ : Lv ≅ Lw ⋙ L)
  (h : ∀ K, ev.hom.app K ≫ δ.hom.app K =
    Sv.map (β.hom.app K) ≫ α.hom.app (Rw.obj K) ≫ L.map (ew.hom.app K))

section Conjugation
variable {P Q R S : Type*} [Category P] [Category Q] [Category R] [Category S]
    (SV : P ⥤ Q) (SW : R ⥤ S) (M : R ⥤ P) (L : S ⥤ Q)
    {Av Dv : P} {Aw Dw : R} {Aq Dq : Q} {As Ds : S}
    (δA : SV.obj Av ≅ Aq) (δD : SV.obj Dv ≅ Dq)
    (εA : SW.obj Aw ≅ As) (εD : SW.obj Dw ≅ Ds)
    (σA : Av ≅ M.obj Aw) (σD : Dv ≅ M.obj Dw)
    (cA : Aq ≅ L.obj As) (cD : Dq ≅ L.obj Ds)
    (α : M ⋙ SV ≅ SW ⋙ L)
    (hA : δA.hom ≫ cA.hom = SV.map σA.hom ≫ α.hom.app Aw ≫ L.map εA.hom)
    (hD : δD.hom ≫ cD.hom = SV.map σD.hom ≫ α.hom.app Dw ≫ L.map εD.hom)
end Conjugation

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]

end AlgebraicGeometry.Scheme
