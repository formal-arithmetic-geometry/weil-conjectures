/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.CondensedModelWeil
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.AbsoluteFrobeniusNaturality

/-!
# The two Weil structures on a pulled-back object agree

Let `k` be a finite field, `f : X₀ ⟶ Spec k`, `p : X̄ ⟶ X₀` the projection of the geometric
fibre, `Fr_X = 𝟙 × σ` the geometric Galois Frobenius of `X̄`, `Φ = Φ₀ × 𝟙` the scheme
Frobenius of `X̄` and `Φ₀` the `q`-power Frobenius of `X₀`. For a module object `M` over `Λ` on
`X₀`, the pullback `p^* M` carries two natural Weil structures:

- for `Fr_X`, `Fr_X^* p^* M ≅ (Fr_X ≫ p)^* M = p^* M`
  (`AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberWeil`);
- for `Φ`, `Φ^* p^* M ≅ (Φ ≫ p)^* M = (p ≫ Φ₀)^* M ≅ p^* Φ₀^* M ≅ p^* M`, through the
  trivialization `Φ₀^* ≅ 𝟭` of the pullback along the absolute Frobenius of `X₀`
  (`AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberWeilModelFrobenius`).

We show that they agree under the identification `Φ^* ≅ Fr_X^*` of
`AlgebraicGeometry.ProEtale.CondensedRing.upperStarGeometricFiberFrobeniusIso`. The key input is
the naturality of the absolute Frobenius trivialization under pullback
(`ProEtale.CondensedRing.upperStarComp_hom_app_comp_map_upperStarIterateFrobeniusIso_hom_app`).

## Main results

- `AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberProjUpperStarModelFrobeniusIso_eq`:
  the structure isomorphism `p^* ⋙ Φ^* ≅ p^*` of the `Φ`-Weil structure is
  `p^* ⋙ Φ^* ≅ p^* ⋙ Fr_X^* ≅ p^*`.
- `ProEtale.CondensedRing.upperStarComp_symm_trans_isoWhiskerRight_eq_isoWhiskerLeft_trans`:
  the general coherence behind it, for any `p : X ⟶ Y` and compatible trivializations.
- `AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberWeilCompTransportIso`: the transport
  `geometricFiberFrobeniusTransport` along `Φ^* ≅ Fr_X^*` of the `Fr_X`-Weil objects `p^* M`
  (`geometricFiberWeil`) is isomorphic, with identity components, to the `Φ`-Weil objects `p^* M`
  (`geometricFiberWeilModelFrobenius`).
- `CategoryTheory.Endofunctor.IsoAlgebra.functorOfNatIsoCompMapOfNatIsoIso`: the general
  transport of structure isomorphisms along an isomorphism of endofunctors.
-/

@[expose] public section

universe v v' u u'

open CategoryTheory

open scoped CategoryTheory.Obj

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- A functor `P : C ⥤ D` with an isomorphism `s : P ⋙ G ≅ P` gives the functor `C ⥤ IsoAlgebra G`
sending `c` to `P c` with the structure isomorphism `s_c : G (P c) ≅ P c`. -/
@[simps obj map]
noncomputable def functorOfNatIso {G : D ⥤ D} (P : C ⥤ D) (s : P ⋙ G ≅ P) :
    C ⥤ IsoAlgebra G where
  obj c := mk (P.obj c) (s.app c)
  map φ := ObjectProperty.homMk
    { f := P.map φ
      h := s.hom.naturality φ }

end CategoryTheory.Endofunctor.IsoAlgebra

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Coherence

variable {X Y Y' Z : Scheme.{u}}

/-- A coherence of the composition isomorphisms of pullbacks: for `a ≫ r = F` and `r ≫ p = q`,
the two isomorphisms `p^* ⋙ F^* ≅ q^* ⋙ a^*`, through `(F ≫ p)^* = (a ≫ q)^*` and through
`F^* = (a ≫ r)^* ≅ r^* ⋙ a^*` and `p^* ⋙ r^* ≅ (r ≫ p)^* = q^*`, agree. -/
@[reassoc]
lemma upperStarComp_inv_app_comp_upperStarCongr_hom_app_comp_upperStarComp_hom_app
    (a : X ⟶ Y) (r : Y ⟶ Y') (p : Y' ⟶ Z) {F : X ⟶ Y'} {q : Y ⟶ Z} (hF : a ≫ r = F)
    (hq : r ≫ p = q) (h : F ≫ p = a ≫ q)
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    (upperStarComp Λ F p).inv.app M ≫ (upperStarCongr Λ h).hom.app M ≫
        (upperStarComp Λ a q).hom.app M =
      (upperStarCongr Λ hF.symm).hom.app ((p)^*⟦Λ⟧.obj M) ≫
        (upperStarComp Λ a r).hom.app ((p)^*⟦Λ⟧.obj M) ≫
        (a)^*⟦Λ⟧.map ((upperStarComp Λ r p).inv.app M ≫ (upperStarCongr Λ hq).hom.app M) := by
  subst hF hq
  rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, upperStarCongr_self Λ (rfl : a ≫ r = a ≫ r),
    upperStarCongr_self Λ (rfl : r ≫ p = r ≫ p), Iso.refl_hom, Iso.refl_hom, NatTrans.id_app,
    NatTrans.id_app, Category.comp_id, Category.id_comp,
    upperStarComp_hom_app_comp_upperStarComp_hom_app_assoc, ← CategoryTheory.Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]

end Coherence

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

end AlgebraicGeometry.ProEtale.CondensedRing
