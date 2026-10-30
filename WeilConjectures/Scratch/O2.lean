import WeilConjectures.Scratch.O1
import WeilConjectures.WeilSheaf.GeometricFiberPullback
import WeilConjectures.WeilSheaf.StalkCharpoly

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The identification `e^* ≅ (e⁻¹)_*` of underlying sheaves followed by the underlying morphism
of a morphism out of `(e⁻¹)_* N` precomposed with the identification of `ℓ`-adic sheaves. -/
lemma upperStarIsoLowerStarInv_hom_app_comp_hom {Y : Scheme.{u}} (e : Y ≅ Y)
    {N N' : AdicSheaf l Y} (g : (e.hom)^*ᵃ[l].obj N ⟶ N') :
    (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) e).hom.app N.X ≫
        ((adicUpperStarIsoLowerStarInv l e).inv.app N).hom ≫ g.hom = g.hom := by
  rw [adicUpperStarIsoLowerStarInv_inv_app_hom, Iso.hom_inv_id_app_assoc]


/-- `upperStarIsoLowerStarInv_hom_app_comp_hom` in the form of the Weil structures of pulled-back
sheaves. -/
lemma upperStarIsoLowerStarInv_hom_app_comp_forget_map {Y Z : Scheme.{u}} (e : Y ≅ Y)
    (p : Y ⟶ Z) (h : e.hom ≫ p = p) (M : AdicSheaf l Z) :
    (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) e).hom.app ((p)^*ᵃ[l].obj M).X ≫
        (AdicSheaf.forget Y).map ((adicUpperStarIsoLowerStarInv l e).inv.app ((p)^*ᵃ[l].obj M) ≫
          (adicUpperStarComp l e.hom p).inv.app M ≫ (adicUpperStarCongr l h).hom.app M) =
      ((adicUpperStarComp l e.hom p).inv.app M).hom ≫ ((adicUpperStarCongr l h).hom.app M).hom := by
  rw [Mod.forget_map, Mod.comp_hom', ← Mod.comp_hom']
  exact upperStarIsoLowerStarInv_hom_app_comp_hom e _

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]


end AlgebraicGeometry.WeilSheaf


namespace CategoryTheory.Endofunctor.IsoAlgebra

/-- The structure isomorphism of `IsoAlgebra.mk a Φ`, through `(mk a Φ).carrier = a`. -/
lemma mk_str_hom_comp_eqToHom {C : Type*} [Category* C] {G : C ⥤ C} (a : C) (Φ : G.obj a ≅ a)
    (h : (mk a Φ).carrier = a) :
    (mk a Φ).str.hom ≫ eqToHom h = G.map (eqToHom h) ≫ Φ.hom := by
  rw [eqToHom_refl, eqToHom_map, eqToHom_refl, Category.comp_id, Category.id_comp, mk_str]

end CategoryTheory.Endofunctor.IsoAlgebra

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

lemma geometricFiberPullback_obj_carrier_eq {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H) :
    (geometricFiberPullback (k₀ := k₀) hH).obj.carrier =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*ᵃ[l].obj H :=
  rfl

/-- The Weil structure of `p^* H` through `(p^* H).carrier = p^* H`. -/
lemma geometricFiberPullback_obj_str_hom_comp_eqToHom {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) :
    (geometricFiberPullback (k₀ := k₀) hH).obj.str.hom ≫
        eqToHom (geometricFiberPullback_obj_carrier_eq hH) =
      (frobeniusPullback k₀ l X).map (eqToHom (geometricFiberPullback_obj_carrier_eq hH)) ≫
        ((ProEtaleWeilSheaf.geometricFiberPullbackFrobeniusIso k₀ l X).app H).hom :=
  Endofunctor.IsoAlgebra.mk_str_hom_comp_eqToHom _ _ _

end AlgebraicGeometry.WeilSheaf
