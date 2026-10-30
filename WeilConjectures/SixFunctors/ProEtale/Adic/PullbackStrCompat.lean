/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobenius
public import WeilConjectures.SixFunctors.ProEtale.Adic.UpperStarFactor

/-!
# Compatibilities of pulled-back Weil structures with pieces

Let `φ` be an automorphism of `W` and `p : W ⟶ S` with `φ ≫ p = p`, so that the pullback `p^* H`
of an `ℓ`-adic sheaf carries the canonical Weil structure `φ^* p^* H ≅ (φ ≫ p)^* H = p^* H`
(`AlgebraicGeometry.ProEtale.pullbackStrIso`, in the pushforward convention
`φ^* = (φ⁻¹)_*`). For pieces `a, b : Z ⟶ W` over `q : Z ⟶ S` with `a ≫ φ = b` (or
`a ≫ φ = ψ ≫ j`), the identifications `a^* p^* H ≅ q^* H` are compatible with these Weil
structures (`AlgebraicGeometry.ProEtale.pullbackStr_compat`,
`AlgebraicGeometry.ProEtale.pullbackStr_compat_β`): this is the associativity of the
factorisation isomorphisms of pullbacks. The statements take all the data up to equality, so
that they can be instantiated without the kernel unfolding pullbacks.
-/

@[expose] public section

universe u

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

/-- The identification `a^* p^* H ≅ q^* H` along a piece `a` with `a ≫ p = q` is compatible with
the Weil structure `φ^* p^* H ≅ p^* H` and the identification `φ^* ⋙ a^* ≅ b^*` for
`a ≫ φ = b`. -/
lemma pullbackStr_compat {Z W S : Scheme.{u}} (φ : W ≅ W) (p : W ⟶ S) (hφ : φ.hom ≫ p = p)
    (a b : Z ⟶ W) (q : Z ⟶ S) (hab : a ≫ φ.hom = b) (ha : a ≫ p = q) (hb : b ≫ p = q)
    (H : AdicSheaf l S) :
    (a)^*ᵃ[l].map ((adicUpperStarIsoLowerStarInv l φ).inv.app ((p)^*ᵃ[l].obj H) ≫
        (adicUpperStarFactorApp l hφ H).inv) ≫ (adicUpperStarFactorApp l ha H).inv =
    (a)^*ᵃ[l].map ((adicUpperStarIsoLowerStarInv l φ).inv.app ((p)^*ᵃ[l].obj H)) ≫
      (adicUpperStarComp l a φ.hom).inv.app ((p)^*ᵃ[l].obj H) ≫
      (adicUpperStarCongr l hab).hom.app ((p)^*ᵃ[l].obj H) ≫
        (adicUpperStarFactorApp l hb H).inv := by
  simp only [adicUpperStarFactorApp_inv]
  rw [← adicUpperStarFactor_inv_app_assoc, Functor.map_comp, Category.assoc,
    map_adicUpperStarFactor_inv_app_comp_inv_app hφ ha hab hb]

/-- The last-piece version of `pullbackStr_compat`, for `a ≫ φ = ψ ≫ j`. -/
lemma pullbackStr_compat_last {Z W S : Scheme.{u}} (φ : W ≅ W) (ψ : Z ≅ Z) (p : W ⟶ S) (q : Z ⟶ S)
    (hφ : φ.hom ≫ p = p) (hψ : ψ.hom ≫ q = q) (a j : Z ⟶ W) (h : a ≫ φ.hom = ψ.hom ≫ j)
    (ha : a ≫ p = q) (hj : j ≫ p = q) (H : AdicSheaf l S) :
    (a)^*ᵃ[l].map ((adicUpperStarIsoLowerStarInv l φ).inv.app ((p)^*ᵃ[l].obj H) ≫
        (adicUpperStarFactorApp l hφ H).inv) ≫ (adicUpperStarFactorApp l ha H).inv =
    (a)^*ᵃ[l].map ((adicUpperStarIsoLowerStarInv l φ).inv.app ((p)^*ᵃ[l].obj H)) ≫
      (adicUpperStarComp l a φ.hom).inv.app ((p)^*ᵃ[l].obj H) ≫
      (adicUpperStarCongr l h).hom.app ((p)^*ᵃ[l].obj H) ≫
      (adicUpperStarComp l ψ.hom j).hom.app ((p)^*ᵃ[l].obj H) ≫
      (adicUpperStarIsoLowerStarInv l ψ).hom.app ((j)^*ᵃ[l].obj ((p)^*ᵃ[l].obj H)) ≫
      (ψ.inv)_*ᵃ[l].map (adicUpperStarFactorApp l hj H).inv ≫
      (adicUpperStarIsoLowerStarInv l ψ).inv.app ((q)^*ᵃ[l].obj H) ≫
        (adicUpperStarFactorApp l hψ H).inv := by
  have e' : (ψ.hom ≫ j) ≫ p = q := by rw [Category.assoc, hj, hψ]
  simp only [adicUpperStarFactorApp_inv]
  rw [← adicUpperStarFactor_inv_app_assoc, ← adicUpperStarFactor_rfl, Functor.map_comp]
  simp only [Category.assoc]
  rw [← (adicUpperStarIsoLowerStarInv l ψ).hom.naturality_assoc, Iso.hom_inv_id_app_assoc,
    map_adicUpperStarFactor_inv_app_comp_inv_app hj hψ rfl e', Iso.hom_inv_id_app_assoc,
    map_adicUpperStarFactor_inv_app_comp_inv_app hφ ha h e']

variable {l} in
/-- The canonical Weil structure `φ^* p^* H ≅ (φ ≫ p)^* H = p^* H` for `φ ≫ p = p`, in the
pushforward convention `φ^* = (φ⁻¹)_*`. -/
noncomputable def pullbackStrIso {W S : Scheme.{u}} (φ : W ≅ W) (p : W ⟶ S)
    (hφ : φ.hom ≫ p = p) : (p)^*ᵃ[l] ⋙ (φ.inv)_*ᵃ[l] ≅ (p)^*ᵃ[l] :=
  Functor.isoWhiskerLeft _ (adicUpperStarIsoLowerStarInv l φ).symm ≪≫
    (adicUpperStarComp l _ _).symm ≪≫ adicUpperStarCongr l hφ

/-- The canonical Weil structure is the identification `φ^* p^* H ≅ p^* H` after
`(φ⁻¹)_* ≅ φ^*`. -/
lemma pullbackStrIso_hom_app {W S : Scheme.{u}} (φ : W ≅ W) (p : W ⟶ S) (hφ : φ.hom ≫ p = p)
    (H : AdicSheaf l S) :
    (pullbackStrIso φ p hφ).hom.app H =
      (adicUpperStarIsoLowerStarInv l φ).inv.app ((p)^*ᵃ[l].obj H) ≫
        (adicUpperStarFactorApp l hφ H).inv := by
  rw [adicUpperStarFactorApp_inv, adicUpperStarFactor_inv_app]
  simp only [pullbackStrIso, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom]

/-- The components of the identification `β` of the last piece of the cyclic decomposition. -/
lemma pullbackStr_β_hom_app {Z W : Scheme.{u}} (φ : W ≅ W) (ψ : Z ≅ Z) (a j : Z ⟶ W)
    (h : a ≫ φ.hom = ψ.hom ≫ j) (X : AdicSheaf l W) :
    (Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l φ).symm (a)^*ᵃ[l] ≪≫
        (adicUpperStarComp l a φ.hom).symm ≪≫ adicUpperStarCongr l h ≪≫
        adicUpperStarComp l ψ.hom j ≪≫
        Functor.isoWhiskerLeft (j)^*ᵃ[l] (adicUpperStarIsoLowerStarInv l ψ)).hom.app X =
    (a)^*ᵃ[l].map ((adicUpperStarIsoLowerStarInv l φ).inv.app X) ≫
      (adicUpperStarComp l a φ.hom).inv.app X ≫ (adicUpperStarCongr l h).hom.app X ≫
      (adicUpperStarComp l ψ.hom j).hom.app X ≫
      (adicUpperStarIsoLowerStarInv l ψ).hom.app ((j)^*ᵃ[l].obj X) :=
  rfl

/-- `pullbackStr_compat_last` in the form of the compatibility with `β` of
`CategoryTheory.Endofunctor.IsoAlgebra.CyclicDecomposition.functorObjIsoMk`. -/
lemma pullbackStr_compat_last' {Z W S : Scheme.{u}} (φ : W ≅ W) (ψ : Z ≅ Z) (p : W ⟶ S)
    (q : Z ⟶ S) (hφ : φ.hom ≫ p = p) (hψ : ψ.hom ≫ q = q) (a j : Z ⟶ W)
    (h : a ≫ φ.hom = ψ.hom ≫ j) (ha : a ≫ p = q) (hj : j ≫ p = q) (H : AdicSheaf l S) :
    (a)^*ᵃ[l].map ((pullbackStrIso φ p hφ).hom.app H) ≫ (adicUpperStarFactorApp l ha H).symm.hom =
    (Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l φ).symm (a)^*ᵃ[l] ≪≫
        (adicUpperStarComp l a φ.hom).symm ≪≫ adicUpperStarCongr l h ≪≫
        adicUpperStarComp l ψ.hom j ≪≫
        Functor.isoWhiskerLeft (j)^*ᵃ[l] (adicUpperStarIsoLowerStarInv l ψ)).hom.app
          ((p)^*ᵃ[l].obj H) ≫
      (ψ.inv)_*ᵃ[l].map (adicUpperStarFactorApp l hj H).symm.hom ≫
      ((pullbackStrIso ψ q hψ).hom.app H) := by
  rw [pullbackStrIso_hom_app, pullbackStrIso_hom_app, pullbackStr_β_hom_app, Iso.symm_hom,
    Iso.symm_hom]
  simp only [Category.assoc]
  exact pullbackStr_compat_last l φ ψ p q hφ hψ a j h ha hj H

/-- `pullbackStr_compat` for an object `X = p^* H` and a Weil structure `s` given up to these
identifications. -/
lemma pullbackStr_compat_of_eq {Z W S : Scheme.{u}} (φ : W ≅ W) (p : W ⟶ S) (hφ : φ.hom ≫ p = p)
    (a b : Z ⟶ W) (q : Z ⟶ S) (hab : a ≫ φ.hom = b) (ha : a ≫ p = q) (hb : b ≫ p = q)
    (H : AdicSheaf l S) (X : AdicSheaf l W) (hX : X = (p)^*ᵃ[l].obj H)
    (s : (φ.inv)_*ᵃ[l].obj X ⟶ X) (hs : HEq s ((pullbackStrIso φ p hφ).hom.app H)) :
    (a)^*ᵃ[l].map s ≫
        (eqToIso (congrArg (a)^*ᵃ[l].obj hX) ≪≫ (adicUpperStarFactorApp l ha H).symm).hom =
      (Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l φ).symm (a)^*ᵃ[l] ≪≫
        (adicUpperStarComp l a φ.hom).symm ≪≫ adicUpperStarCongr l hab).hom.app X ≫
      (eqToIso (congrArg (b)^*ᵃ[l].obj hX) ≪≫ (adicUpperStarFactorApp l hb H).symm).hom := by
  subst hX
  obtain rfl := eq_of_heq hs
  simp only [eqToIso_refl, Iso.refl_trans, Iso.symm_hom, pullbackStrIso_hom_app, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.assoc]
  exact pullbackStr_compat l φ p hφ a b q hab ha hb H

/-- `pullbackStr_compat_last'` for an object `X = p^* H` and a Weil structure `s` given up to these
identifications. -/
lemma pullbackStr_compat_last_of_eq {Z W S : Scheme.{u}} (φ : W ≅ W) (ψ : Z ≅ Z) (p : W ⟶ S)
    (q : Z ⟶ S) (hφ : φ.hom ≫ p = p) (hψ : ψ.hom ≫ q = q) (a j : Z ⟶ W)
    (h : a ≫ φ.hom = ψ.hom ≫ j) (ha : a ≫ p = q) (hj : j ≫ p = q) (H : AdicSheaf l S)
    (X : AdicSheaf l W) (hX : X = (p)^*ᵃ[l].obj H)
    (s : (φ.inv)_*ᵃ[l].obj X ⟶ X) (hs : HEq s ((pullbackStrIso φ p hφ).hom.app H)) :
    (a)^*ᵃ[l].map s ≫
        (eqToIso (congrArg (a)^*ᵃ[l].obj hX) ≪≫ (adicUpperStarFactorApp l ha H).symm).hom =
    (Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l φ).symm (a)^*ᵃ[l] ≪≫
        (adicUpperStarComp l a φ.hom).symm ≪≫ adicUpperStarCongr l h ≪≫
        adicUpperStarComp l ψ.hom j ≪≫
        Functor.isoWhiskerLeft (j)^*ᵃ[l] (adicUpperStarIsoLowerStarInv l ψ)).hom.app X ≫
      (ψ.inv)_*ᵃ[l].map
        (eqToIso (congrArg (j)^*ᵃ[l].obj hX) ≪≫ (adicUpperStarFactorApp l hj H).symm).hom ≫
      ((pullbackStrIso ψ q hψ).hom.app H) := by
  subst hX
  obtain rfl := eq_of_heq hs
  simp only [eqToIso_refl, Iso.refl_trans]
  exact pullbackStr_compat_last' l φ ψ p q hφ hψ a j h ha hj H

/-- The compatibility with `β` of
`CategoryTheory.Endofunctor.IsoAlgebra.CyclicDecomposition.functorObjIsoMk`, with all the data
of the decomposition given up to equality. -/
lemma pullbackStr_compat_β {Z W S : Scheme.{u}} (φ : W ≅ W) (ψ : Z ≅ Z) (p : W ⟶ S)
    (q : Z ⟶ S) (hφ : φ.hom ≫ p = p) (hψ : ψ.hom ≫ q = q) (a j : Z ⟶ W)
    (h : a ≫ φ.hom = ψ.hom ≫ j) (ha : a ≫ p = q) (hj : j ≫ p = q) (H : AdicSheaf l S)
    (Jl J0 : AdicSheaf l W ⥤ AdicSheaf l Z) (hJl : Jl = (a)^*ᵃ[l]) (hJ0 : J0 = (j)^*ᵃ[l])
    (Φ : (φ.inv)_*ᵃ[l] ⋙ Jl ≅ J0 ⋙ (ψ.inv)_*ᵃ[l])
    (hΦ : HEq Φ (Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l φ).symm (a)^*ᵃ[l] ≪≫
        (adicUpperStarComp l a φ.hom).symm ≪≫ adicUpperStarCongr l h ≪≫
        adicUpperStarComp l ψ.hom j ≪≫
        Functor.isoWhiskerLeft (j)^*ᵃ[l] (adicUpperStarIsoLowerStarInv l ψ)))
    (X : AdicSheaf l W) (hX : X = (p)^*ᵃ[l].obj H)
    (s : (φ.inv)_*ᵃ[l].obj X ⟶ X) (hs : HEq s ((pullbackStrIso φ p hφ).hom.app H))
    (cl : Jl.obj X ≅ (q)^*ᵃ[l].obj H)
    (hcl : HEq cl (eqToIso (congrArg (a)^*ᵃ[l].obj hX) ≪≫ (adicUpperStarFactorApp l ha H).symm))
    (c0 : J0.obj X ≅ (q)^*ᵃ[l].obj H)
    (hc0 : HEq c0 (eqToIso (congrArg (j)^*ᵃ[l].obj hX) ≪≫ (adicUpperStarFactorApp l hj H).symm)) :
    Jl.map s ≫ cl.hom = Φ.hom.app X ≫ (ψ.inv)_*ᵃ[l].map c0.hom ≫
      ((pullbackStrIso ψ q hψ).hom.app H) := by
  subst hJl hJ0
  obtain rfl := eq_of_heq hΦ
  obtain rfl := eq_of_heq hcl
  obtain rfl := eq_of_heq hc0
  exact pullbackStr_compat_last_of_eq l φ ψ p q hφ hψ a j h ha hj H X hX s hs

end AlgebraicGeometry.ProEtale
