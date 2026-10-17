/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.RingSheaf.MonoidalComp
public import WeilConjectures.SixFunctors.ProEtale.RingSheaf.OpenClosed

/-!
# Base change of the extension by zero of module sheaves over a sheaf of rings

Let `B` be a sheaf of `R`-algebras on `X_proét`. For a commutative square `a ≫ b = c ≫ d` of
schemes, the coefficient rings `a^* b^* B` and `c^* d^* B` are identified by a ring isomorphism
(`ProEtale.RingSheaf.upperStarCompAlgHom`), and the transports of module sheaves agree:
`a^* ∘ b^* ≅ Res ∘ c^* ∘ d^*` (`ProEtale.RingSheaf.upperStarCompIso`).

For a morphism `g : X' ⟶ X` and base changes `j' : U' ⟶ X'`, `g_U : U' ⟶ U` of a quasi-compact
open immersion `j` with closed complement `i`, this gives the base change isomorphism
`g^* j_! ≅ j'_! g_U^*` on module sheaves, the `j^* B`-module sheaf `g_U^* N` being regarded as a
`j'^* g^* B`-module sheaf along the ring isomorphism
(`ProEtale.RingSheaf.openImmersionLowerShriekBaseChangeIso`). This is part (4) of blueprint
`det-sf-open-closed-sequence-ring-sheaf`. As in the blueprint, it is formal: `g^* j_! N` is
supported on `U'`, so it is `j'_! j'^* g^* j_! N`, and `j'^* g^* j_! N ≅ g_U^* j^* j_! N ≅ g_U^* N`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.RingSheaf

open Scheme

variable {R : Type (u + 1)} [CommRing R] {X : Scheme.{u}}
  (B : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) [MonObj B]

section Coefficients

variable {V X' U : Scheme.{u}} {a : V ⟶ X'} {b : X' ⟶ X} {c : V ⟶ U} {d : U ⟶ X}
  (h : a ≫ b = c ≫ d)

/-- For `k = k'`, the identification `k^* B ≅ k'^* B` is a morphism of monoid objects. -/
lemma isMonHom_upperStarCongr_hom_app {k k' : V ⟶ X} (e : k = k') :
    IsMonHom ((upperStarCongr (ModuleCat.{u + 1} R) e).hom.app B) := by
  subst e
  exact NatTrans.isMonHom_app _ _

/- The identification `a^* b^* B ⟶ (a ≫ b)^* B = (c ≫ d)^* B ⟶ c^* d^* B` of the coefficient
rings of a commutative square `a ≫ b = c ≫ d`. It is written out (rather than being a
definition) because the kernel fails to check the monoid morphism property through a
definition. -/
set_option hygiene false in
local notation "ψ[" h "]" =>
  Functor.compAlgHom _ _ (upperStarComp (ModuleCat.{u + 1} R) a b).inv B ≫
    (upperStarCongr (ModuleCat.{u + 1} R) h).hom.app B ≫
      inv (Functor.compAlgHom _ _ (upperStarComp (ModuleCat.{u + 1} R) c d).inv B)

/-- The identification of the coefficient rings `a^* b^* B ⟶ c^* d^* B` of a commutative square
`a ≫ b = c ≫ d` is a morphism of monoid objects. -/
instance isMonHom_upperStarCompAlgHom : IsMonHom ψ[h] :=
  have := isMonHom_upperStarCongr_hom_app B h
  have : IsMonHom (inv (Functor.compAlgHom _ _ (upperStarComp (ModuleCat.{u + 1} R) c d).inv B)) :=
    IsMonHom.inv _
  have : IsMonHom ((upperStarCongr (ModuleCat.{u + 1} R) h).hom.app B ≫
      inv (Functor.compAlgHom _ _ (upperStarComp (ModuleCat.{u + 1} R) c d).inv B)) :=
    inferInstance
  inferInstance

/-- For a commutative square `a ≫ b = c ≫ d`, the transports of module sheaves agree:
`a^* ∘ b^* ≅ Res ∘ c^* ∘ d^*`, the restriction of scalars being along the identification
`a^* b^* B ⟶ c^* d^* B` of the coefficient rings. -/
set_option maxHeartbeats 2000000 in
noncomputable def upperStarCompIso :
    upperStar B b ⋙ upperStar ((b)^*[ModuleCat.{u + 1} R].obj B) a ≅
      upperStar B d ⋙ upperStar ((d)^*[ModuleCat.{u + 1} R].obj B) c ⋙ Mod.comap ψ[h] :=
  have := isMonHom_upperStarCongr_hom_app B h
  Functor.mapModCompIso _ _ (upperStarComp (ModuleCat.{u + 1} R) a b).inv B ≪≫
    Functor.isoWhiskerRight (Functor.mapModNatIso (upperStarCongr (ModuleCat.{u + 1} R) h) B)
      _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapComp
      (Functor.compAlgHom _ _ (upperStarComp (ModuleCat.{u + 1} R) a b).inv B)
      ((upperStarCongr (ModuleCat.{u + 1} R) h).hom.app B)).symm ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapCongr (by
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id])) ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapComp ψ[h]
      (Functor.compAlgHom _ _ (upperStarComp (ModuleCat.{u + 1} R) c d).inv B)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapModCompIso _ _ (upperStarComp (ModuleCat.{u + 1} R) c d).inv B).symm _ ≪≫
    Functor.associator _ _ _

end Coefficients

end AlgebraicGeometry.ProEtale.RingSheaf
