/-
Copyright (c) 2026 Claude and The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityScalarWeilLaw
public import WeilConjectures.WeilSheaf.SmoothPurityCoefficientFactor
public import WeilConjectures.WeilSheaf.SmoothPurityScalarCoefficientTransport
import Mathlib.Init
import Lean.Elab.Tactic.ElabTerm
import WeilConjectures.Tactic.ExactModProofs

/-! # Changing coefficients in a scalar Frobenius relation -/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

section Transport

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

variable {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k))

/-- **The Weil structures of pulled-back module objects are compatible with the extension of
scalars** along a change of coefficients `a : Λ ⟶ Λ'`: through the (Pull) isomorphisms
`Ext (p^* M) ≅ p^* (Ext M)` and `Ext (Fr^* N) ≅ Fr^* (Ext N)`, the extension of scalars of the
Weil structure `Fr^* p^* M ≅ p^* M` is the Weil structure of `p^* (Ext M)`. -/
lemma purity_extendScalars_map_geometricFiberProjUpperStarFrobeniusIso_hom_app_comp_pullIso_hom_app
    (M : Mod (Sheaf (ProEt.topology X₀) Ab.{u + 1}) (condensedRingObj Λ X₀)) :
    (Mod.extendScalars (coefficientMap a f.geometricFiber)).map
          ((geometricFiberProjUpperStarFrobeniusIso Λ f).hom.app M) ≫
        (pullIso a f.geometricFiberProj).hom.app M =
      (pullIso a f.geometricGaloisFrobenius.hom).hom.app ((f.geometricFiberProj)^*⟦Λ⟧.obj M) ≫
        (f.geometricGaloisFrobenius.hom)^*⟦Λ'⟧.map ((pullIso a f.geometricFiberProj).hom.app M) ≫
          (geometricFiberProjUpperStarFrobeniusIso Λ' f).hom.app
            ((Mod.extendScalars (coefficientMap a X₀)).obj M) := by
  have h := purity_extendScalars_map_factor_hom_comp_pullIso a f.geometricFiberProj
    f.geometricGaloisFrobenius.hom f.geometricGaloisFrobenius_hom_comp_geometricFiberProj M
  simp only [purityModuleFactorIso, geometricFiberProjUpperStarFrobeniusIso] at h ⊢
  exact_mod_proofs h

end Transport

section ScalarRelation

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

variable (M N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  (e : ((f.geometricFiberProj)^*[Ab.{u + 1}].mapMod _).obj M ≅
    ((f.geometricFiberProj)^*[Ab.{u + 1}].mapMod _).obj N)
  (c : ℤ)

/-- Unfold the trivialization at the isomorphism level. -/
lemma purityChangeCoefficientTrivialization_eq
    (e₁ : ((f.geometricFiberProj)^*[Ab.{u + 1}].mapMod _).obj M ≅
      ((f.geometricFiberProj)^*[Ab.{u + 1}].mapMod _).obj (𝟙_ _)) :
    purityChangeCoefficientTrivialization Λ a f.geometricFiberProj M e₁ =
      purityChangeCoefficientPullbackIso Λ a f.geometricFiberProj M (𝟙_ _) e₁ ≪≫
        (f.geometricFiberProj)^*⟦Λ'⟧.mapIso (purityCoefficientUnitIso Λ a X) := rfl

end ScalarRelation

end AlgebraicGeometry.ProEtale.CondensedRing
