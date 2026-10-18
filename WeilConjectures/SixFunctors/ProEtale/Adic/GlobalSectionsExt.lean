/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologyBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ForgetModuleCohomology

/-!
# Global sections of sheaves of `ℚ̄_ℓ`-modules as morphisms out of `ℤ`

For a pro-étale sheaf `M` of `ℚ̄_ℓ`-modules on `X`, morphisms `ℤ_X ⟶ M` of abelian sheaves are
the global sections `Γ(X, M)` (`AlgebraicGeometry.ProEtale.constantIntHomAddEquivΓ`), naturally
in `M`. This identifies the complex `Hom(ℤ_X, J)` computing `Ext(ℤ_X, -)` from an injective
resolution `J` with the complex of global sections `Γ(X, J)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] (X : Scheme.{u})

/-- Morphisms `ℤ_X ⟶ M` of abelian sheaves, for a sheaf `M` of `ℚ̄_ℓ`-modules, are the global
sections `Γ(X, M)`. -/
noncomputable def constantIntHomAddEquivΓ
    (M : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) :
    ((constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶ (sheafForget₂ (ULift.{u + 1} (PadicAlgCl l)) X).obj M) ≃+
      (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj M :=
  ((constantSheafAdj _ AddCommGrpCat.{u + 1} (Scheme.ProEt.isTerminalMkId X)).homAddEquiv _ _).trans
    ((AddCommGrpCat.uliftZMultiplesAddEquiv _).trans
      ((Sheaf.ΓNatIsoSheafSections _ _
        (Scheme.ProEt.isTerminalMkId X)).app M).symm.toLinearEquiv.toAddEquiv)

lemma constantIntHomAddEquivΓ_apply
    (M : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l))
    (f : (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶ (sheafForget₂ (ULift.{u + 1} (PadicAlgCl l)) X).obj M) :
    constantIntHomAddEquivΓ X M f =
      (Sheaf.ΓNatIsoSheafSections _ _ (Scheme.ProEt.isTerminalMkId X)).inv.app M
        (AddCommGrpCat.uliftZMultiplesAddEquiv _
          ((constantSheafAdj _ AddCommGrpCat.{u + 1} (Scheme.ProEt.isTerminalMkId X)).homEquiv _ _
            f)) :=
  rfl

omit [Fact l.Prime] in
/-- `AddCommGrpCat.uliftZMultiplesAddEquiv` is natural. -/
lemma _root_.AddCommGrpCat.uliftZMultiplesAddEquiv_comp {G H : AddCommGrpCat.{u + 1}}
    (g : AddCommGrpCat.of (ULift ℤ) ⟶ G) (k : G ⟶ H) :
    AddCommGrpCat.uliftZMultiplesAddEquiv H (g ≫ k) =
      k (AddCommGrpCat.uliftZMultiplesAddEquiv G g) :=
  rfl

variable {X} in
lemma constantIntHomAddEquivΓ_comp {M N : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)}
    (f : (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶ (sheafForget₂ (ULift.{u + 1} (PadicAlgCl l)) X).obj M)
    (φ : M ⟶ N) :
    constantIntHomAddEquivΓ X N (f ≫ (sheafForget₂ (ULift.{u + 1} (PadicAlgCl l)) X).map φ) =
      (Sheaf.Γ _ _).map φ (constantIntHomAddEquivΓ X M f) := by
  have h := ConcreteCategory.congr_hom ((Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X)
    (WeilCoefficients.{u} l) (Scheme.ProEt.isTerminalMkId X)).inv.naturality φ)
  rw [constantIntHomAddEquivΓ_apply, constantIntHomAddEquivΓ_apply,
    Adjunction.homEquiv_naturality_right, AddCommGrpCat.uliftZMultiplesAddEquiv_comp]
  simp only [ConcreteCategory.comp_apply] at h
  exact h _

end AlgebraicGeometry.ProEtale
