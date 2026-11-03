/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteBrown.FiniteBrownAdjointData
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteBrown
/-- Counit-preserving uniqueness from the two representing Hom bijections.
Source: the elementary uniqueness step in sk-lem-sp-finite-existence.
(blueprint: sk-lem-sp-finite-existence).
Proof plan: transpose the prescribed counits through each Hom bijection, compose the two
transposes, and use injectivity to prove both composites are identities. -/
theorem finiteBrownAdjointExistence_localUnique
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (c : Compactification f) [Smooth f]
    (d : ℕ) (_hcd : BaseFieldFiniteCD ell k) (B : BrownData ell n hn k f c) :
    Nonempty (FiniteBrownLocalUniqueData ell n hn k f c B d) := by
  let data : FiniteBrownLocalUniqueData ell n hn k f c B d :=
    { localUnique := by
        intro W K H H' hH hH' ε ε' hε hε'
        let MH : (ctf (Coeff ell n) W.toScheme).FullSubcategory := ⟨H, hH⟩
        let MH' : (ctf (Coeff ell n) W.toScheme).FullSubcategory := ⟨H', hH'⟩
        let φ := fun a : H ⟶ H ↦
          (support (Coeff ell n) c).map ((bang (Coeff ell n) W.ι).map a) ≫ ε
        let ψ := fun a : H ⟶ H' ↦
          (support (Coeff ell n) c).map ((bang (Coeff ell n) W.ι).map a) ≫ ε'
        let φ' := fun a : H' ⟶ H ↦
          (support (Coeff ell n) c).map ((bang (Coeff ell n) W.ι).map a) ≫ ε
        let ψ' := fun a : H' ⟶ H' ↦
          (support (Coeff ell n) c).map ((bang (Coeff ell n) W.ι).map a) ≫ ε'
        let a : H ⟶ H' := Classical.choose ((hε' MH).2 (φ (𝟙 H)))
        let b : H' ⟶ H := Classical.choose ((hε MH').2 (ψ' (𝟙 H')))
        have ha : ψ a = φ (𝟙 H) := Classical.choose_spec ((hε' MH).2 (φ (𝟙 H)))
        have hb : φ' b = ψ' (𝟙 H') := Classical.choose_spec ((hε MH').2 (ψ' (𝟙 H')))
        have hab : φ (a ≫ b) = φ (𝟙 H) := by
          calc
            φ (a ≫ b) =
                (support (Coeff ell n) c).map ((bang (Coeff ell n) W.ι).map a) ≫ φ' b := by
                  simp [φ, φ', Functor.map_comp, Category.assoc]
            _ = (support (Coeff ell n) c).map ((bang (Coeff ell n) W.ι).map a) ≫ ψ' (𝟙 H') := by rw [hb]
            _ = ψ a := by simp [ψ, ψ']
            _ = φ (𝟙 H) := ha
        have hba : ψ' (b ≫ a) = ψ' (𝟙 H') := by
          calc
            ψ' (b ≫ a) =
                (support (Coeff ell n) c).map ((bang (Coeff ell n) W.ι).map b) ≫ ψ a := by
                  simp [ψ', ψ, Functor.map_comp, Category.assoc]
            _ = (support (Coeff ell n) c).map ((bang (Coeff ell n) W.ι).map b) ≫ φ (𝟙 H) := by rw [ha]
            _ = φ' b := by simp [φ, φ']
            _ = ψ' (𝟙 H') := hb
        have hab' : a ≫ b = 𝟙 H := by
          apply (hε MH).1
          change φ (a ≫ b) = φ (𝟙 H)
          exact hab
        have hba' : b ≫ a = 𝟙 H' := by
          apply (hε' MH').1
          change ψ' (b ≫ a) = ψ' (𝟙 H')
          exact hba
        have haz : ψ a = ε := by simpa [ψ, φ] using ha
        let z : H ≅ H' := { hom := a, inv := b, hom_inv_id := hab', inv_hom_id := hba' }
        refine ⟨z, ?_, ?_⟩
        · simpa [ψ, φ] using ha
        · intro z' hz'
          apply Iso.ext
          apply (hε' MH).1
          exact hz'.trans haz.symm
    }
  exact ⟨data⟩
end AlgebraicGeometry.ProEtale.FiniteBrown
