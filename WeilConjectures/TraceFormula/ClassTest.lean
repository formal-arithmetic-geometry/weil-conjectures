/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Product

/-!

# The test map of a class on a product

A morphism `φ : Z ⟶ RHom(Lp₂^* M, Rp₁^! M)` on `S ⨯ S` is determined by its *test map*
`Rp₁_! (Lp₂^* M ⊗ Z) ⟶ M` (`ProEtale.CondensedRing.classTest`), its uncurried
`Rp₁_! ⊣ Rp₁^!`-adjoint. The test map of the class of a correspondence is computed in
`WeilConjectures.TraceFormula.SourceExchangeTest`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {S : Over (Spec (.of k))} [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom] (M : Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧)

/-- The *test map* of a morphism `φ : Z ⟶ RHom(Lp₂^* M, Rp₁^! M)`: its `Rp₁_! ⊣ Rp₁^!`-adjoint
uncurried form `Rp₁_! (Lp₂^* M ⊗ Z) ⟶ M`. -/
noncomputable def classTest {Z : Dᵇc((S ⨯ S).left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (φ : Z ⟶ (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : S ⨯ S ⟶ S)).obj M)).obj
      ((boundedConstructibleUpperShriek ℓ (prod.fst : S ⨯ S ⟶ S)).obj M)) :
    (boundedConstructibleLowerShriek ℓ (prod.fst : S ⨯ S ⟶ S)).obj
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : S ⨯ S ⟶ S)).obj M ⊗ Z) ⟶ M :=
  ((boundedConstructibleUpperShriekAdjunction ℓ (prod.fst : S ⨯ S ⟶ S)).homEquiv _ _).symm
    (uncurry φ)

variable {M}

lemma classTest_injective {Z : Dᵇc((S ⨯ S).left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {φ φ' : Z ⟶ (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : S ⨯ S ⟶ S)).obj M)).obj
      ((boundedConstructibleUpperShriek ℓ (prod.fst : S ⨯ S ⟶ S)).obj M)}
    (h : classTest ℓ M φ = classTest ℓ M φ') : φ = φ' :=
  uncurry_injective (Equiv.injective _ h)

lemma classTest_comp {Z Z' : Dᵇc((S ⨯ S).left)⟦Profinite.padicAlgClRingObj ℓ⟧} (ψ : Z' ⟶ Z)
    (φ : Z ⟶ (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : S ⨯ S ⟶ S)).obj M)).obj
      ((boundedConstructibleUpperShriek ℓ (prod.fst : S ⨯ S ⟶ S)).obj M)) :
    classTest ℓ M (ψ ≫ φ) =
      (boundedConstructibleLowerShriek ℓ (prod.fst : S ⨯ S ⟶ S)).map (_ ◁ ψ) ≫
        classTest ℓ M φ := by
  rw [classTest, classTest, uncurry_natural_left, Adjunction.homEquiv_naturality_left_symm]

lemma classTest_curry {Z : Dᵇc((S ⨯ S).left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (ψ : (boundedConstructibleLowerShriek ℓ (prod.fst : S ⨯ S ⟶ S)).obj
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : S ⨯ S ⟶ S)).obj M ⊗ Z) ⟶ M) :
    classTest ℓ M (curry (((boundedConstructibleUpperShriekAdjunction ℓ
      (prod.fst : S ⨯ S ⟶ S)).homEquiv _ _) ψ)) = ψ := by
  rw [classTest, uncurry_curry, Equiv.symm_apply_apply]


end AlgebraicGeometry.ProEtale.CondensedRing
