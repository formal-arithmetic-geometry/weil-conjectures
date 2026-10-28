/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExceptionalHom
public import WeilConjectures.TraceFormula.KunnethVerdier
public import WeilConjectures.TraceFormula.LocalTerm

/-!

# The trace class: evaluation kernels and the class bijection `correspondenceClassEquiv`

Split off `WeilConjectures.TraceFormula.TraceClass` (which imports this module), as that file
alone took longer than the 60 s a file may take. -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))}

/-! ### Evaluation kernels -/

section Evaluation

variable (ℓ) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The identification `LΔ_X^* (K ⊠ N) ≅ K ⊗ N` of the restriction of an external product to the
diagonal: the monoidal structure of `LΔ_X^*` and `L(Δ_X ≫ p_i)^* = L(𝟙)^* ≅ 𝟭`. -/
noncomputable def diagUpperStarExternalProductIso
    (K N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ (diag X)).obj (externalProduct ℓ K N) ≅ K ⊗ N :=
  (Functor.Monoidal.μIso (boundedConstructibleUpperStar _ ℓ (diag X)) _ _).symm ≪≫
    tensorIso
      (((boundedConstructibleUpperStarComp _ ℓ (diag X) prod.fst).app K).symm ≪≫
        eqToIso (by rw [diag, prod.lift_fst]) ≪≫
        (boundedConstructibleUpperStarId _ ℓ X).app K)
      (((boundedConstructibleUpperStarComp _ ℓ (diag X) prod.snd).app N).symm ≪≫
        eqToIso (by rw [diag, prod.lift_snd]) ≪≫
        (boundedConstructibleUpperStarId _ ℓ X).app N)

/-- The *evaluation kernel* `e_K : K ⊠ D_X K ⟶ RΔ_* ω_X` (blueprint
`lem-trf-trace-map-from-external-duality`, `def-trf-kernel-pushforward-maps`): the
`LΔ^* ⊣ RΔ_*` adjoint of the evaluation `LΔ^* (K ⊠ D_X K) ≅ K ⊗ D_X K ⟶ ω_X`. -/
noncomputable def evaluationKernel (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    externalProduct ℓ K (verdierDual ℓ (toPoint X) K) ⟶
      (boundedConstructibleLowerStar _ ℓ (diag X)).obj (dualizingComplex' ℓ X) :=
  (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ (diag X)).homEquiv _ _
    ((diagUpperStarExternalProductIso ℓ K _).hom ≫ (ihom.ev K).app (dualizingComplex' ℓ X))

end Evaluation

/-! ### The class of a correspondence -/

section CorrespondenceClass

variable (ℓ) {C Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom] (c : C ⟶ Y ⨯ X)

/-- **The class of a correspondence** (blueprint `lem-trf-correspondence-class`): for the support
`c = (c₁, c₂) : C ⟶ Z = Y ⨯ X` of a correspondence from `(X, K)` to `(Y, L)`, with
`c₁ = c ≫ p₁` and `c₂ = c ≫ p₂`, the tensor–hom adjunction, the derived projection formula for
`c` and the exceptional adjunction give a bijection
```
Hom(Rc_! ℚ̄_ℓ,C, RHom(Lp₂^* K, Rp₁^! L)) ≃ Hom(Lc₂^* K, Rc₁^! L),
```
natural in `K` and `L` (`correspondenceClassEquiv_naturality_left`,
`correspondenceClassEquiv_naturality_right`). The *class* `[u]` of a coefficient map `u` is its
inverse image, a class supported on `c`. -/
noncomputable def correspondenceClassEquiv (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleLowerShriek _ ℓ c).obj (𝟙_ _) ⟶
        (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ X ⟶ X)).obj K)).obj
          ((boundedConstructibleUpperShriek _ ℓ (prod.fst : Y ⨯ X ⟶ Y)).obj L)) ≃
      ((boundedConstructibleUpperStar _ ℓ (c ≫ prod.snd)).obj K ⟶
        (boundedConstructibleUpperShriek _ ℓ (c ≫ prod.fst)).obj L) where
  toFun g := (boundedConstructibleUpperStarComp _ ℓ c prod.snd).hom.app K ≫
    Verdier.correspondenceClassEquiv (boundedConstructibleUpperShriekAdjunction _ ℓ c)
      (boundedConstructibleExceptionalProjection _ ℓ c) _ _ g ≫
    (boundedConstructibleUpperShriekComp_padicAlgCl ℓ c prod.fst).inv.app L
  invFun f := (Verdier.correspondenceClassEquiv (boundedConstructibleUpperShriekAdjunction _ ℓ c)
      (boundedConstructibleExceptionalProjection _ ℓ c) _ _).symm
    ((boundedConstructibleUpperStarComp _ ℓ c prod.snd).inv.app K ≫ f ≫
      (boundedConstructibleUpperShriekComp_padicAlgCl ℓ c prod.fst).hom.app L)
  left_inv g := by
    simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id,
      Iso.inv_hom_id_app_assoc, Equiv.symm_apply_apply]
  right_inv f := by
    simp only [Equiv.apply_symm_apply, Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj,
      Category.comp_id, Iso.hom_inv_id_app_assoc]

end CorrespondenceClass

end AlgebraicGeometry.ProEtale.CondensedRing
