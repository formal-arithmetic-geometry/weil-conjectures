/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.TraceClassDiagonal

/-!

# The supported class and the Künneth–Verdier map

Let `c = (C, c₁, c₂, u)` be an endocorrespondence of `(X, K)`. Its *supported class*
`ũ : Rc_! ℚ̄_ℓ,C ⟶ K ⊠ D_X K` (`ProEtale.CondensedRing.Correspondence.supportedClass`) is the
class `[u] : Rc_! ℚ̄_ℓ,C ⟶ RHom(Lp₂^* K, Rp₁^! K)` of `u` (blueprint
`lem-trf-correspondence-class`) read through the inverse of the Künneth–Verdier isomorphism
`κ_{K,K}` (`ProEtale.CondensedRing.Correspondence.supportedClass_eq`, blueprint
`lem-trf-trace-source-exchange`, Step 0).

The Künneth–Verdier map `κ_{M,N}` is natural in `M`
(`ProEtale.CondensedRing.kunnethVerdierMap_naturality_left`), so the supported class of the
diagonal correspondence of an endomorphism `v` is that of the identity followed by
`Lp₁^* v ⊠ 1` (`ProEtale.CondensedRing.Correspondence.supportedClass_ofEnd`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section KunnethVerdier

variable (ℓ) {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The exceptional adjoint of the exceptional Künneth map is natural in `M`. -/
lemma exceptionalKunnethAdjoint_naturality {M M' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (f : M ⟶ M') :
    exceptionalKunnethAdjoint ℓ (Y := Y) M ≫ f =
      (boundedConstructibleLowerShriek _ ℓ (prod.fst : X ⨯ Y ⟶ X)).map
          ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).map f ▷ _) ≫
        exceptionalKunnethAdjoint ℓ M' := by
  have hPF := boundedConstructibleExceptionalProjectionMorphism_natural_right
    (Profinite.padicAlgClRingObj ℓ) ℓ (prod.fst : X ⨯ Y ⟶ X)
    ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj (dualizingComplex' ℓ Y)) f
  have hinv : (boundedConstructibleLowerShriek _ ℓ (prod.fst : X ⨯ Y ⟶ X)).map
        (_ ◁ (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).map f) ≫
      inv (((boundedConstructibleExceptionalProjection _ ℓ (prod.fst : X ⨯ Y ⟶ X)).app
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
          (dualizingComplex' ℓ Y))).app M') =
      inv (((boundedConstructibleExceptionalProjection _ ℓ (prod.fst : X ⨯ Y ⟶ X)).app
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj
          (dualizingComplex' ℓ Y))).app M) ≫ (_ ◁ f) := by
    rw [boundedConstructibleExceptionalProjection_app_app,
      boundedConstructibleExceptionalProjection_app_app, IsIso.comp_inv_eq, Category.assoc,
      hPF, IsIso.inv_hom_id_assoc]
  simp only [exceptionalKunnethAdjoint, Category.assoc]
  rw [← Functor.map_comp_assoc, ← BraidedCategory.braiding_naturality_left,
    Functor.map_comp_assoc, reassoc_of% hinv]
  simp only [← whisker_exchange_assoc, leftUnitor_naturality, Category.assoc]

/-- The exceptional Künneth map `α : M ⊠ ω_Y ⟶ Rp_X^! M` is natural in `M`. -/
lemma exceptionalKunnethMap_naturality {M M' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (f : M ⟶ M') :
    exceptionalKunnethMap ℓ (Y := Y) M ≫
        (boundedConstructibleUpperShriek _ ℓ (prod.fst : X ⨯ Y ⟶ X)).map f =
      ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).map f ▷ _) ≫
        exceptionalKunnethMap ℓ M' := by
  rw [exceptionalKunnethMap, exceptionalKunnethMap,
    ← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left,
    exceptionalKunnethAdjoint_naturality]
  rfl

/-- The Künneth–Verdier map `κ_{M,N}` is natural in `M`. -/
lemma kunnethVerdierMap_naturality_left {M M' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (f : M ⟶ M') (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    kunnethVerdierMap ℓ M N ≫
        (ihom _).map ((boundedConstructibleUpperShriek _ ℓ (prod.fst : X ⨯ Y ⟶ X)).map f) =
      ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).map f ▷ _) ≫
        kunnethVerdierMap ℓ M' N := by
  rw [kunnethVerdierMap, kunnethVerdierMap, curry_natural_right, ← curry_natural_left]
  congr 1
  simp only [kunnethVerdierPairing, Category.assoc, exceptionalKunnethMap_naturality]
  rw [← whisker_exchange_assoc, ← whisker_exchange_assoc, ← whisker_exchange_assoc,
    associator_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_right, comp_whiskerRight_assoc,
    associator_inv_naturality_middle_assoc]

/-- The inverse of the Künneth–Verdier isomorphism is natural in `M`. -/
lemma inv_kunnethVerdierMap_naturality_left
    {M M' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (f : M ⟶ M')
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (ihom _).map ((boundedConstructibleUpperShriek _ ℓ (prod.fst : X ⨯ Y ⟶ X)).map f) ≫
        inv (kunnethVerdierMap ℓ M' N) =
      inv (kunnethVerdierMap ℓ M N) ≫
        ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).map f ▷ _) := by
  rw [IsIso.comp_inv_eq, Category.assoc, ← kunnethVerdierMap_naturality_left,
    IsIso.inv_hom_id_assoc]

end KunnethVerdier

end AlgebraicGeometry.ProEtale.CondensedRing
