/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.TraceClassCorrespondenceClassApply

/-!

# The trace class: the naturality of `correspondenceClassEquiv` in `L` and `K`

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

/-! ### The class of a correspondence -/

section CorrespondenceClass

variable (ℓ) {C Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom] (c : C ⟶ Y ⨯ X)

/-- Naturality of the class bijection in `L` (blueprint `lem-trf-correspondence-class`). -/
lemma correspondenceClassEquiv_naturality_right
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {L L' : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (b : L ⟶ L')
    (g : (boundedConstructibleLowerShriek _ ℓ c).obj (𝟙_ _) ⟶
        (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ X ⟶ X)).obj K)).obj
          ((boundedConstructibleUpperShriek _ ℓ (prod.fst : Y ⨯ X ⟶ Y)).obj L)) :
    correspondenceClassEquiv ℓ c K L'
        (g ≫ (ihom _).map ((boundedConstructibleUpperShriek _ ℓ prod.fst).map b)) =
      correspondenceClassEquiv ℓ c K L g ≫
        (boundedConstructibleUpperShriek _ ℓ (c ≫ prod.fst)).map b := by
  -- unfold the bijection by `correspondenceClassEquiv_apply` first: matching the `_conj`
  -- lemma against the bundled `Equiv` took 40-50 s
  simp only [correspondenceClassEquiv_apply]
  exact Verdier.correspondenceClassEquiv_naturality_right_conj
    (boundedConstructibleUpperShriekAdjunction _ ℓ c)
    (boundedConstructibleExceptionalProjection _ ℓ c) _
    (boundedConstructibleUpperShriekComp_padicAlgCl ℓ c prod.fst)
    ((boundedConstructibleUpperStarComp _ ℓ c prod.snd).hom.app K) b g

/-- Naturality of the class bijection in `K` (blueprint `lem-trf-correspondence-class`). -/
lemma correspondenceClassEquiv_naturality_left
    {K K' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (a : K' ⟶ K)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (g : (boundedConstructibleLowerShriek _ ℓ c).obj (𝟙_ _) ⟶
        (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ X ⟶ X)).obj K)).obj
          ((boundedConstructibleUpperShriek _ ℓ (prod.fst : Y ⨯ X ⟶ Y)).obj L)) :
    correspondenceClassEquiv ℓ c K' L
        (g ≫ (pre ((boundedConstructibleUpperStar _ ℓ prod.snd).map a)).app _) =
      (boundedConstructibleUpperStar _ ℓ (c ≫ prod.snd)).map a ≫
        correspondenceClassEquiv ℓ c K L g := by
  -- unfold the bijection by `correspondenceClassEquiv_apply` first: matching the `_conj`
  -- lemma against the bundled `Equiv` took 40-50 s
  simp only [correspondenceClassEquiv_apply]
  exact Verdier.correspondenceClassEquiv_naturality_left_conj
    (boundedConstructibleUpperShriekAdjunction _ ℓ c)
    (boundedConstructibleExceptionalProjection _ ℓ c) _
    (boundedConstructibleUpperStarComp _ ℓ c prod.snd)
    ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ c prod.fst).inv.app L) a g

end CorrespondenceClass

end AlgebraicGeometry.ProEtale.CondensedRing
