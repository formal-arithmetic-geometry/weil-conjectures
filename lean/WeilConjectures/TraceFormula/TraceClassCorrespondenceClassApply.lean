/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.TraceClassCorrespondenceClass

/-!

# The trace class: `correspondenceClassEquiv_apply`

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

lemma correspondenceClassEquiv_apply (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (g : (boundedConstructibleLowerShriek _ ℓ c).obj (𝟙_ _) ⟶
        (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ X ⟶ X)).obj K)).obj
          ((boundedConstructibleUpperShriek _ ℓ (prod.fst : Y ⨯ X ⟶ Y)).obj L)) :
    correspondenceClassEquiv ℓ c K L g =
      (boundedConstructibleUpperStarComp _ ℓ c prod.snd).hom.app K ≫
        Verdier.correspondenceClassEquiv (boundedConstructibleUpperShriekAdjunction _ ℓ c)
          (boundedConstructibleExceptionalProjection _ ℓ c) _ _ g ≫
        (boundedConstructibleUpperShriekComp_padicAlgCl ℓ c prod.fst).inv.app L :=
  rfl

end CorrespondenceClass

end AlgebraicGeometry.ProEtale.CondensedRing
