/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.LocalTermLocality
public import WeilConjectures.TraceFormula.Specialization.Basic

/-!

# Varshavsky's vanishing lemma

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence

variable (c : Correspondence ℓ K)

theorem restrict_traceClass_eq_zero_of_isContractingAt' (F : c.FixedLocus)
    {y : RationalPoint c.C} (hc : c.IsContractingAt y) {B : Over (Spec (.of k))}
    [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F) [IsOpenImmersion j.left]
    [IsClosedImmersion j.left]
    (hB : Set.range j.left.base =
      {(F.liftPoint y hc.comp_c₁_eq_comp_c₂).left.base (default : Spec (.of k))})
    (hK : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (y ≫ c.c₁)).obj K)) :
    (c.traceClass F).restrict j = 0 :=
  sorry

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
