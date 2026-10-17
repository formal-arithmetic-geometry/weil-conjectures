/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.IdentityMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence
public import WeilConjectures.TraceFormula.CompactCohomology
public import WeilConjectures.TraceFormula.Dualizing

/-!

# Additivity of the compactly supported Frobenius trace

Let `Φ` be a finite universal homeomorphism of `X`, `j : U ⟶ X` an open immersion and
`i : Z ⟶ X` a closed immersion onto the complement, both stable under `Φ`. For a Weil object
`(K, φ)` the trace of the compactly supported Frobenius on `RΓ_c(X, K)` is the sum of the traces
on `RΓ_c(U, K|_U)` and `RΓ_c(Z, K|_Z)`
(blueprint `prop-trf-trace-additivity-open-closed`, `sk-i-global-additivity`).

## The Frobenius operator `Φ^♯`

The compactly supported Frobenius of `(K, φ)` is `RΓ_c(φ) ∘ Φ^♯`, where
```
Φ^♯ : Ra_{X!} V ⟶ Ra_{X!} RΦ_* LΦ^* V ≅ Ra_{X!} RΦ_! LΦ^* V ≅ R(Φ ≫ a_X)_! LΦ^* V = Ra_{X!} LΦ^* V
```
(`ProEtale.CondensedRing.frobeniusSharp`, blueprint `prop-trf-graph-operator`) is built from the
unit of `LΦ^* ⊣ RΦ_*`, the identification `RΦ_! ≅ RΦ_*` and the composition isomorphism of the
lower shriek (`ProEtale.CondensedRing.WeilBoundedConstructible.compactFrobenius_eq`). This uses
that the compact-support base change of the square of identities over `a_X` is the identity, a
consequence of the description of `Ex_!` as a mate
(`boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section FrobeniusSharp

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

variable (ℓ X) in
/-- The composition square `R(𝟙 X)_! ⋙ Ra_{X!} ≅ Ra_{X!} ⋙ R(𝟙 s)_!` of the square of
identities over `a_X` is the identity through `R(𝟙)_! ≅ 𝟭`. -/
lemma lowerShriekSquareIso_isPullback_toPoint_app
    (c : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ (isPullback_toPoint X).w).hom.app c ≫
        (boundedConstructibleLowerShriekId ℓ (point k)).hom.app
          ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
            c) =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
        ((boundedConstructibleLowerShriekId ℓ X).hom.app c) := by
  have hl := boundedConstructibleLowerShriekComp_padicAlgCl_id_left ℓ (toPoint X) c
  have hr := boundedConstructibleLowerShriekComp_padicAlgCl_id_right ℓ (toPoint X) c
  rw [boundedConstructibleLowerShriekId, Iso.trans_hom, NatTrans.comp_app,
    boundedConstructibleLowerShriekId, Iso.trans_hom, NatTrans.comp_app,
    ← cancel_epi ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ (𝟙 X) (toPoint X)).hom.app c),
    hl, boundedConstructibleLowerShriekSquareIso_padicAlgCl, Iso.trans_hom, Iso.trans_hom,
    NatTrans.comp_app, NatTrans.comp_app, Iso.symm_hom, Category.assoc, Category.assoc,
    Iso.hom_inv_id_app_assoc, hr, eqToIso.hom, eqToHom_app]
  simp only [Functor.id_obj, eqToHom_trans]

variable (ℓ X) in
/-- The compact-support base change of the cartesian square of identities over `a_X` is the
identity: `L(𝟙 s)^* Ra_{X!} ≅ Ra_{X!} ≅ Ra_{X!} L(𝟙 X)^*`. -/
lemma lowerShriekBaseChange_isPullback_toPoint_app
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (isPullback_toPoint X)).app K =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k)).hom.app
          ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
            K) ≫
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
          ((boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X).inv.app K) := by
  have h := mateEquiv_symm_app_eq_of_id
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ (𝟙 X))
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ (𝟙 (point k)))
    (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X)
    (boundedConstructibleLowerShriekId ℓ X)
    (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k))
    (boundedConstructibleLowerShriekId ℓ (point k))
    (fun c ↦ Adjunction.unit_ofNatIsoRight_conjugateIsoEquiv
      (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ (𝟙 X))
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (𝟙 X))
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ X) c)
    (fun d ↦ Adjunction.unit_ofNatIsoRight_conjugateIsoEquiv
      (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ
        (𝟙 (point k)))
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (𝟙 (point k)))
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k)) d)
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X))
    (boundedConstructibleLowerShriekSquareIso_padicAlgCl ℓ (isPullback_toPoint X).w).hom
    (lowerShriekSquareIso_isPullback_toPoint_app ℓ X) K
  rw [boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_mateEquiv]
  exact h

end FrobeniusSharp

end AlgebraicGeometry.ProEtale.CondensedRing
