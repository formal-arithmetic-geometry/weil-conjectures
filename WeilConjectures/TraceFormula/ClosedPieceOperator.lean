/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CompactPullback

/-!

# The Frobenius endomorphism of the closed piece of the localization triangle

Let `Φ` be a finite universal homeomorphism of `X` and `i : Z ⟶ X` a closed immersion stable
under `Φ`. For a Weil object `(K, φ)` this file defines the endomorphism `E_Z` of
`RΓ_c(X, Ri_* Li^* K)` induced by the compactly supported Frobenius of `K|_Z`, through the
isomorphism `Ra_{X!} Ri_* ≅ Ra_{Z!}`.

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleLowerStarCompToPoint`: `Ra_{X!} Ri_* ≅ Ra_{Z!}`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.compactFrobeniusClosedPiece`: the operator
  `E_Z`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Frobenius

variable {X U Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

variable (ℓ) in
/-- The isomorphism `Ra_{X!} Ri_* ≅ Ra_{X!} Ri_! ≅ Ra_{Z!}` for a proper `i : Z ⟶ X`. -/
noncomputable def boundedConstructibleLowerStarCompToPoint (i : Z ⟶ X) [IsProper i.left] :
    boundedConstructibleLowerStar ℓ i ⋙
        boundedConstructibleLowerShriek ℓ (toPoint X) ≅
      boundedConstructibleLowerShriek ℓ (toPoint Z) :=
  Functor.isoWhiskerRight (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ i).symm _ ≪≫
    boundedConstructibleLowerShriekCompToPoint ℓ i

/-- The pullback `i^♯ : Ra_{X!} ⟶ Ra_{Z!} Li^*` along a proper `i` is `Ra_{X!}` of the unit of
`Li^* ⊣ Ri_*` followed by `Ra_{X!} Ri_* ≅ Ra_{Z!}`. -/
lemma compactPullback_app_eq (i : Z ⟶ X) [IsProper i.left]
    (N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (compactPullback ℓ i).app N =
      (boundedConstructibleLowerShriek ℓ (toPoint X)).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ
            i).unit.app N) ≫
        (boundedConstructibleLowerStarCompToPoint ℓ i).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj N) := by
  rw [compactPullback_app, boundedConstructibleLowerStarCompToPoint, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom]

variable {Φ : X ⟶ X} {ΦU : U ⟶ U} {ΦZ : Z ⟶ Z} {j : U ⟶ X} {i : Z ⟶ X}
  [IsOpenImmersion j.left] [IsClosedImmersion i.left] [IsFinite Φ.left]
  [IsUniversalHomeomorphism Φ.left] [IsFinite ΦU.left] [IsUniversalHomeomorphism ΦU.left]
  [IsFinite ΦZ.left] [IsUniversalHomeomorphism ΦZ.left]

namespace WeilBoundedConstructible

variable (ℓ) in
/-- The operator `E_Z` on `RΓ_c(X, Ri_* Li^* K)`: the compactly supported Frobenius of the
restriction `K|_Z`, transported along `Ra_{X!} Ri_* ≅ Ra_{Z!}`. -/
noncomputable def compactFrobeniusClosedPiece (hi : ΦZ ≫ i = i ≫ Φ)
    (K : WeilBoundedConstructible ℓ Φ) :
    (boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        ((boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)) ⟶
      (boundedConstructibleLowerShriek ℓ (toPoint X)).obj
        ((boundedConstructibleLowerStar ℓ i).obj
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)) :=
  (boundedConstructibleLowerStarCompToPoint ℓ i).hom.app
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier) ≫
    ((compactPullback ℓ ΦZ).app ((boundedConstructibleUpperStar
      (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint Z)).map
        ((weilUpperStarComparison ℓ ΦZ Φ i hi).hom.app K.carrier ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).map K.str.hom)) ≫
    (boundedConstructibleLowerStarCompToPoint ℓ i).inv.app
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i).obj K.carrier)

end WeilBoundedConstructible

end Frobenius

end AlgebraicGeometry.ProEtale.CondensedRing
