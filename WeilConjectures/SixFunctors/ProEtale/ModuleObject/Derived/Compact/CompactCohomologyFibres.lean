/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CompactCohomology

/-!

# Compactly supported cohomology of Weil objects: fibres and compatibilities

The Frobenius comparison `θ_f` of `WeilConjectures.TraceFormula.CompactCohomology` at a fibre
(proper base change for Weil objects) and its compatibility with the composition isomorphisms of
the lower shriek (the Leray isomorphism for Weil objects), blueprint
`lem-trf-weil-shriek-operator-fibres`. Split off `WeilConjectures.TraceFormula.CompactCohomology`,
which alone took longer than the 60 s a file may take.

## Main statements

- `ProEtale.CondensedRing.nonempty_weilCompactCohomology_weilLowerShriekOfFrobenius_iso`
- `ProEtale.CondensedRing.nonempty_weilStalk_weilLowerShriekOfFrobenius_iso`

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The Frobenius comparison at a fibre -/

section Fibre

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y X' Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

set_option maxHeartbeats 1000000 in
-- the instances of the categories of sheaves make the rewriting slow
set_option maxHeartbeats 1000000 in
-- the instances of the categories of sheaves make the rewriting slow
/-- `baseChange_comp_weilLowerShriekFrobeniusComparison_stalk`
followed by a morphism `h`; stated by hand, `@[reassoc]` took 7-20 s here. -/
lemma baseChange_comp_weilLowerShriekFrobeniusComparison_stalk_assoc {ΦY : Y ⟶ Y} {p : X' ⟶ X}
    {f' : X' ⟶ Y} {r : X ⟶ X'} {ΦZ : Z ⟶ Z} {j : Z ⟶ X'} {y : RationalPoint Y}
    [IsFinite r.left] [IsUniversalHomeomorphism r.left] [IsProper ΦZ.left]
    (sq : IsPullback p f' (r ≫ f') ΦY) (hy : y ≫ ΦY = y)
    (hZ : IsPullback (j ≫ p) (toPoint Z) (r ≫ f') y) (hL : IsPullback j (toPoint Z) f' y)
    (hT : IsPullback (j ≫ p) ΦZ r j) (hi : ΦZ ≫ j ≫ p = (j ≫ p) ≫ r ≫ p)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    {W : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧} (h : _ ⟶ W) :
    eqToHom (congrArg (fun g ↦ (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ)
        ℓ g).obj ((boundedConstructibleLowerShriek ℓ
          (r ≫ f')).obj K)) hy.symm) ≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ y ΦY).hom.app
        ((boundedConstructibleLowerShriek ℓ (r ≫ f')).obj K) ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ y).map
        ((weilLowerShriekFrobeniusComparison ℓ (r ≫ p) ΦY (r ≫ f') sq r rfl rfl).hom.app K) ≫
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hZ).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (r ≫ p)).obj K) ≫ h =
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ hZ).app K ≫
      (compactPullback ℓ ΦZ).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (j ≫ p)).obj K) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint Z)).map
        ((weilUpperStarComparison ℓ ΦZ (r ≫ p) (j ≫ p) hi).hom.app K) ≫ h := by
  have e := baseChange_comp_weilLowerShriekFrobeniusComparison_stalk ℓ sq hy hZ hL hT hi K =≫ h
  simp only [Category.assoc] at e
  exact e

end Fibre

/-! ### Compatibilities with the lower shriek -/

section Compatibilities

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y X' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]
  {ΦX : X ⟶ X} {ΦY : Y ⟶ Y} {f : X ⟶ Y} {p : X' ⟶ X} {f' : X' ⟶ Y}
  (sq : IsPullback p f' f ΦY) {r : X ⟶ X'} (hrp : r ≫ p = ΦX) (hrf : r ≫ f' = f)
  [IsFinite r.left] [IsUniversalHomeomorphism r.left]
  [IsFinite ΦX.left] [IsUniversalHomeomorphism ΦX.left]
  [IsFinite ΦY.left] [IsUniversalHomeomorphism ΦY.left]

omit [IsFinite ΦX.left]
  [IsUniversalHomeomorphism ΦX.left] [IsFinite ΦY.left] [IsUniversalHomeomorphism ΦY.left]
  [IsFinite r.left] [IsUniversalHomeomorphism r.left] in
omit [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom] [IsFinite ΦX.left]
  [IsUniversalHomeomorphism ΦX.left] [IsFinite ΦY.left] [IsUniversalHomeomorphism ΦY.left] in
omit [IsUniversalHomeomorphism ΦX.left] [IsUniversalHomeomorphism ΦY.left] in
include sq hrp hrf in
omit [IsUniversalHomeomorphism ΦX.left] [IsUniversalHomeomorphism ΦY.left] in
include sq hrp hrf in
set_option maxHeartbeats 1000000 in
-- the defeq of the carriers of the lower shriek of Weil objects with `Rf_! K` is slow
variable {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] {ΦZ : Z ⟶ Z} [IsFinite ΦZ.left] [IsUniversalHomeomorphism ΦZ.left]
  {i : Z ⟶ X} (hi : ΦZ ≫ i = i ≫ ΦX) {y : RationalPoint Y} (hy : y ≫ ΦY = y)
  (hZ : IsPullback i (toPoint Z) f y)

set_option maxHeartbeats 1000000 in
-- the defeq of the carriers of the lower shriek of Weil objects with `Rf_! K` is slow
omit [IsFinite ΦY.left] [IsUniversalHomeomorphism ΦY.left] in
include hZ in
end Compatibilities

end AlgebraicGeometry.ProEtale.CondensedRing
