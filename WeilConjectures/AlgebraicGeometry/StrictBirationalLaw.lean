/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeBirationalMaps

/-! # Strict birational laws and their left-translation charts

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 5.2 Definition 1 and the
construction preceding Lemma 4, printed pp.114--118
(blueprint: def-sfb-strict-birational-law).

Associativity is equality on a fibrewise dense open of the triple product.
The two strict charts retain all six projection-density conditions. Translation
charts specify the actual pullback of the universal left-translation isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RelativeBirational

variable {S : Scheme.{u}}

/-- The square over the base, with its second projection as structure map.
Source: BLR 5.2 Definition 1 (blueprint: def-sfb-strict-birational-law). -/
noncomputable def square (Y : Over S) : Over S :=
  Over.mk (pullback.snd Y.hom Y.hom ≫ Y.hom)

/-- The triple product, with its third projection as structure map.
Source: BLR 5.2 Definition 1 (blueprint: def-sfb-strict-birational-law). -/
noncomputable def cube (Y : Over S) : Over S :=
  Over.mk (pullback.snd (square Y).hom Y.hom ≫ Y.hom)

/-- The first coordinate of the triple product. Source: BLR 5.2 Definition 1
(blueprint: def-sfb-strict-birational-law). -/
noncomputable def cubeFirst (Y : Over S) : (cube Y).left ⟶ Y.left :=
  pullback.fst (square Y).hom Y.hom ≫ pullback.fst Y.hom Y.hom

/-- The second coordinate of the triple product. Source: BLR 5.2 Definition 1
(blueprint: def-sfb-strict-birational-law). -/
noncomputable def cubeSecond (Y : Over S) : (cube Y).left ⟶ Y.left :=
  pullback.fst (square Y).hom Y.hom ≫ pullback.snd Y.hom Y.hom

/-- The third coordinate of the triple product. Source: BLR 5.2 Definition 1
(blueprint: def-sfb-strict-birational-law). -/
noncomputable def cubeThird (Y : Over S) : (cube Y).left ⟶ Y.left :=
  pullback.snd (square Y).hom Y.hom

/-- Associativity of a relative rational multiplication: on a dense common open,
`ab`, `bc`, `a(bc)` and `(ab)c` lie in the multiplication domain, their coordinates
are the indicated ones, and the two results coincide as scheme morphisms.
Source: BLR 5.2 Definition 1 (blueprint: def-sfb-strict-birational-law). -/
def Associative {Y : Over S} (m : PartialMap (square Y) Y) : Prop :=
  ∃ (H : (cube Y).left.Opens) (_ : FibrewiseDense (cube Y).hom H)
    (ab bc a_bc ab_c : H.toScheme ⟶ m.domain.toScheme),
    ab ≫ m.domain.ι ≫ pullback.fst Y.hom Y.hom = H.ι ≫ cubeFirst Y ∧
    ab ≫ m.domain.ι ≫ pullback.snd Y.hom Y.hom = H.ι ≫ cubeSecond Y ∧
    bc ≫ m.domain.ι ≫ pullback.fst Y.hom Y.hom = H.ι ≫ cubeSecond Y ∧
    bc ≫ m.domain.ι ≫ pullback.snd Y.hom Y.hom = H.ι ≫ cubeThird Y ∧
    a_bc ≫ m.domain.ι ≫ pullback.fst Y.hom Y.hom = H.ι ≫ cubeFirst Y ∧
    a_bc ≫ m.domain.ι ≫ pullback.snd Y.hom Y.hom = bc ≫ m.hom ∧
    ab_c ≫ m.domain.ι ≫ pullback.fst Y.hom Y.hom = ab ≫ m.hom ∧
    ab_c ≫ m.domain.ι ≫ pullback.snd Y.hom Y.hom = H.ι ≫ cubeThird Y ∧
    a_bc ≫ m.hom = ab_c ≫ m.hom

/-- Strictness data for an associative birational law. The ambient smoothness,
separatedness, finite type and nonempty-fibre assumptions are supplied by the consumer.
Source: BLR 5.2 Definition 1 (blueprint: def-sfb-strict-birational-law). -/
structure StrictLaw (Y : Over S) where
  mul : PartialMap (square Y) Y
  associative : Associative mul
  leftRange : (square Y).left.Opens
  rightRange : (square Y).left.Opens
  domain_fst_dense : FibrewiseDense (pullback.fst Y.hom Y.hom) mul.domain
  domain_snd_dense : FibrewiseDense (pullback.snd Y.hom Y.hom) mul.domain
  leftRange_fst_dense : FibrewiseDense (pullback.fst Y.hom Y.hom) leftRange
  leftRange_snd_dense : FibrewiseDense (pullback.snd Y.hom Y.hom) leftRange
  rightRange_fst_dense : FibrewiseDense (pullback.fst Y.hom Y.hom) rightRange
  rightRange_snd_dense : FibrewiseDense (pullback.snd Y.hom Y.hom) rightRange
  leftIso : mul.domain.toScheme ≅ leftRange.toScheme
  rightIso : mul.domain.toScheme ≅ rightRange.toScheme
  left_fst : leftIso.hom ≫ leftRange.ι ≫ pullback.fst Y.hom Y.hom =
    mul.domain.ι ≫ pullback.fst Y.hom Y.hom
  left_snd : leftIso.hom ≫ leftRange.ι ≫ pullback.snd Y.hom Y.hom = mul.hom
  right_fst : rightIso.hom ≫ rightRange.ι ≫ pullback.fst Y.hom Y.hom = mul.hom
  right_snd : rightIso.hom ≫ rightRange.ι ≫ pullback.snd Y.hom Y.hom =
    mul.domain.ι ≫ pullback.snd Y.hom Y.hom

/-- The chart obtained by pulling back the universal left translation along `a`.
The equations determine the pairing map and both maps on the open subschemes;
the full inverse-image domains ensure this is the specified canonical pullback.
Source: BLR 5.2, preceding Lemma 4 (blueprint: def-sfb-strict-birational-law). -/
def IsLeftTranslation {Y : Over S} (m : StrictLaw Y) (T : Over S) (a : T ⟶ Y)
    (f : Chart ((Over.pullback T.hom).obj Y)) : Prop :=
  ∃ q : (pullback Y.hom T.hom) ⟶ (square Y).left,
    q ≫ pullback.fst Y.hom Y.hom = pullback.snd Y.hom T.hom ≫ a.left ∧
    q ≫ pullback.snd Y.hom Y.hom = pullback.fst Y.hom T.hom ∧
    f.domain = q ⁻¹ᵁ m.mul.domain ∧ f.codomain = q ⁻¹ᵁ m.leftRange ∧
    ∃ (d : f.domain.toScheme ⟶ m.mul.domain.toScheme)
      (v : f.codomain.toScheme ⟶ m.leftRange.toScheme),
      d ≫ m.mul.domain.ι = f.domain.ι ≫ q ∧
      v ≫ m.leftRange.ι = f.codomain.ι ≫ q ∧
      f.iso.hom ≫ v = d ≫ m.leftIso.hom

end AlgebraicGeometry.RelativeBirational
