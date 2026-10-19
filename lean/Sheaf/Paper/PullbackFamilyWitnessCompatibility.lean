/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P6
-/
module

public import Sheaf.Paper.WitnessCompatibility
import Sheaf.Paper.FamilyWitnessCompatibilityFromOrigins
import Sheaf.Paper.EtaleProEtaleScalarMate

/-! # Witness compatibility for one inverse-image family

This is the pullback half of amplification step (b).
Source: blueprint main-20261015, sec-proper-base-change/sk-thm-properbasechange,
`thm-weil-pbc-amplification-proper.proof.md`
(blueprint: lem-weil-pbc-pullback-family-witness-compatibility).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale


variable {A : Type (u + 1)} [CommRing A]

private def pullbackCoordinates {X Y : Scheme.{u}} (g : Y ⟶ X)
    (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    pbcWitnessPullback g d n ≅
      (upperStar (ModuleCat.{u + 1} (PbcQuotient d n)) g).mapDerivedCategory := by
  let R := finiteCoefficientRealization X (PbcQuotient d n)
  let S := finiteCoefficientRealization Y (PbcQuotient d n)
  let U := upperStar (ModuleCat.{u + 1} (PbcQuotient d n)) g
  let Ri := finiteCoefficientUnrealization X (PbcQuotient d n)
  let Si := finiteCoefficientUnrealization Y (PbcQuotient d n)
  letI : R.asEquivalence.functor.Additive := finiteCoefficientRealization_additive X _
  letI : S.asEquivalence.functor.Additive := finiteCoefficientRealization_additive Y _
  let eR : R.mapDerivedCategory ⋙ Ri.mapDerivedCategory ≅ 𝟭 _ :=
    R.asEquivalence.mapDerivedCategory.unitIso.symm
  let eS : S.mapDerivedCategory ⋙ Si.mapDerivedCategory ≅ 𝟭 _ :=
    S.asEquivalence.mapDerivedCategory.unitIso.symm
  refine Functor.isoWhiskerLeft R.mapDerivedCategory
    (Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryCompIso Ri (U ⋙ S) ≪≫
        Functor.isoWhiskerLeft Ri.mapDerivedCategory (Functor.mapDerivedCategoryCompIso U S))
      Si.mapDerivedCategory) ≪≫ ?_
  exact Functor.isoWhiskerRight eR (U.mapDerivedCategory ⋙ S.mapDerivedCategory ⋙
    Si.mapDerivedCategory) ≪≫
    Functor.isoWhiskerLeft U.mapDerivedCategory eS ≪≫ U.mapDerivedCategory.rightUnitor

private def pullbackRho {X Y : Scheme.{u}} (g : Y ⟶ X)
    (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    pbcWitnessPullback g d (n + 1) ⋙ pbcWitnessReduction Y d n ≅
      pbcWitnessReduction X d n ⋙ pbcWitnessPullback g d n :=
  Functor.isoWhiskerRight
    (pullbackCoordinates g d (n + 1) ≪≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1}
        (PbcQuotient d (n + 1))) g).symm) _ ≪≫
    (scalarPullbackProEtaleIso
      (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n)) g).symm ≪≫
    Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} (PbcQuotient d n)) g ≪≫
        (pullbackCoordinates g d n).symm)

private def pullbackOrigin {X Y : Scheme.{u}} (g : Y ⟶ X)
    (d : Scheme.AdicCoefficientDatum A) (P : PbcWitnessedInputTowers X d) (n : ℕ) :
    (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) Y).mapDerivedCategory.obj
      (Functor.obj
        (Etale.upperStar (ModuleCat.{u + 1} (PbcQuotient d n)) g).mapDerivedCategoryPlus
        (P.obj.origin n).L).obj ≅
      (pbcWitnessPullback g d n).obj (P.obj.K n) := by
  let Λ := PbcQuotient d n
  exact (Functor.mapDerivedCategoryCompIso _ _).symm.app _ ≪≫
    (Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm).app _ ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).app _ ≪≫
    (upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategory.mapIso (P.obj.alpha n) ≪≫
    (pullbackCoordinates g d n).symm.app _


/-- Exact inverse image transports normalized bounded constructible input towers
with retained etale origins and their quotient normalizations, functorially.
Source: blueprint main-20261015, sec-proper-base-change/sk-thm-properbasechange,
thm-weil-pbc-amplification-proper.proof.md, step (b); the nonperfect-quotient
projection-formula repair is the argument recorded in that node's proof steps 3-4.
(blueprint: lem-weil-pbc-pullback-family-witness-compatibility).

Proof: fix consecutive quotient rings B and C. Inverse image of module sheaves with
constant coefficients is exact. Its derived functor is termwise inverse image. The
canonical tensor-pullback comparison, computed on K-flat flat-term representatives,
identifies inverse image of derived B-to-C extension with derived extension of inverse
image. On local generators it sends (x tensor b) tensor c to x tensor q(b)c, with inverse
inserting 1. The universal scalar-extension counits identify this map with the canonical
adjunction mate. Conjugate by the published finite-coefficient realizations; restrict
to the reduction-domain subcategory to get rho.

For an input witnessed tower, take etale inverse images of its retained origins.
Exact inverse image preserves their lower bounds. The canonical comparison-pullback
isomorphism, followed by inverse image of the input alpha, gives each output origin.
Compose rho with pullback of theta to obtain its adjacent normalization. Pull back beta
and use the same tensor comparison to obtain the etale adjacent normalization. Naturality
of the comparison mate in the input alpha proves the retained-origin square. On pairs
of maps apply the two inverse-image functors. Their naturality proves compatibility with
theta, beta and alpha. They preserve identities and composites, so this is a functor on
the input full subcategory. For three quotients, both balancing composites send
((x tensor d) tensor b) tensor c to x tensor q(d)q(b)c. Identity quotient maps give the
unit balancing map. Hence the resulting normalizations have precisely the iterated
quotient convention required in PbcFamilyWitnessCompatibility. No geometric finiteness
or invertibility hypothesis on the scheme map is used. -/
theorem pbcFamilyWitnessCompatibility_pullback
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : Scheme.AdicCoefficientDatum A) :
    PbcFamilyWitnessCompatibility X Y d (pbcWitnessPullback g d) := by
  apply pbcFamilyWitnessCompatibility_of_origins d (pbcWitnessPullback g d)
    (fun n ↦ Functor.isoWhiskerLeft _ (pullbackRho g d n))
    (fun P n ↦ Functor.obj
      (Etale.upperStar (ModuleCat.{u + 1} (PbcQuotient d n)) g).mapDerivedCategoryPlus
      (P.obj.origin n).L)
  exact pullbackOrigin g d

end AlgebraicGeometry.ProEtale
