/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Paper.CondensedConstantConstructibility
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.Paper.ProEtaleSurjectiveClosedCoverRefinement
import Sheaf.Paper.CondensedSurjectiveClosedEquivalence

/-!
# Reflection of integral finite constant models across surjective closed immersions

Source: Stacks Project, Tags 09AB and 09BK; blueprint main-20261015,
`det-lem-int-ext-formula`, proof (1)
(blueprint: lem-sfb-integral-model-surjective-closed-reflection).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The condensed valuation ring of the finite p-adic extension, with continuous-function
sections and the topology of the unique extending spectral absolute value. This merely
specializes the existing continuous coefficient construction.
Source: blueprint det-lem-int-ext-formula, proof (1)
(blueprint: lem-sfb-integral-model-surjective-closed-reflection). -/
noncomputable def integralModelCondensedCoefficients (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  letI := spectralNorm.normedField (Padic l) E
  Mon.mk (Profinite.continuousCoefficientRingObj (Padic.coefficientExtensionIntegers l E))

/-- The integral condensed coefficient ring is commutative, by its pointwise operations.
Source: blueprint det-lem-int-ext-formula, proof (1)
(blueprint: lem-sfb-integral-model-surjective-closed-reflection). -/
noncomputable instance integralModelCondensedCoefficients_isCommMonObj
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    IsCommMonObj (integralModelCondensedCoefficients l E).X :=
  letI := spectralNorm.normedField (Padic l) E
  inferInstanceAs (IsCommMonObj
    (Profinite.continuousCoefficientRingObj (Padic.coefficientExtensionIntegers l E)))


attribute [local irreducible] upperStar lowerStar upperStarFromPoint
  CondensedRing.upperStarComp upperStarFromPointComp
  Mod.extendScalarsIsoComapInv

private theorem pointModelPullback {S T : Scheme.{u}} (f : S ⟶ T)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    Nonempty ((CondensedRing.upperStar Λ f).obj
      (((upperStarFromPoint T).mapMod Λ).obj P) ≅
        ((upperStarFromPoint S).mapMod Λ).obj P) := by
  let φ := condensedPullbackHom Λ f
  let N := ((upperStarFromPoint S).mapMod Λ).obj P
  let e := (Functor.mapModCompIso (upperStarFromPoint T) (upperStar Ab.{u + 1} f)
    (upperStarFromPointComp f).hom Λ).app P
  exact ⟨(Mod.extendScalars φ).mapIso e ≪≫
    (Mod.extendScalarsIsoComapInv φ).app ((Mod.comap φ).obj N) ≪≫
      (Mod.comapEquivalenceOfIsIso φ).unitIso.symm.app N⟩

-- Keep the composition comparison abstract when applying it to chosen pullback maps.
private theorem modulePullbackSquare
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y S T : Scheme.{u}}
    (f : S ⟶ X) (g : Y ⟶ X) (p : T ⟶ S) (q : T ⟶ Y)
    (h : p ≫ f = q ≫ g)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Nonempty ((CondensedRing.upperStar Λ p).obj ((CondensedRing.upperStar Λ f).obj M) ≅
      (CondensedRing.upperStar Λ q).obj ((CondensedRing.upperStar Λ g).obj M)) := by
  exact ⟨((CondensedRing.upperStarComp Λ p f).app M).symm ≪≫
    eqToIso (congrArg (fun k ↦ (CondensedRing.upperStar Λ k).obj M) h) ≪≫
      (CondensedRing.upperStarComp Λ q g).app M⟩

private theorem pointModelSquare
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y S T : Scheme.{u}}
    (f : S ⟶ X) (g : Y ⟶ X) (p : T ⟶ S) (q : T ⟶ Y)
    (h : p ≫ f = q ≫ g)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (he : Nonempty ((CondensedRing.upperStar Λ g).obj M ≅
      ((upperStarFromPoint Y).mapMod Λ).obj P)) :
    Nonempty ((CondensedRing.upperStar Λ p).obj ((CondensedRing.upperStar Λ f).obj M) ≅
      ((upperStarFromPoint T).mapMod Λ).obj P) := by
  obtain ⟨e⟩ := he
  obtain ⟨es⟩ := modulePullbackSquare Λ f g p q h M
  obtain ⟨em⟩ := pointModelPullback q Λ P
  exact ⟨es ≪≫ (CondensedRing.upperStar Λ q).mapIso e ≪≫ em⟩

-- An existential cover interface keeps chosen scheme-limit constructions out of
-- the coefficient functors' dependent types.
private theorem exists_pullback_cover {X Z : Scheme.{u}} (i : Z ⟶ X)
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X) :
    ∃ B : Scheme.Cover.{u} Scheme.proetalePrecoverage Z,
      ∃ (a : B.I₀ → C.I₀) (q : ∀ b, B.X b ⟶ C.X (a b)),
        ∀ b, B.f b ≫ i = q b ≫ C.f (a b) := by
  refine ⟨C.pullback₁ i, id, fun b ↦ pullback.snd i (C.f b), fun b ↦ ?_⟩
  exact pullback.condition

private theorem finiteConstantModel_reflection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [Surjective i]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    HasFiniteConstantLocalModel Λ X F ↔
      HasFiniteConstantLocalModel Λ Z ((CondensedRing.upperStar Λ i).obj F) := by
  classical
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨B, a, q, hs⟩ := exists_pullback_cover i C
    refine ⟨B, fun b ↦ ?_⟩
    obtain ⟨P, hP, he⟩ := hC (a b)
    refine ⟨P, hP, ?_⟩
    exact pointModelSquare Λ i (C.f (a b)) (B.f b) (q b) (hs b) F P he
  · rintro ⟨C, hC⟩
    obtain ⟨B, hB⟩ := Scheme.exists_cover_refinement_surjective_closed i C
    refine ⟨B, fun b ↦ ?_⟩
    obtain ⟨a, W, q, p, r, hsq, hr⟩ := hB b
    obtain ⟨P, hP, ⟨e⟩⟩ := hC a
    have : IsClosedImmersion q :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip inferInstance
    have : Surjective q :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip inferInstance
    have : (CondensedRing.upperStar Λ q).IsEquivalence :=
      condensedSurjectiveClosedPullback_isEquivalence Λ q
    obtain ⟨er⟩ := pointModelPullback r Λ P
    obtain ⟨eq⟩ := pointModelPullback q Λ P
    let ep : (CondensedRing.upperStar Λ q).obj
        ((CondensedRing.upperStar Λ (B.f b)).obj F) ≅
      (CondensedRing.upperStar Λ q).obj
        (((upperStarFromPoint (B.X b)).mapMod Λ).obj P) :=
      calc
        _ ≅ (CondensedRing.upperStar Λ (q ≫ B.f b)).obj F :=
          ((CondensedRing.upperStarComp Λ q (B.f b)).app F).symm
        _ ≅ (CondensedRing.upperStar Λ (p ≫ i)).obj F :=
          eqToIso (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).obj F) hsq.w)
        _ ≅ (CondensedRing.upperStar Λ p).obj ((CondensedRing.upperStar Λ i).obj F) :=
          (CondensedRing.upperStarComp Λ p i).app F
        _ ≅ (CondensedRing.upperStar Λ (r ≫ C.f a)).obj
            ((CondensedRing.upperStar Λ i).obj F) :=
          eqToIso (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).obj
            ((CondensedRing.upperStar Λ i).obj F)) hr.symm)
        _ ≅ (CondensedRing.upperStar Λ r).obj
            ((CondensedRing.upperStar Λ (C.f a)).obj
              ((CondensedRing.upperStar Λ i).obj F)) :=
          (CondensedRing.upperStarComp Λ r (C.f a)).app
            ((CondensedRing.upperStar Λ i).obj F)
        _ ≅ (CondensedRing.upperStar Λ r).obj
            (((upperStarFromPoint (C.X a)).mapMod Λ).obj P) :=
          (CondensedRing.upperStar Λ r).mapIso e
        _ ≅ ((upperStarFromPoint W).mapMod Λ).obj P := er
        _ ≅ _ := eq.symm
    exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ q).preimageIso ep⟩⟩

/-- A module has finite constant integral local models exactly when its pullback across a
surjective closed immersion does. In the existing `HasFiniteConstantLocalModel` interface,
scalar models are finite presentations on the point. Their matrices have entries in
`A = O_E`, and their pullbacks are `B_U ⊗_{A_U} P_U` through the constant-section map.
Since A is a DVR, its finitely generated modules are exactly its finitely presented modules;
thus this includes torsion modules and allows a different module on each cover member.

Source: Stacks Project Tags 09AB and 09BK; blueprint det-lem-int-ext-formula, proof (1)
(blueprint: lem-sfb-integral-model-surjective-closed-reflection).

Proof:
1. Write C_T(P) for the scalar-extension model. The abelian inverse image is strong
monoidal and preserves colimits (`lem-weil-pbc-left-exact-site-inverse-image-tensor`).
It preserves constant abelian sheaves by their presentations by sums of copies of Z.
Apply it to the relative tensor coequalizer of `sk-def-sfb-change-of-scalars`. The
untwisted coefficient isomorphism of `sk-prop-sfb-cartesian-coefficients` identifies
f^* C_T(P) with C_S(P), without flatness or freeness assumptions on P.
2. Pull the covering in (a) back to Z using `def-weil-proetale-inverse-image`.
The composition isomorphisms of `sk-def-sfb-module-pushforward-pullback` and step 1 give
(b), using the same scalar modules.
3. Conversely apply `new-lem-weil-pbc-proetale-surjective-closed-cover-refinement` to
the cover in (b). It gives a cover T_gamma of X whose closed fibres W_gamma refine
that cover of Z. The projections W_gamma -> T_gamma are surjective closed immersions,
by `lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism`.
4. Pull the models in (b) to W_gamma and use step 1 and composition of module pullbacks.
By `new-lem-weil-pbc-condensed-surjective-closed-equivalence`, pullback from T_gamma to
W_gamma is fully faithful. Lift each model isomorphism and its inverse by fullness;
faithfulness verifies their composites are identities. This gives (a) on the cover
T_gamma without gluing different models. No Noetherianity or nilpotence bound is used. -/
theorem integralModel_surjective_closed_reflection
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [Surjective i]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralModelCondensedCoefficients l E).X X)) :
    HasFiniteConstantLocalModel (integralModelCondensedCoefficients l E).X X F ↔
      HasFiniteConstantLocalModel (integralModelCondensedCoefficients l E).X Z
        ((CondensedRing.upperStar (integralModelCondensedCoefficients l E).X i).obj F) := by
  exact finiteConstantModel_reflection (integralModelCondensedCoefficients l E).X i F

end AlgebraicGeometry.ProEtale
