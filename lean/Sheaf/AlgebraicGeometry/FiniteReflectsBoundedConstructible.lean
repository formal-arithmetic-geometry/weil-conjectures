/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.SixFunctors.Finite.Counit
import Sheaf.AlgebraicGeometry.ConstructibleOfFiniteDirectImage

/-!
# Finite direct image reflects bounded constructibility

Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc/lem-fin-finite-reflects-derived.md
(blueprint: lem-fin-finite-reflects-derived).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Transport the stratification, its covers and its finite constant values along an iso. -/
private theorem constructible_of_iso
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : F ≅ G)
    (hG : Scheme.IsConstructibleEtaleModuleSheaf G) :
    Scheme.IsConstructibleEtaleModuleSheaf F := by
  obtain ⟨S, hS⟩ := hG
  refine ⟨S, fun k ↦ ?_⟩
  obtain ⟨d, hd⟩ := hS k
  let e' := (upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).mapIso e
  let d' : Scheme.LocallyConstantDatum
      ((upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).obj F) :=
    { cover := d.cover
      isConstant := fun i ↦ by
        have := d.isConstant i
        exact Sheaf.isConstant_congr _
          (((S.domain k).smallEtaleTopology.overPullback (ModuleCat.{u + 1} Λ)
            (d.cover.etalePrecoverageToEtale i)).mapIso e').symm }
  refine ⟨d', fun i ↦ ?_⟩
  obtain ⟨M, hM, ⟨iM⟩⟩ := hd i
  exact ⟨M, hM, ⟨((S.domain k).smallEtaleTopology.overPullback
    (ModuleCat.{u + 1} Λ) (d.cover.etalePrecoverageToEtale i)).mapIso e' ≪≫ iM⟩⟩

/-- For a finite morphism of Noetherian schemes and a finite commutative coefficient ring,
the total derived direct image on ordinary, unbounded etale module derived categories
reflects membership in `D^b_c`.

Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc/lem-fin-finite-reflects-derived.md
(blueprint: lem-fin-finite-reflects-derived).

Proof:
1. The finite direct image on module sheaves is exact
(`lemma-weil-pbc-finite-direct-image-exact`). The source library's
`Functor.rightDerivedFunctorHomologyFunctorIso` combines exact-functor descent and
commutation with cohomology, giving `p_* H^q(K) ≅ H^q(Rp_*K)` for every integer q,
without a boundedness hypothesis.
2. The source library's `isZero_of_isZero_lowerStar_of_isFinite` reflects zero objects:
the finite stalk formula (`lemma-weil-pbc-finite-stalk-formula`) identifies each source
stalk as a quotient of a stalk of the image, and geometric stalk conservativity
(`lemma-weil-pbc-geometric-stalk-conservative`) detects the zero sheaf. Apply this to
cohomology outside the bounds of the image. Exactly the same interval bounds K.
3. Transport constructibility along the cohomology comparison by retaining the
stratification and its finite constant values, composing each trivialization with the
restricted comparison. Apply `lem-fin-finite-reflects-constructibility` in every degree.
The definition `def-weil-pbc-constructible-complexes` supplies constructible cohomology
of the image in every degree, so no separate zero-sheaf constructibility lemma is needed. -/
theorem isBoundedConstructible_of_finite_rightDerivedLowerStar
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {Z S : Scheme.{u}} [IsNoetherian Z] [IsNoetherian S]
    (p : Z ⟶ S) [IsFinite p] (K : DerivedCategoryModule Λ Z)
    (hK : DerivedCategory.isBoundedConstructible Λ S
      ((rightDerivedLowerStar (ModuleCat.{u + 1} Λ) p).obj K)) :
    DerivedCategory.isBoundedConstructible Λ Z K := by
  let F := lowerStar (ModuleCat.{u + 1} Λ) p
  have e (i : ℤ) :
      F.obj ((_root_.DerivedCategory.homologyFunctor _ i).obj K) ≅
        (_root_.DerivedCategory.homologyFunctor _ i).obj
          ((rightDerivedLowerStar (ModuleCat.{u + 1} Λ) p).obj K) :=
    (F.rightDerivedFunctorHomologyFunctorIso i).app K
  obtain ⟨hc, a, b, hab, hz⟩ := hK
  refine ⟨fun i ↦ ?_, a, b, hab, fun i hi ↦ ?_⟩
  · apply Scheme.isConstructibleEtaleModuleSheaf_of_finite_lowerStar p
    exact constructible_of_iso (e i) (hc i)
  · apply isZero_of_isZero_lowerStar_of_isFinite (ModuleCat.{u + 1} Λ) p
    exact (hz i hi).of_iso (e i)

end AlgebraicGeometry.Etale
