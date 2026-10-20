/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage

/-!
# Higher direct images along an open immersion

Source: blueprint `sec-smooth-purity/sk-prop-sf-finiteness/thm-fin-open-immersion.md`
(blueprint: thm-fin-open-immersion).

Constructibility uses the recorded finite-stratification predicate on module sheaves.
The higher direct images are the cohomology sheaves of the derived direct image of `F[0]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Higher direct images of a finite constructible module sheaf under an open immersion
of finite-type schemes over a field are constructible, vanish in sufficiently high degrees,
and restrict to zero on the source in positive degrees.
Source: blueprint `sec-smooth-purity/sk-prop-sf-finiteness/thm-fin-open-immersion.md`
(blueprint: thm-fin-open-immersion).

Proof:
1. The single complex F[0] is bounded constructible by
   def-weil-pbc-constructible-complexes. The coefficient convention supplies a positive
   annihilator N invertible in k. Apply cor-fin-deligne-open-finite-coefficients to F[0].
   Its bounded constructibility gives the constructibility of every cohomology sheaf and
   an upper bound b beyond which all cohomology sheaves vanish.
2. By def-weil-pbc-direct-image choose a bounded-below K-injective representative I of
   F[0] with injective terms. The module derived direct image is represented by j_*I;
   the coefficient category remains that of module sheaves throughout.
3. The abelian counit in lem-kun-open-immersion-restriction is invertible.
   The compatibility in prop-weil-pbc-inverse-image-modules-exact makes its module counit
   invertible as well: the inverse of an invertible linear map is linear. Naturality in
   the differentials assembles the degreewise counits into j^*j_*I ≅ I.
4. The exact module inverse image preserves kernels, images and their quotients, hence
   commutes with the cohomology sheaves of def-weil-derived-cohomology-sheaves. Therefore
   j^*H^q(j_*I) ≅ H^q(j^*j_*I) ≅ H^q(F[0]), which vanishes for q > 0. -/
theorem openImmersion_higherDirectImages_constructible_vanishing
    (k : Type u) [Field k] (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (N : ℕ) (hΛ : IsSmoothBaseChangeCoefficients N Λ (Spec (.of k)))
    {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    (∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((rightDerivedLowerStar (ModuleCat.{u + 1} Λ) j).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) ∧
    (∃ b : ℤ, ∀ q : ℤ, b < q → IsZero
      ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((rightDerivedLowerStar (ModuleCat.{u + 1} Λ) j).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))) ∧
    (∀ q : ℤ, 0 < q → IsZero
      ((upperStar (ModuleCat.{u + 1} Λ) j).obj
        ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((rightDerivedLowerStar (ModuleCat.{u + 1} Λ) j).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F))))) := by
  have : Scheme.IsConstructibleSheaf F :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).1 hF
  have hsingle : DerivedCategory.isBoundedConstructible Λ U
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F) := by
    refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      ((DerivedCategory.boundedConstructible_singleFunctor_obj F 0).2 q),
      0, 0, le_rfl, fun q hq ↦ ?_⟩
    rcases hq with hq | hq
    · exact _root_.DerivedCategory.isZero_of_isGE _ 0 q hq
    · exact _root_.DerivedCategory.isZero_of_isLE _ 0 q hq
  obtain ⟨hc, a, b, hab, hv⟩ :=
    isBoundedConstructible_rightDerivedLowerStar_of_isOpenImmersion k Λ N hΛ
      (X ↘ Spec (.of k)) j _ hsingle
  refine ⟨hc, ⟨b, fun q hq ↦ hv q (Or.inr hq)⟩, fun q hq ↦ ?_⟩
  exact isZero_upperStar_homology_rightDerivedLowerStar_singleFunctor Λ j F q (ne_of_gt hq)

end AlgebraicGeometry.Etale
