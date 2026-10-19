/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImages
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Proper direct-image constructibility

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
`thm-fin-proper-constructibility-complete.md`, statement and proof
(blueprint: thm-fin-proper-constructibility-complete).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Every proper morphism between finite-type schemes over a field satisfies `C(f)`:
each nonnegative higher direct image of a constructible finite-coefficient module sheaf
is constructible, with no uniform vanishing assertion.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`,
`thm-fin-proper-constructibility-complete.md`, statement and proof
(blueprint: thm-fin-proper-constructibility-complete).

Proof: The source library already proves proper direct-image constructibility with
finite-stalk constructibility and the total derived direct image. On the empty target,
every sheaf is zero and hence constructible. Otherwise the invertible annihilating
exponent on the target descends to the ground field. Convert the constructibility of
`F` to the finite-stalk convention and apply the source theorem. The compatibility
isomorphism between total and bounded-below right derived functors identifies its
homology sheaf with `higherDirectImage`; transport constructibility through this
isomorphism and convert back to the finite-constant-value convention. -/
theorem hasConstructibleHigherDirectImages_of_proper
    (k : Type u) [Field k] (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S : Scheme.{u}} [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (hX : IsSmoothBaseChangeCoefficients N Λ X)
    (hS : IsSmoothBaseChangeCoefficients N Λ S) (f : X ⟶ S) [IsProper f] :
    HasConstructibleHigherDirectImages k N Λ hX hS f := by
  classical
  intro q F hF
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
  by_cases hS' : IsEmpty S
  · let := hS'
    exact Scheme.IsConstructibleSheaf.of_isZero (Scheme.Etale.isZero_sheaf_of_isEmpty _)
  have : Nonempty S := not_isEmpty_iff.mp hS'
  have : HasInvertibleExponent Λ S := ⟨N, hS.1, hS.2.2.1, hS.2.2.2⟩
  have : HasInvertibleExponent Λ (Spec (.of k)) :=
    .of_hom_of_nonempty (S ↘ Spec (.of k))
  have : Scheme.IsConstructibleSheaf F := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).1 hF
  let A := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F
  have : Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((_root_.DerivedCategory.Plus.ι ⋙
          (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor).obj A)) := by
    change Scheme.IsConstructibleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))
    exact hasConstructibleDirectImages_of_isProper (S ↘ Spec (.of k)) f F inferInstance q
  exact Scheme.IsConstructibleSheaf.of_iso
    ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).mapIso
      ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlusCompatibility.app A).symm)

end AlgebraicGeometry.Etale
