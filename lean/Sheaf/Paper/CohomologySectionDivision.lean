/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.Topology.OpenModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import Sheaf.AlgebraicGeometry.Ample
import Sheaf.Paper.NonvanishingSectionTrivializes
import Sheaf.Topology.RestrictInjectiveResolution

/-! # Dividing restricted twisted cohomology by a nonvanishing section

Source: Stacks Project, Tags 09MR and 01CY, construction of the canonical map.
(blueprint: lem-sc-cohomology-section-division)
-/

@[expose] public section

universe uMV

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry

/-- Multiplication by each tensor power of the nonvanishing section is bijective
on cohomology over W intersect S. Its inverse after restriction is compatible with
transition multiplication. This is a statement on individual twists, before either
direct sums or quotient fractions are formed.

Source: Stacks Project, Tag 09MR, canonical map; Tag 01CY, local trivialization.
Proof: The section s trivializes L on S. Its n-th tensor power, tensored with F,
is therefore an isomorphism on S and on every W intersect S. Compute cohomology on
that open using a restricted injective resolution, or equivalently derive the
restriction functor; the functor sends this isomorphism to an isomorphism. This gives
the last bijectivity assertion. Define q by restricting a class to W intersect S
and then applying the inverse cohomology isomorphism. Multiplication followed by
its inverse gives the first formula. To check transition compatibility, multiply
both proposed values by s^(n+b). Naturality of cohomology restriction and the tensor
power identity s^(n+b)=s^n tensor s^b give the same result. Cancel this bijective
multiplication to obtain the second formula. When n=0 this is ordinary restriction;
when s is zero S is empty and all target groups are zero. No quasi-coherence or
compactness hypothesis is used.
(blueprint: lem-sc-cohomology-section-division). -/
theorem exists_cohomologySection_division (X : Scheme.{uMV})
    (L F : X.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    (S : X.Opens) (_hS : (S : Set X) = nonvanishingLocus L s) :
    ∃ q : ∀ (W : X.Opens) (p n : ℕ),
      (openModuleCohomology X.toRingedSpace p W).obj (F ⊗ L.tensorPow n : X.Modules) →+
        (openModuleCohomology X.toRingedSpace p (W ⊓ S)).obj F,
      (∀ (W : X.Opens) (p n : ℕ)
        (ξ : (openModuleCohomology X.toRingedSpace p W).obj (F ⊗ L.tensorPow n : X.Modules)),
        (openModuleCohomology X.toRingedSpace p (W ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (q W p n ξ) =
          (openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_left : W ⊓ S ≤ W))).app (F ⊗ L.tensorPow n : X.Modules) ξ) ∧
      (∀ (W : X.Opens) (p n b : ℕ)
        (ξ : (openModuleCohomology X.toRingedSpace p W).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        q W p (n + b) ((openModuleCohomology X.toRingedSpace p W).map
          (mulTensorPowSection (homOfGlobalSection L s) F n b) ξ) = q W p n ξ) ∧
      (∀ (W : X.Opens) (p n : ℕ), Function.Bijective
        ((openModuleCohomology X.toRingedSpace p (W ⊓ S)).map
          (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
            F ⟶ (F ⊗ L.tensorPow n : X.Modules)))) := by sorry

end AlgebraicGeometry
