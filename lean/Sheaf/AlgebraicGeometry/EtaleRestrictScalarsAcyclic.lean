/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic

/-! # Restricted injective module sheaves are direct-image acyclic -/

@[expose] public section

universe u

open CategoryTheory
open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- An injective sheaf remains acyclic for étale direct image after restriction of
coefficients. This does not assert that restriction preserves injective objects.

Source: Stacks Project, Tag 03FD, proof, together with Tag 0D6J(3).
Proof: an injective sheaf of Λ'-modules has vanishing positive cohomology on every
object of the étale site, even after forgetting to abelian sheaves, by the Čech
acyclicity argument in 03FD. Restriction along φ does not change this abelian sheaf.
The same argument on each slice identifies its Λ-module cohomology with its abelian
cohomology. The presheaf computing the positive higher direct image along f thus
vanishes on every étale object over W: its value is the cohomology on the pullback
étale object over Z. Its sheafification is zero. Hence every positive classical
right derived functor of f_* vanishes on the restricted sheaf, which is precisely
`rightAcyclic`. No flatness of φ or quasi-compactness of f is required.
(blueprint: lem-sbc-restrict-scalars-injective-direct-image-acyclic) -/
theorem restrictScalars_injective_lowerStar_rightAcyclic
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {Z W : Scheme.{u}} (f : Z ⟶ W)
    (I : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ')) [Injective I] :
    ((f)_*[ModuleCat.{u + 1} Λ]).rightAcyclic
      ((Sheaf.restrictScalars Z.smallEtaleTopology φ).obj I) := by sorry

end AlgebraicGeometry.Etale
