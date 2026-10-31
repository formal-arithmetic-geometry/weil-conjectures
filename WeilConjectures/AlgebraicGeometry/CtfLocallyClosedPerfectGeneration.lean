/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyConstantPerfectComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

/-! # Finite generation by scalar-perfect pieces

Source: current blueprint, internal-Hom stability proof, Steps 3--5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Finite triangulated generation by locally closed scalar-perfect pieces.
Source: internal-Hom stability proof, Steps 3--5
(blueprint: lem-sfb-ctf-locally-closed-perfect-generation).

Proof: Make the finite locally closed stratification adapted to the finitely many terms
or cohomology sheaves an ordered refinement with open prefixes V_r. Extension by zero
of the open--closed short exact sequences gives distinguished triangles with vertices
C_(r-1), C_r and the extension of the restriction to stratum r. Start at zero and
induct over the finite number of strata. Coherence identifies these extensions with
open extension followed by closed direct image for the chosen factorization.
For finite coefficients descend to the etale site and use a bounded flat constructible
model. Its termwise local scalar models are finite flat modules over a Noetherian ring,
hence finitely presented projective. Pull back exactly to the pro-etale site. Apply
the preceding stratification induction to each term and then use the stupid truncation
triangles of the bounded model. For integral coefficients the local-model theorem gives
bounded completed finite free complexes on the strata, so apply the stratification
induction directly to the complex. For rational coefficients use the lisse finite free
quotients of the constructible-heart filtration, and then the finitely many cohomological
truncation triangles. Transport through coefficient isomorphisms. Every induction uses
only finitely many cones and shifts, never retracts. On an empty scheme the empty
filtration starts and ends at zero, which belongs to any triangulated Q. -/
theorem ctf_locallyClosedPerfect_generation
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (K : (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    (hK : constantModelBoundedConstructible Λ X K ∧ DerivedCategory.finiteTorAmplitude _ K)
    (Q : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    [Q.IsTriangulated] [Q.IsClosedUnderIsomorphisms]
    (hQ : ∀ (S Z : Scheme.{u}) (j : S ⟶ Z) (i : Z ⟶ X)
      [IsOpenImmersion j] [IsClosedImmersion i] (P : (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)))),
      IsLocallyConstantPerfectComplex Λ S P →
      Q (((openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
        (lowerStar Λ i).rightDerivedFunctor).obj P)) : Q K := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
