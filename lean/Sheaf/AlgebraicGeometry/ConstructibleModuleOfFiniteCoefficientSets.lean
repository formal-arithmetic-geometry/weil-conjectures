/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Module constructibility from finite sets and finite coefficients

Source: the normalization exact-sequence blueprint, unit `sk-thm-p1`, module refinement
in lem-weil-pbc-finite-pushforward-finite-stalk-module.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A sheaf annihilated by a finite-index ideal is module constructible when its
underlying set sheaf is constructible.

Source: normalization exact-sequence blueprint, module refinement in
`lem-weil-pbc-finite-pushforward-finite-stalk-module`, step 3.
(blueprint: lem-weil-pbc-constructible-module-of-finite-coefficient-sets)

Proof: The sectionwise annihilation gives every section module its canonical action
of the quotient ring, by quotient induction, and restriction maps remain linear.
Choose the finite constructible stratification and finite-set trivializing covers.
On each nonempty member, the transported addition, zero, and scalar operations are
locally constant maps on finite constant sets. For each input tuple they are locally
constant sections of the finite constant target. Refine the cover to trivialize these
sections, taking finite common refinements for all input tuples and all elements of
the finite quotient ring. Cover transitivity gives the required etale covers.
The identities for the transported operations follow from the original sheaf, yielding
constant finite quotient modules on the refinements. As Lambda-modules these are also
finite and hence finitely generated. The original stratification thus witnesses
IsConstructibleSheaf. Empty strata are discarded; the zero module and zero quotient
ring satisfy the same argument without any nontriviality assumption. -/
theorem isConstructibleSheaf_of_finite_coefficient_underlying_sets
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)))
    (I : Ideal Λ) (hI : Finite (Λ ⧸ I))
    (hkill : ∀ (U : X.Etaleᵒᵖ) (r : Λ), r ∈ I →
      ∀ m : F.obj.obj U, r • m = 0) : IsConstructibleSheaf F := by
  sorry

end AlgebraicGeometry.Scheme
