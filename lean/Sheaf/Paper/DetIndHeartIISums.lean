/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Paper.ConstructibleExtContinuity
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian

/-!
# Ext out of a constructible sheaf commutes with sums of ind-constructible sheaves

Source: blueprint main-20261015, sec-six-functors-basics/sk-cor-ind-heart-ii,
node det-ind-heart-ii-sums (blueprint: det-ind-heart-ii-sums).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits DirectSum
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Ext out of a constructible module sheaf preserves arbitrary coproducts of
ind-constructible module sheaves.
Source: blueprint main-20261015, sec-six-functors-basics/sk-cor-ind-heart-ii,
node det-ind-heart-ii-sums (blueprint: det-ind-heart-ii-sums).

Proof:
1. View the ambient category as sheaves of modules over the commutative ring sheaf
   `Λ_X`; its module-object construction is `CategoryTheory.Mod`.  For every finite
   subfamily `T ⊆ S`, the coproduct is a biproduct.  The inclusions and projections
   satisfy the two biproduct identities, so postcomposition gives an additive
   isomorphism from the finite direct sum of Ext groups to the Ext group of the
   finite coproduct, with inverse given by postcomposition with the projections.
   These identities hold for degree-zero complexes in the derived category and after
   every integer shift.
2. The finite subsets of `S`, ordered by inclusion, form a small filtered category,
   including the empty subset.  The coproduct over `S` is the filtered colimit of the
   finite subcoproducts, and the same is true in abelian groups for the Ext groups.
   The required colimits exist in the ambient module category.
3. Apply the constructible Ext-continuity statement to this filtered diagram, the
   constructible source `C`, and the chosen coefficient ring.  It identifies the
   filtered colimit of the finite comparisons with the comparison for the full
   coproduct.  The finite inverses are compatible with the transition maps, so they
   induce an inverse on colimits.  On the `s`-th summand this composite is exactly
   postcomposition with the shifted coprojection, which is the displayed map.
-/
theorem det_ind_heart_ii_sums
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : Λ = Profinite.continuousMapRingObj E ∨
      Λ = Profinite.padicAlgClRingObj ℓ)
    (C : CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))
    (hC : IsConstantModelConstructible Λ X C)
    (q : ℤ) (S : Type (u + 1))
    (B : S → CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))
    (hB : ∀ s : S, ObjectProperty.ind
      (IsConstantModelConstructible Λ X) (B s))
    (c : Cofan B) (hc : IsColimit c) :
    Function.Bijective
      (@DirectSum.toAddMonoid S _ _ (Classical.decEq S) _ _ (fun s : S ↦
        Preadditive.rightComp ((DerivedCategory.singleFunctor _ 0).obj C)
          ((shiftFunctor _ q).map ((DerivedCategory.singleFunctor _ 0).map (c.inj s)))) :
        (⨁ s : S,
          ((DerivedCategory.singleFunctor _ 0).obj C ⟶
            (shiftFunctor _ q).obj ((DerivedCategory.singleFunctor _ 0).obj (B s)))) →+
          ((DerivedCategory.singleFunctor _ 0).obj C ⟶
            (shiftFunctor _ q).obj ((DerivedCategory.singleFunctor _ 0).obj c.pt))) := by
  sorry

end AlgebraicGeometry.ProEtale
