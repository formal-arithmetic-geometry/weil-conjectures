/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.GroupTheory.Torsion
import Sheaf.AlgebraicGeometry.ProperUnboundedBaseChangeModN
import Sheaf.AlgebraicGeometry.ProperUnboundedBaseChangeForgetful

/-! # Proper base change on unbounded derived categories

The existing unbounded theorem is placed below the bounded proper-base-change proof
modules so that the projection formula can use it without an import cycle.
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme
variable (Λ : Type (u + 1)) [CommRing Λ]
variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- Proper base change for a torsion coefficient ring on unbounded complexes.
Source: Stacks Project, Tag 0F0C, Lemma 59.92.3, and the coefficient-forgetting
comparison of the canonical exchange mates.
(blueprint: lem-kun-proper-base-change-torsion-ring)

Proof in words: choose n > 0 annihilating 1 in Λ. The map Z/nZ → Λ sends the
class of a to a·1. Restricting coefficient scalars termwise is exact, so the input
complex E gives an unbounded Z/nZ-complex Eₙ with exactly the same underlying
abelian complex. Proper unbounded base change for Z/nZ coefficients (Tag 0F0C)
makes its exchange map invertible, for arbitrary base change. The natural
coefficient-forgetting comparisons identify the forgotten exchange mates with
one abelian exchange map. Their endpoint comparison maps are isomorphisms.
For the Z/nZ complex, this shows the abelian exchange is invertible. For E with
Λ coefficients, the same abelian exchange and the comparison isomorphisms show
that its forgotten exchange is invertible. Exact coefficient forgetting reflects
isomorphisms on the unbounded derived categories: it is conservative on homology
sheaves and commutes with homology. Hence the original Λ-linear exchange is
invertible. This comparison concerns the canonical adjunction mate, not merely
isomorphic endpoints. Apply it componentwise and assemble the natural isomorphism.
No boundedness assumption on E or Noetherian assumption on the schemes is used. -/
private theorem Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring_sheaf
    (hΛ : IsAddTorsion Λ)
    [IsProper f] (sq : IsPullback g' f' f g) :
    IsIso (Etale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) := by
  obtain ⟨n, hn, hunit⟩ := (hΛ 1).exists_nsmul_eq_zero
  have h : ∀ K, IsIso ((Etale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
    fun K ↦ isIso_derivedBaseChangeMap_of_isIso_modN Λ n hunit sq
      (Etale.isIso_derivedBaseChangeMap_of_isProper_modN n hn sq) K
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry
