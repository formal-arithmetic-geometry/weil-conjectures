/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G7
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind

/-!
# Extending a specified constructible Ext bound to ind-constructible sheaves

Source: blueprint latest, sec-six-functors-basics/sk-cor-ind-heart-ii/_section.md,
vanishing clause, used by the one-cohomology case of det-finite-window-bounded.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A specified bound against constructible sheaves also bounds Ext into an
ind-constructible sheaf. The coefficient equality includes the multiplication,
via bundled monoid objects. This is the sheaf input to bounded-complex devissage.

Source: blueprint latest, sk-cor-ind-heart-ii, vanishing clause, and
sk-lem-finite-window-bounded.proof.md, one-cohomology case
(blueprint: lem-finite-window-ind-ext-bound).

Proof: choose a small filtered constructible presentation B = colim B_i.
The filtered-colimit Ext comparison of sk-lem-constructible-ext-continuity,
clause (1), identifies Ext^r(C,B) with colim Ext^r(C,B_i). Every stage group is
zero by the supplied bound since d < r. A colimit of zero abelian groups is
zero; transporting along the comparison gives the claim. This uses only
sheaves, viewed as complexes in degree zero, so the common lower bound is zero.
The source states this for arbitrary X. The existing theorem
indHeartII_vanishing has additional Noetherian hypotheses and cannot discharge
this general-scheme input; that applicability gap is retained here explicitly. -/
theorem constructibleInd_extBound
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hΛ : Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj E) ∨
      Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (X : Scheme.{u})
    (C : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (_hC : IsConstantModelConstructible Λ X C)
    (d : ℕ)
    (hbound : ∀ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X),
      IsConstantModelConstructible Λ X N → ∀ r : ℕ, d < r →
        Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C N r))
    (B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hB : ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) B)
    (r : ℕ) (hr : d < r) :
    Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C B r) := by sorry

end AlgebraicGeometry.ProEtale
