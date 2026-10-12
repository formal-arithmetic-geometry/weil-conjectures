/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections

/-!
# A finite-cover connectedness criterion for abelian étale sections

Source: Stacks Project, Tags 09ZG and 09ZF.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Abelian étale sections restrict isomorphically to a closed subscheme when every
irreducible closed subset of every finite cover meets it in a nonempty connected set.

Source: Stacks Project, Lemmas 59.82.4 and 59.82.2 (Tags 09ZG and 09ZF).
(blueprint: lem-weil-pbc-etale-abelian-h0-finite-connected-criterion)

Proof:
1. Every finite scheme X' over the qcqs scheme X is qcqs and spectral. The base
   change of the closed immersion i is closed and has image h inverse image of
   range i. The hypothesis and Tag 09ZG give bijective restriction of sections
   of every Zariski sheaf of sets on X'. The identity finite cover includes X.
2. Apply Gabber's Tag 09ZF criterion: these Zariski comparisons on X and all
   finite X' imply bijective restriction of sections of every étale sheaf of sets.
3. Apply this to the underlying sheaf of sets of G. Forgetting abelian groups
   preserves limits and filtered colimits. The pointwise inverse-image colimits
   and the local matching families defining sheafification are therefore the
   same after forgetting groups. The natural comparison respects the adjunction
   units, and the terminal base-change comparison identifies their global sections.
4. Thus the underlying function of globalSectionsUpperStarMap is the bijection
   of step 2, conjugated by canonical bijections. A bijective homomorphism of
   abelian groups has an additive inverse, so it is an isomorphism.

The universe of the underlying sets is u+1. This is independent of any henselian
pair, any coefficient ring, and any identification of H^0 with global sections.
For the empty scheme, the condition is vacuous and both section groups are zero. -/
theorem isIso_abelian_globalSectionsUpperStarMap_of_finite_connected_closed_intersections
    {X Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hconn : ∀ (X' : Scheme.{u}) (h : X' ⟶ X) [IsFinite h],
      ∀ C : Set X', IsClosed C → IsIrreducible C →
        IsConnected (C ∩ h ⁻¹' Set.range i))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} i G) := by sorry

end AlgebraicGeometry.Etale
