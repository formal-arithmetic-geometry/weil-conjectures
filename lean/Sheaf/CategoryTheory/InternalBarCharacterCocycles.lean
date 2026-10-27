/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.CategoryTheory.InternalBarCharacterData

/-! # Ordered products as internal inhomogeneous cocycles

This calculation only uses the inhomogeneous bar and the characters.
Source: agent-written internal bar calculation, step 5
(blueprint: lem-sfb-internal-bar-character-cocycles).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open Profinite.CondensedAction Profinite.CondensedAction.InternalBar
open CategoryTheory.CondensedDerivedRestriction (Character)
namespace Profinite.CondensedAction.InternalBarCharacter
variable {A : CategoryTheory.CondensedBar.Ring.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The ordered character product is a linear internal inhomogeneous cocycle,
including the constant unit cocycle for the empty list.
Source: lem-sfb-internal-bar-character-lifts, proof step 5, agent-written
internal-bar expansion of blueprint direct-images paragraph (3).
(blueprint: lem-sfb-internal-bar-character-cocycles).

Proof: On a profinite slice T over S assign to a tuple g the product of the
character values times the restricted scalar r. Character naturality and the
ring restriction laws prove this is a natural function family. The evaluation
equivalence supplies a section of the internal function module. Its additive,
scalar, and restriction laws give an internal A-linear map A to the degree-q
function module. Transport it through B.term to the bar term. Its differential
is the alternating sum of the faces specified by B.face. The coefficient action
is trivial. Expand each interior a_i(g_i g_(i+1)) using the character addition
law and distribute the product. The resulting terms cancel consecutively with
the adjacent face, including the first dropping face and the last dropping
face. For q=0 the two faces are 1-1. The differential therefore vanishes on
every slice. Evaluation is injective, so it vanishes internally. Extend the
map to the single complex supported in degree q by mkHomFromSingle. Transport
back through the term isomorphisms gives the displayed scalar formula.
This argument is independent of any homogeneous resolution or chosen deletion
lifts; empty slices, zero coefficients and zero characters cause no exception.
-/
theorem exists_product_cocycle
    {H : CategoryTheory.CondensedBar.InternalFunctions A}
    (B : CategoryTheory.CondensedBar.BarDiagram (G := G) H)
    (a : List (Character A G)) :
    ∃ c : (HomologicalComplex.single (Modules A.toMon) (.up ℤ) (a.length : ℤ)).obj
        (Mod.regular A.X) ⟶ CategoryTheory.CondensedBar.extend
          ((CategoryTheory.CondensedBar.cochains B).obj
            ((trivial (R := A.toMon) (P := G)).obj (Mod.regular A.X))),
    ∀ (S : Profinite.{u}) (r : CategoryTheory.CondensedBar.sectionRing A S)
      (T : Profinite.{u}) (f : T ⟶ S) (g : Fin a.length → C(T, G)),
    (H.evaluate (CategoryTheory.CondensedBar.power G a.length) S (Mod.regular A.X)
      (onSections A.toMon (cocycleComponent B c) S r)).val T f
        (CategoryTheory.CondensedBar.tupleMap g) =
      (InternalAbelianSheafModule.sectionRingSheaf
        (coherentTopology Profinite.{u}) A.X).obj.map f.op r *
          ∏ k : Fin a.length, (a.get k).app T (g k) := by sorry

end Profinite.CondensedAction.InternalBarCharacter
