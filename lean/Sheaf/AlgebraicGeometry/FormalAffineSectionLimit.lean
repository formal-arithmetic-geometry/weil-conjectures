/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-! # The inverse limit of affine sections of a formal module

Source: Stacks Project, Lemma 087W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Sections on U of a module on the open subscheme U, regarded as a Γ(X,U)-module.
Source: Stacks Project, Lemma 087W, affine sections construction.
(blueprint: lem-weil-pbc-formal-affine-section-limit-full). -/
noncomputable def formalAffineSections (X : Scheme.{u}) (U : X.Opens) :
    U.toScheme.Modules ⥤ ModuleCat.{u} Γ(X, U) :=
  Scheme.Modules.pushforward U.ι ⋙ SheafOfModules.evaluation X.ringCatSheaf (op U)

/-- The tower of affine sections of an adic system, before taking its limit.
Source: Stacks Project, Lemma 087W.
(blueprint: lem-weil-pbc-formal-affine-section-limit-full). -/
noncomputable def formalAffineSectionTower (X : Scheme.{u}) (U : X.Opens)
    [IsNoetherian U.toScheme] (J : U.toScheme.IdealSheafData) :
    CoherentFormalModule U.toScheme J ⥤ (ℕᵒᵖ ⥤ ModuleCat.{u} Γ(X, U)) :=
  ObjectProperty.ι _ ⋙
    (Functor.whiskeringRight ℕᵒᵖ U.toScheme.Modules (ModuleCat.{u} Γ(X, U))).obj
      (formalAffineSections X U)

/-- The actual module limit of the affine section tower; no module witness is chosen.
Source: Stacks Project, Lemma 087W.
(blueprint: lem-weil-pbc-formal-affine-section-limit-full). -/
noncomputable def formalAffineSectionLimit (X : Scheme.{u}) (U : X.Opens)
    [IsNoetherian U.toScheme] (J : U.toScheme.IdealSheafData) :
    CoherentFormalModule U.toScheme J ⥤ ModuleCat.{u} Γ(X, U) :=
  formalAffineSectionTower X U J ⋙ lim

/-- On an affine open, the inverse limit of sections is fully faithful on coherent
formal modules. This concerns arbitrary formal systems and does not identify the
completion of any coherent module.

Source: Stacks Project, Lemma 087W, full faithfulness and the formula N/J^(n+1)N = N_n.
(blueprint: lem-weil-pbc-formal-affine-section-limit-full).

Proof: Identify U with Spec Γ(X,U) and its ideal with the ideal of global sections.
Lemma 087W identifies a formal system with a finite module over the completed ring;
its underlying Γ(X,U)-module is the inverse limit of its section tower. The same
lemma identifies the projections as surjections with kernel J^(n+1) times the limit.
Any Γ(X,U)-linear map between two limits preserves these kernels, hence descends
uniquely to maps on every quotient. The affine tilde/sections equivalence turns them
into sheaf maps between the levels. Surjectivity of the projections proves that the
maps commute with transitions. They therefore give a map of formal systems whose
limit is the given linear map. Conversely a map with zero limit has every component
zero, again by surjectivity, and the affine sections equivalence makes the sheaf map
zero. This proves fullness and faithfulness. The zero and unit ideals give respectively
constant and zero towers; the argument also covers the empty affine open. -/
theorem formalAffineSectionLimit_full_faithful (X : Scheme.{u})
    (U : X.Opens) [IsNoetherian U.toScheme] (hU : IsAffineOpen U)
    (J : U.toScheme.IdealSheafData) :
    (formalAffineSectionLimit X U J).Full ∧
      (formalAffineSectionLimit X U J).Faithful := by sorry

end AlgebraicGeometry
