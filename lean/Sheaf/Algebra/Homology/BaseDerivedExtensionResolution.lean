/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

/-!
# Total derived scalar extension computed on resolutions

Source: Stacks Project, Tag 06Y6, lemma-derived-base-change
(blueprint: lem-pc-base-derived-extension-resolution).
-/

@[expose] public section

set_option autoImplicit false

universe uR uB v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

variable (R : Type uR) (B : Type uB) [CommRing R] [CommRing B]
  [Algebra R B]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uB v} R)]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uB v} B)]

/-- Source: Stacks Project, Tag 06Y6, lemma-derived-base-change, and Tag 06XN.
(blueprint: lem-pc-base-derived-extension-resolution).

Proof: Take K-flat resolutions of all R-complexes. Tensoring a quasi-isomorphism
between K-flat complexes with B in degree zero is a quasi-isomorphism, by the
fixed-second-factor derived tensor construction. Termwise extension is triangulated
on the homotopy category. Apply the resolving-class left-derived construction to
obtain L and its counit, invertible on K-flat models. Every E has a quasi-isomorphism
P to E with P K-flat, giving the last clause. For unequal ring universes, lift both
rings to the common carrier universe. The restriction equivalences along the ring
isomorphisms preserve complexes and quasi-isomorphisms and intertwine extension of
scalars by the tensor universal property. Transport the universal pair, its shift
structure and triangulatedness back along these equivalences. The counit comparison
on a transported resolution stays invertible. This argument works for unbounded
complexes, zero rings and zero complexes; no flatness of B over R is assumed. -/
theorem exists_baseDerivedExtension_resolution
    [(extendScalars.{_, _, max uR uB v} (algebraMap R B)).Additive] :
    ∃ (L : DerivedCategory (ModuleCat.{max uR uB v} R) ⥤
        DerivedCategory (ModuleCat.{max uR uB v} B))
      (ε : DerivedCategory.Qh ⋙ L ⟶
        (extendScalars.{_, _, max uR uB v} (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh),
      L.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (ModuleCat.{max uR uB v} R) (.up ℤ)) ∧
      (∃ c : L.CommShift ℤ, letI := c; L.IsTriangulated) ∧
      ∀ E : CochainComplex (ModuleCat.{max uR uB v} R) ℤ,
        ∃ (P : CochainComplex (ModuleCat.{max uR uB v} R) ℤ) (s : P ⟶ E),
          QuasiIso s ∧ IsIso (ε.app ((HomotopyCategory.quotient _ _).obj P)) := by sorry

end ModuleCat
