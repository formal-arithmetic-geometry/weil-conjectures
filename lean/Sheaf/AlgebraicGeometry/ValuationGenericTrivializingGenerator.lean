/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.ValuationProperCoherentSections
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme

/-! # A generic trivializing generator over a valuation ring

Source: Stacks Project, More on Morphisms, Tag 0EX8, general-case proof, first paragraph.
(blueprint: lem-sc-valuation-generic-trivializing-generator)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- Global sections have an A-basis whose zero scheme has empty generic fibre.

Source: Stacks Project, More on Morphisms, Tag 0EX8, general-case proof through the
choice of a generator of H⁰(X,L).
(blueprint: lem-sc-valuation-generic-trivializing-generator)

Proof: Proper coherent cohomology makes H⁰(X,L) finitely presented over A. Flatness
of X/A and local freeness of L make multiplication by each nonzero element of A
injective on L and hence on its global sections. A finitely presented torsion-free
module over a valuation ring is finite free. Flat base change to K identifies its
scalar extension with H⁰(X_K,L_K). Triviality of L_K and the canonical global-function
isomorphism identify this last module with K, so the free module has rank one.
Choose an A-basis s. Its base change is a K-basis of H⁰(X_K,L_K); under a trivialization
it is a nonzero scalar in K. Multiplication by this scalar trivializes L_K, so its
zero ideal is the unit ideal. Zero schemes commute with pullback, giving the last
clause. No integrality assumption on the closed fibre is used here. -/
theorem exists_generic_trivializing_generator
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [L.IsInvertible]
    (hglobal : IsIso (pullback.snd f (Spec.map
      (CommRingCat.ofHom (algebraMap A K)))).appTop)
    (htriv : Nonempty ((tensorPullback
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A K))))).obj L ≅
      SheafOfModules.unit _)) :
    ∃ s : Γ(L, ⊤),
      Function.Bijective (fun a : A ↦
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom a • s) ∧
      (Hom.zeroLocus (homOfGlobalSection L s)).comap
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A K)))) = ⊤ := by
  sorry

end AlgebraicGeometry.Scheme.Modules
