/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.Algebra.Homology.HomComplex
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # A bounded finite free Hom complex preserves quasi-isomorphisms

Source: Stacks Project, Cohomology, Tag 08DM. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Hom out of a bounded finite free complex preserves every quasi-isomorphism,
without a boundedness hypothesis on its target.
Source: Stacks Project, Cohomology, Tag 08DM, finite locally free Hom computation.
(blueprint: lem-sc-strictly-perfect-hom-quasi-iso).

Proof: The cone of s is acyclic. Filter the total Hom from E into this cone by
source degree. Both bounds on E make this a finite filtration. Each associated
graded complex is a shift of internal Hom from one finite free term into the cone.
Internal Hom from a finite free module is a finite direct sum, hence exact, so
these graded complexes are acyclic. Induction on the finite filtration proves
that the total Hom into the cone is acyclic. The Hom mapping-cone identification
then implies that Hom(E,s) is a quasi-isomorphism. No boundedness of either target
is used. Rank zero, E=0, and the empty ringed space are included. -/
theorem quasiIso_homComplex_map_of_bounded_finiteFree
    (X : RingedSpace.{u})
    (E : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ)
    (hbounded : ∃ N : ℤ, ∀ p : ℤ, N < p → IsZero (E.X p))
    (hbelow : ∃ M : ℤ, ∀ p : ℤ, p < M → IsZero (E.X p))
    (hfree : ∀ p : ℤ, ∃ r : ℕ, Nonempty (E.X p ≅
      SheafOfModules.free (R := moduleRings X) (ULift.{u} (Fin r))))
    {G I : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ}
    (s : G ⟶ I) [QuasiIso s] :
    QuasiIso (((homComplexFunctor (R := X.sheaf)).obj (op E)).map s) := by sorry

end AlgebraicGeometry
