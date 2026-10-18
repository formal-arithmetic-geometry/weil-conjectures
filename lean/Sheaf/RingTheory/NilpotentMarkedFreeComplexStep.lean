/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.RingTheory.PseudoCoherentNilpotentInvariance
import Sheaf.RingTheory.NilpotentMarkedFreeComplexLift

/-! # Compatible finite-free complex towers

Source: Stacks Project, More on Algebra, Tag 0CQF.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- A marked finite-free reduction lifts across one surjective nilpotent ring map.
Source: Stacks Project, Tags 0H76, 0BCB and 0BCA
(blueprint: lem-weil-pbc-nilpotent-marked-free-complex-step).

Proof: The marking of F shows that the reduced derived object is pseudo-coherent.
Nilpotent invariance gives pseudo-coherence of K. Identify S with R modulo ker φ by
surjectivity and transport scalar extension and its adjunction along this ring
isomorphism. Left adjoints to the same restriction functor are uniquely isomorphic,
with the isomorphism fixed by the unit. Choose the derived scalar-extension functor
from derived change of rings on the punctual site and use this unit-compatible
isomorphism. Apply marked free-complex lifting to F, the prescribed marking and b.
Transport the resulting model and reduction isomorphism back to S. Its adjoint is u.
It is surjective in every degree: the extension unit is surjective for a surjective
ring map, since every tensor is a sum of scalar multiples of unit tensors and each
scalar lifts. The normalized derived coefficient adjunction on the bounded-above
finite-free model identifies Q(u) with the prescribed derived transition. This also
covers F=0, the zero ring, and rank-zero terms. -/
theorem exists_nilpotent_marked_finiteFree_step
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hsurj : Function.Surjective φ)
    (hnil : IsNilpotent (RingHom.ker φ))
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} S)]
    (L : DerivedCategory (ModuleCat.{max u v} R) ⥤
      DerivedCategory (ModuleCat.{max u v} S))
    (adj : L ⊣ (ModuleCat.restrictScalars φ).mapDerivedCategory)
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (E : DerivedCategory (ModuleCat.{max u v} S))
    (t : K ⟶ (ModuleCat.restrictScalars φ).mapDerivedCategory.obj E)
    (hred : IsIso ((adj.homEquiv K E).symm t))
    (F : CochainComplex (ModuleCat.{max u v} S) ℤ)
    (b : ℤ) (hbound : F.IsStrictlyLE b)
    (hterms : ∀ i, Module.Free S (F.X i) ∧ Module.Finite S (F.X i))
    (β : Q.obj F ≅ E) :
    ∃ (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
      (β' : Q.obj P ≅ K)
      (u : P ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj F)
      (θ : ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P ≅ F),
      P.IsStrictlyLE b ∧
      (∀ i, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)) ∧
      (∀ i, Function.Surjective (u.f i)) ∧
      (∀ i, (ModuleCat.extendRestrictScalarsAdj φ).homEquiv
        (P.X i) (F.X i) (θ.hom.f i) = u.f i) ∧
      Q.map u = β'.hom ≫ t ≫
        (ModuleCat.restrictScalars φ).mapDerivedCategory.map β.inv ≫
        (ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.hom.app F := by
  sorry

end DerivedCategory
