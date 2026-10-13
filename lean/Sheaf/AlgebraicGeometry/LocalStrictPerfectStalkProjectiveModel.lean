/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Module.Projective
import Sheaf.Algebra.Homology.ModuleStalkExact

/-! # Bounded finite-projective models of locally strictly perfect stalks

Source: Stacks Project, Tags 08C4, 08CM, 01AG and 00A0.
(blueprint: lem-sc-local-strict-perfect-stalk-projective-model).
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A local strictly perfect representative supplies a bounded finite-projective
representative of the termwise stalk of any complex representing the same derived object.

Source: Stacks Project, Cohomology of Sheaves, Tags 08C4 and 08CM;
Modules, Tag 01AG; Sheaves, Tag 00A0 (restriction to an open neighbourhood).
(blueprint: lem-sc-local-strict-perfect-stalk-projective-model).

Proof:
1. Choose V, P and its derived comparison from hlocal. The category of opens over V
   is equivalent to the open-subspace site of V. At x, neighbourhoods contained in V
   are cofinal among all neighbourhoods. Germ restriction therefore identifies both
   the stalk ring and the stalk modules of a restricted sheaf with their stalks on X.
   This identification commutes with all sheaf morphisms, hence with differentials.
2. Apply the stalk functor termwise to P to obtain L over O_X,x. Stalks preserve zero
   objects, so the lower and upper bounds of P give the same bounds for L. Stalks
   commute with finite coproducts, and the germ of the unit module is the stalk ring.
   Consequently the stalk of the finite free sheaf on Fin m is the free module of
   rank m. Apply stalks to each retraction in IsStrictlyPerfect. Its composite is
   the identity by functoriality. Thus every L.X j is a retract of a finite free
   module: it is finite and projective, without using local-ring freeness yet.
3. Stalks are exact by Tag 01AG, so preserve quasi-isomorphisms. Their termwise
   functor descends to the derived localization. Apply it to the local comparison,
   and compose with the cofinal germ comparison and eG. This gives Q(L) isomorphic
   to Q(G_x). This last argument uses the universal property of localization; the
   morphism universes v and w can differ, since it only transports an isomorphism
   between the represented objects, not an equivalence of the entire categories.
No residue fibre, finiteness of its cohomology, or minimal model is asserted here.
For a zero representative all terms and their retracts are zero. -/
theorem exists_localStrictPerfect_stalk_projective_model
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (x : X)
    [HasDerivedCategory.{v} (ModuleCat.{u} (X.presheaf.stalk x))]
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eG : DerivedCategory.Q.obj G ≅ E)
    (hlocal : ∃ V : X.Opens, x ∈ V ∧
      ∃ P : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)) ℤ,
        IsStrictlyPerfect X V P ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj E ≅
          DerivedCategory.Q.obj P))
    : ∃ (L : CochainComplex (ModuleCat.{u} (X.presheaf.stalk x)) ℤ)
      (a b : ℤ),
      (∀ j : ℤ, j < a ∨ b < j → IsZero (L.X j)) ∧
      (∀ j : ℤ, Module.Finite (X.presheaf.stalk x) (L.X j) ∧
        Module.Projective (X.presheaf.stalk x) (L.X j)) ∧
      Nonempty (DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G)) := by sorry

end AlgebraicGeometry.Scheme
