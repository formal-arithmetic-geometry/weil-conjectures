/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian

import Sheaf.AlgebraicGeometry.CoherentStalkMapExtends
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! Generic coherent ideal lattices. Source: Stacks Project, Tag 01YE. -/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- A finite generic basis extends to a finite free map on an open neighbourhood.

Source: Stacks Project, Tag 01YE, integral case, choice and extension of the generic basis.
Proof: write ξ for the generic point and E for the free sheaf on ULift (Fin r).
The ring O_{Z,ξ} is the function field, hence a field. Take a finite generating
neighbourhood of G at ξ. The germs of its finitely many generators span G_ξ:
represent a germ by a section, lift that section locally through the generating
free-sheaf epimorphism, and take germs of the resulting finite linear combination.
Thus G_ξ has a finite basis; reindex it by Fin r. The stalk of E is the free module
on the same finite set: its coordinate germs give the identification, since finitely
many representatives and finitely many equalities can be restricted to a common
neighbourhood. The basis therefore defines an isomorphism E_ξ → G_ξ.
The free sheaf E is quasi-coherent and of finite type (its standard finite generating
family), hence coherent by the locally Noetherian criterion. Apply
exists_open_hom_of_coherent_stalk_map to E, G and the basis isomorphism. This supplies
U, hx and φ. Its stated equality says the basis map is the composite of φ_ξ with
the source and target restriction-stalk isomorphisms. Cancelling those isomorphisms
makes φ_ξ invertible, as required. No shrinking to an isomorphism on all of U is needed.
For G_ξ = 0 the basis is empty, r = 0, and the same argument applies.
(blueprint: lem-weil-pbc-coherent-integral-generic-free-neighbourhood)
-/
theorem exists_generic_free_neighbourhood (Z : Scheme.{w}) [IsNoetherian Z]
    [IsIntegral Z] (G : Z.Modules)
    (hG : RingedSpace.IsCoherent Z.toRingedSpace G) :
    ∃ (r : ℕ) (U : Z.Opens) (hx : genericPoint Z ∈ U)
      (φ : (restrictFunctor U.ι).obj
          (SheafOfModules.free (R := Z.ringCatSheaf) (ULift.{w} (Fin r))) ⟶
        (restrictFunctor U.ι).obj G),
      IsIso ((RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace
        (⟨genericPoint Z, hx⟩ : U.toScheme)).map φ) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
