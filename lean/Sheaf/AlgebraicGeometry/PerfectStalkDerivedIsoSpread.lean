/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
import Sheaf.AlgebraicGeometry.AffinePerfectHomColimit
import Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence

/-! # Extending a derived stalk isomorphism between existing local perfect models

Source: Stacks Project, Tag 09RE, affine full faithfulness, and Tag 0BC7 (2).
(blueprint: lem-sc-perfect-stalk-derived-iso-spread).
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Existing local perfect models with isomorphic derived stalks are isomorphic nearby.

Source: Stacks Project, Tag 09RE, affine proof, and Tag 0BC7 (2), with Tags 00CR and 06Z0.
(blueprint: lem-sc-perfect-stalk-derived-iso-spread).

Proof:
1. Intersect U with the neighbourhood V supplied for Q(G), and take an affine
   neighbourhood of x inside that intersection. Restrict P and H to it. These are
   strictly perfect complexes. Their terms are retracts of finite free sheaves, hence
   quasi-coherent; the affine correspondence gives bounded finite projective complexes
   over the section ring A. Exactness of stalks and the local comparison for G identify
   their prime-localized derived objects with the derived stalks of G and H.
2. Present the prime localization as the filtered colimit of the A_f outside the prime.
   Full faithfulness for perfect complexes (09RE, or 0BC7 (2)) descends the given
   isomorphism and its inverse to one common principal neighbourhood. Injectivity
   of the Hom comparison descends both inverse identities after a further shrinking.
   This gives an actual derived isomorphism on an affine open W containing x inside U.
3. Use the affine derived sheaf equivalence and the restriction comparisons to identify
   the two descended objects with Q(G restricted to W) and Q(H restricted to W).
   Compose with these identifications to obtain the conclusion. No terms, ranks or
   differentials of H are changed. The argument also works for zero complexes and any
   bounds, and only takes principal opens inside one affine chart, so no separatedness
   hypothesis is required. The derived-category universes on sheaves and stalk modules
   may differ: comparisons are transported through their localization equivalences.
-/
theorem exists_affine_restriction_iso_of_perfect_stalk_iso
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (x : X) [HasDerivedCategory.{v} (ModuleCat.{u} (X.presheaf.stalk x))]
    (G H : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hlocal : ∃ V : X.Opens, x ∈ V ∧
      ∃ P : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)) ℤ,
        IsStrictlyPerfect X V P ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj
            (DerivedCategory.Q.obj G) ≅ DerivedCategory.Q.obj P))
    (U : X.Opens) (hxU : x ∈ U)
    (hH : IsStrictlyPerfect X U
      (((SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U).mapHomologicalComplex (.up ℤ)).obj H))
    (e : DerivedCategory.Q.obj
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G) ≅
      DerivedCategory.Q.obj
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj H)) :
    ∃ W : X.Opens, x ∈ W ∧ IsAffineOpen W ∧ W ≤ U ∧
      Nonempty (DerivedCategory.Q.obj
          (((SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) W).mapHomologicalComplex (.up ℤ)).obj G) ≅
        DerivedCategory.Q.obj
          (((SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) W).mapHomologicalComplex (.up ℤ)).obj H)) := by sorry

end
end AlgebraicGeometry.Scheme
