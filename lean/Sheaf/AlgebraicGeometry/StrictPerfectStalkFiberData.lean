/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.Algebra.Homology.BoundedFlatKFlat
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackModuleModel
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition

/-! # Strictly perfect stalks and derived residue cohomology

Source: Stacks Project, Tags 0BCD, 08EB and 06YB.
(blueprint: lem-sc-strict-perfect-stalk-fiber-data).
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- The stalk of a locally strictly perfect object is pseudo-coherent, and any finite-free
representative of it computes the derived residue fibre.

Source: Stacks Project, Tag 0BCD, local-ring paragraph; Tags 08EB and 06YB.
(blueprint: lem-sc-strict-perfect-stalk-fiber-data).

Proof:
1. Choose the strictly perfect representative P on V from hlocal. Restriction to V
   followed by its stalk at x agrees with taking the stalk on X, since neighbourhoods
   contained in V are cofinal. Stalks are exact, hence preserve quasi-isomorphisms and
   derived isomorphisms. Apply this to eG and the comparison of P with E restricted to V.
2. The stalk of a rank-m free sheaf is the free stalk module of rank m. Apply stalks to
   the retractions in IsStrictlyPerfect: the terms of the resulting bounded complex
   are finite projective over the local ring O_X,x, hence finite free. Its bounds are
   preserved because stalks preserve zero objects. This gives hK.
3. The finite-free representative chosen by hK is bounded above, hence K-flat. Termwise
   extension along O_X,x -> kappa(x) computes its derived residue tensor product.
   The residue-field point factors through V and through Spec O_X,x. Associativity of
   derived pullback and the affine module/sheaf correspondence identify its degree-i
   homology with derivedFiberCohomology X E i x. This identification is linear over
   kappa(x) = IsLocalRing.ResidueField O_X,x. Transport hfin across the linear
   isomorphism, and use invariance of finrank to obtain the displayed equality.
The computation concerns every bounded-above finite-free representative of the same
derived object: K-flatness makes residue cohomology invariant under its derived comparison.
It therefore applies to Classical.choose hK. No rank-minimal model is constructed here.
-/
theorem strictPerfect_stalk_fiberData
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ x : X, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
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
    (hfin : ∀ i : ℤ, Module.Finite (X.residueField x) (derivedFiberCohomology X E i x)) :
    ∃ hK : DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj
      (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj G)),
      (∀ i : ℤ, Module.Finite (IsLocalRing.ResidueField (X.presheaf.stalk x))
        ((((ModuleCat.extendScalars
          (IsLocalRing.residue (X.presheaf.stalk x))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (Classical.choose hK)).homology i)) ∧
      (∀ i : ℤ, derivedFiberBetti X E i x =
        Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
          ((((ModuleCat.extendScalars
            (IsLocalRing.residue (X.presheaf.stalk x))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (Classical.choose hK)).homology i)) := by sorry

end
end AlgebraicGeometry.Scheme
