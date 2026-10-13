/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.OpenModuleStalkFunctor
import Sheaf.AlgebraicGeometry.PerfectAffineMapRepresentative
import Sheaf.AlgebraicGeometry.AffinePerfectHomColimit
import Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence

/-! # Lifting a derived stalk morphism to a chain map between local perfect models

Source: Stacks Project, Tags 09RE (affine case), 0BC7 (2), 00CR, and 06Z0.
(blueprint: lem-sc-perfect-stalk-derived-hom-lift).
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- An arbitrary derived stalk morphism lifts to a chain map between strictly perfect
models restricted to a smaller affine neighbourhood. The stalk comparison isomorphisms identify
the derived image of that chain map with the original morphism. No invertibility of the
original morphism or the lifted map is asserted.

Source: Stacks Project, Tags 09RE (affine case), 0BC7 (2), 00CR, and 06Z0.
(blueprint: lem-sc-perfect-stalk-derived-hom-lift).

Proof: On the given affine open, the finite-free retract terms of P and Q are
quasi-coherent and
correspond to finite projective modules over the ring of sections. The complexes are
bounded. Exactness of stalks identifies the stalks of the derived comparisons with the
prime localizations of these module complexes, yielding comparison isomorphisms cG,cH.
Transport the given morphism by cG and cH. Present the prime localization as the filtered
colimit of principal localizations outside the prime (00CR). Surjectivity of the perfect
Hom comparison (09RE, or 0BC7 (2)) descends this morphism to one principal localization.
Bounded projective complexes are K-projective, so its derived morphism has a chain-map
representative. The affine correspondence transports this chain map back to the
restricted perfect sheaf complexes; exact restriction and stalk comparisons give the
stated equation. This uses only Hom surjectivity, not descent of an inverse or inverse
identities. Zero ranks and zero complexes cause no exception. -/
theorem exists_affine_perfect_stalk_hom_lift
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (x : X) [HasDerivedCategory.{v} (ModuleCat.{u} (X.presheaf.stalk x))]
    (G H : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (U : X.Opens) (hxU : x ∈ U) (hU : IsAffineOpen U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P) (hQ : IsStrictlyPerfect X U Q)
    (iG : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj G) ≅ DerivedCategory.Q.obj P)
    (iH : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj H) ≅ DerivedCategory.Q.obj Q)
    (t : DerivedCategory.Q.obj
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G) ⟶
      DerivedCategory.Q.obj
        (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj H)) :
    ∃ (V : X.Opens) (hxV : x ∈ V) (_hV : IsAffineOpen V) (hVU : V ≤ U),
      let T := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVU : V ⟶ U)).mapHomologicalComplex (.up ℤ)
      let S : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V) ⥤
          ModuleCat.{u} (X.presheaf.stalk x) := openModuleStalkFunctor X V ⟨x, hxV⟩
      letI : S.PreservesZeroMorphisms :=
        AlgebraicGeometry.openModuleStalkFunctor_preservesZeroMorphisms X V ⟨x, hxV⟩
      ∃ (cG : DerivedCategory.Q.obj
          ((S.mapHomologicalComplex (.up ℤ)).obj
            (T.obj P)) ≅ DerivedCategory.Q.obj
              (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
                (.up ℤ)).obj G))
        (cH : DerivedCategory.Q.obj
          ((S.mapHomologicalComplex (.up ℤ)).obj
            (T.obj Q)) ≅ DerivedCategory.Q.obj
              (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
                (.up ℤ)).obj H))
        (f : T.obj P ⟶ T.obj Q),
        DerivedCategory.Q.map
          ((S.mapHomologicalComplex (.up ℤ)).map f) =
            cG.hom ≫ t ≫ cH.inv := by sorry

end
end AlgebraicGeometry.Scheme
