/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.AffinePerfectModuleModel
public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes

/-! # A global test sheaf for affine tensor cohomology

Source: Stacks Project, Tags 08CG and 08DX; exact restriction to an open subscheme.
(blueprint: lem-pc-affine-sheafification-tensor-vanishing-test).
-/

@[expose] public section

universe u w wX

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Vanishing against the direct image of a spectrum module sheaf implies vanishing
against that sheaf after affine sheafification. This concerns one test sheaf and one
cohomological degree; it assumes neither Tor bounds nor boundedness of the complex.
Source: Stacks Project, Tags 08CG and 08DX, using exact open restriction and its
counit on direct images.
(blueprint: lem-pc-affine-sheafification-tensor-vanishing-test).

Proof: Put R = Gamma(S,U) and j = isoSpec.inv followed by U.ι. This is an open
immersion Spec R -> S. Take the actual test sheaf F = j_* G appearing in the statement.
Unpack the hypothesis as a K-flat representative C of K, its representing isomorphism,
and vanishing of H^i(C tensor F[0]). Exact restriction j^* preserves that vanishing,
commutes with total tensor, and preserves K-flatness. The open-immersion counit
j^* j_* G -> G is an isomorphism. Thus j^* C tensor G[0] has zero degree-i cohomology.
Transport the representing isomorphism hP through overEquiv and restriction by
isoSpec.inv. The restriction-composition isomorphisms, isoSpec's inverse identities,
and the counit of overEquiv identify Q(j^* C) with Q(tilde P). These exact transport
functors induce derived equivalences compatible with Q even when the localization
universes differ. Consequently j^* C, its transported representing isomorphism,
and the computed zero cohomology give the K-flat witness required by the conclusion.
For an empty affine open the same restriction and counit isomorphisms exist; its
module sheaves are zero. Zero rings, zero complexes and unbounded complexes require
no additional hypothesis. -/
theorem affine_sheafification_tensor_vanishing_test (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ V : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over V))]
    (U : S.Opens) (hU : IsAffineOpen U)
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings (Spec (S.presheaf.obj (.op U))).toRingedSpace))]
    (K : schemeDerivedCategory S)
    (P : CochainComplex (ModuleCat.{u} (S.presheaf.obj (.op U))) ℤ)
    (hP : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj K ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification S U hU).mapHomologicalComplex (.up ℤ)).obj P)))
    (G : SheafOfModules.{u}
      (moduleRings (Spec (S.presheaf.obj (.op U))).toRingedSpace)) (i : ℤ)
    (h : schemeDerivedTensorCohomologyVanishes S K
      ((Modules.pushforward (hU.isoSpec.inv ≫ U.ι)).obj G) i) :
    schemeDerivedTensorCohomologyVanishes (Spec (S.presheaf.obj (.op U)))
      (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (S.presheaf.obj (.op U)))
          (SheafOfModules.{u}
            (moduleRings (Spec (S.presheaf.obj (.op U))).toRingedSpace)) _ _ _ _
          (tilde.functor (S.presheaf.obj (.op U)))
          ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj P)) G i := by sorry

end AlgebraicGeometry.Scheme
