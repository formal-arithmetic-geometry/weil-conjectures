/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.PrincipalOpenCechTotal
public import Sheaf.Topology.RingedSpaceModuleCohomology

/-! # Comparing basic-open sections with sections of the restricted scheme

Source: Stacks Project, Tags 08D2 and 08BS; restriction of scalars for section modules.
(blueprint: lem-sc-principal-open-sections-restriction-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Basic-open sections detect the same quasi-isomorphisms as global sections after
restriction to the open subscheme. No quasi-coherence or resolution is assumed.
Source: Stacks Project, Tags 08D2 and 08BS, sections on an open subscheme.
(blueprint: lem-sc-principal-open-sections-restriction-comparison).

Proof: Put U = D(g). Restriction to the localized site followed by the canonical
module equivalence overEquiv U is ordinary open-subscheme restriction. Its global
sections on U are the original module's sections on U, with scalars in O(U).
The canonical ring map A to O(U) restricts this action to the action used by
modulesSpecToSheaf and hence by affineOpenSections. The identifications are
natural in sheaf-module morphisms, and therefore identify both section complexes
and the map induced by i after restriction of scalars. Restriction of scalars is
exact: it leaves the underlying additive group, kernels, images and quotients
unchanged. Thus it preserves and reflects homology isomorphisms in every degree.
For an empty basic open all these section modules are zero. -/
theorem principalOpenSections_restriction_quasiIso_iff
    (A : Type u) [CommRing A] (g : A)
    (F J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (i : F ⟶ J) :
    let U : (Spec (.of A)).Opens := PrimeSpectrum.basicOpen g
    let R := SheafOfModules.overFunctor.{u} (moduleRings (Spec (.of A)).toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U)
    QuasiIso (((affineOpenSections A U).mapHomologicalComplex (ComplexShape.up ℤ)).map i) ↔
      QuasiIso (((RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace).mapHomologicalComplex
         (ComplexShape.up ℤ)).map
          ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map i)) := by
  sorry

end AlgebraicGeometry
