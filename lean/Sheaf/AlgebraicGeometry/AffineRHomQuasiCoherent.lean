/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
import Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel
import Sheaf.Algebra.Homology.DerivedHomProjectiveResolution
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.RingTheory.FiniteFreeResolution

/-! # Affine derived Hom of finite modules has quasi-coherent cohomology

Source: Stacks Project, Perfect Complexes, Tag 0A6H (3), using Tags 08DL, 00LP,
0A64 and 06XR (blueprint: lem-sc-affine-rhom-qcoherent).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The affine derived internal Hom of finite modules has no negative cohomology and has
quasi-coherent cohomology in nonnegative degrees, canonically identified with sheafified Ext.
Source: literature/stacks-project/perfect.tex, Tags 08DL, 00LP, 0A64, and 06XR
(blueprint: lem-sc-affine-rhom-qcoherent).
Proof:
1. Use lem-weil-pbc-finite-free-resolution-noetherian (00LP) to resolve M by finite free
   modules F_i. Sheafify in degrees -i. On principal opens and stalks, the tilde-sections
   and tilde-stalk-localization lemmas identify this with the localized resolution.
   Localization is exact; module-stalk-exact (5) detects the quasi-isomorphism to tilde M[0].
2. Apply lem-sc-derived-hom-finite-free-model. Finite freeness identifies each sheaf Hom
   term with tilde of Hom_A(F_i,N); these identifications commute with the differentials.
3. By tilde-stalk-localization, localization-module-exact and module-stalk-exact (5),
   tilde commutes with the cohomology of this Hom complex. Negative terms are zero.
4. Apply lem-sc-derived-hom-projective-resolution and lem-sc-rhom-cohomology-ext-ring
   (0A64) to identify its degree-q cohomology with Ext^q_A(M,N). The comparison is
   canonical because the comparisons commute with maps of resolutions. Associated
   sheaves are quasi-coherent by lem-weil-pbc-spec-module-tilde-sections.
-/
theorem affineRHomQuasiCoherent
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (M N : ModuleCat.{u} A) [Module.Finite A M] [Module.Finite A N]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u}
        (moduleRings (Spec (CommRingCat.of A)).toRingedSpace))] :
    (∀ (q : ℤ), q < 0 → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u}
        (moduleRings (Spec (CommRingCat.of A)).toRingedSpace)) q).obj
      ((derivedInternalHom
          (Opens.grothendieckTopology (Spec (CommRingCat.of A)).toRingedSpace)
          (Spec (CommRingCat.of A)).toRingedSpace.sheaf).obj
        (op ((DerivedCategory.singleFunctor
          (SheafOfModules.{u}
            (moduleRings (Spec (CommRingCat.of A)).toRingedSpace)) 0).obj (tilde M)),
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u}
              (moduleRings (Spec (CommRingCat.of A)).toRingedSpace)) 0).obj (tilde N))))) ∧
    (∀ (q : ℤ), 0 ≤ q →
      ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u}
        (moduleRings (Spec (CommRingCat.of A)).toRingedSpace)) q).obj
      ((derivedInternalHom
          (Opens.grothendieckTopology (Spec (CommRingCat.of A)).toRingedSpace)
          (Spec (CommRingCat.of A)).toRingedSpace.sheaf).obj
        (op ((DerivedCategory.singleFunctor
          (SheafOfModules.{u}
            (moduleRings (Spec (CommRingCat.of A)).toRingedSpace)) 0).obj (tilde M)),
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u}
              (moduleRings (Spec (CommRingCat.of A)).toRingedSpace)) 0).obj
                (tilde N)))).IsQuasicoherent ∧
      Nonempty (((DerivedCategory.homologyFunctor
      (SheafOfModules.{u}
        (moduleRings (Spec (CommRingCat.of A)).toRingedSpace)) q).obj
      ((derivedInternalHom
          (Opens.grothendieckTopology (Spec (CommRingCat.of A)).toRingedSpace)
          (Spec (CommRingCat.of A)).toRingedSpace.sheaf).obj
        (op ((DerivedCategory.singleFunctor
          (SheafOfModules.{u}
            (moduleRings (Spec (CommRingCat.of A)).toRingedSpace)) 0).obj (tilde M)),
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u}
              (moduleRings (Spec (CommRingCat.of A)).toRingedSpace)) 0).obj (tilde N)))) ≅
        tilde (ModuleCat.of A (Abelian.Ext M N q.toNat)))) := by
  sorry

end AlgebraicGeometry
