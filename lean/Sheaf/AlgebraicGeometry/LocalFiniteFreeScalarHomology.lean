/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Local finite free computation of scalar derived Hom cohomology

Source: Stacks Project, Tag 08DL; Tag 08DM for bounded truncations.
(blueprint: lem-sc-local-finite-free-scalar-homology). -/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- A finite free resolution on an open computes restricted scalar Ext, independently
of the supplied universe of the ambient derived category.

Source: Stacks Project, Tag 08DL, restriction; Tag 08DM, strictly perfect Hom
applied to bounded truncations of the bounded-above finite free model.
(blueprint: lem-sc-local-finite-free-scalar-homology).

Proof: Choose a bounded-below injective resolution I of the degree-zero structure
sheaf on Y. It is K-injective; its restriction remains bounded below and K-injective.
The representative comparison for derived internal Hom and the homology factorization
identify ambient cohomology with homology of Hom(single K,I). Restriction is exact;
restriction of I is K-injective and restriction commutes with the Hom complex.
The over-site equivalence transports these complexes to U.toScheme. The augmentation
E -> single(K|U) becomes invertible in the derived category. Compute in the standard
universe on U.toScheme, using this same restricted I: the representative comparison
and the finite free Hom model identify Hom(single(K|U),I|U) with Hom(E,O_U).
Take homology and transport back through the over-site equivalence. Since the
initial computation used a complex of module sheaves independent of the derived
universe, its homology comparison applies to the arbitrary supplied ambient universe.
The finite free model applies because E is bounded above and O_U[0] is bounded
below. Equivalently, for each fixed Hom cohomology degree only a finite truncation
of E contributes when paired with the bounded-below I; Tag 08DM applies to this
strictly perfect truncation. Thus no lower bound on E is required.
The zero resolution and empty opens are included. No affine or Koszul hypothesis
is involved in this assertion. -/
theorem local_finite_free_scalar_homology
    {Y : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (U : Y.Opens) (K : Y.Modules)
    (E : CochainComplex U.toScheme.Modules ℤ)
    (hbounded : ∃ N : ℤ, ∀ p : ℤ, N < p → IsZero (E.X p))
    (hfree : ∀ p : ℤ, ∃ r : ℕ, Nonempty (E.X p ≅
      SheafOfModules.free (R := moduleRings U.toScheme.toRingedSpace)
        (ULift.{u} (Fin r))))
    (ε : E ⟶ (CochainComplex.singleFunctor U.toScheme.Modules 0).obj
      ((Scheme.Modules.restrictFunctor U.ι).obj K)) [QuasiIso ε] (q : ℤ) :
    let F : Y.Modules := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) q).obj
        ((derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj K),
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
                (SheafOfModules.unit Y.ringCatSheaf)))
    Nonempty (F.over U ≅ (Scheme.Modules.overEquiv U).inverse.obj
      ((homComplex (R := U.toScheme.toRingedSpace.sheaf) E
        ((CochainComplex.singleFunctor U.toScheme.Modules 0).obj
          (SheafOfModules.unit U.toScheme.ringCatSheaf))).homology q)) := by sorry

end AlgebraicGeometry
