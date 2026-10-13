/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.Algebra.Homology.HomComplexToSingle
public import Sheaf.Algebra.Homology.SignedModuleDualComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Associated sheafification of finite free signed duals

Source: Stacks Project, duality.tex, Tag 0BQZ; schemes.tex, Tag 01HV.
(blueprint: lem-sc-affine-finite-free-dual-complex-comparison).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Sheafification and transport to an affine open commute with signed duals
of degreewise finite free chain complexes.

Source: Stacks Project, duality.tex, Tag 0BQZ, local finite free Hom computation;
schemes.tex, Tag 01HV, associated sheaves on affine schemes.
(blueprint: lem-sc-affine-finite-free-dual-complex-comparison).

Proof: choose finite bases of K_q. On each standard open D(g), the associated
sheaf has the localized basis. An internal sheaf map to the structure sheaf is
uniquely determined by its values on these basis sections. Consequently the
internal dual identifies with the associated sheaf of Hom_A(K_q,A). A change
of standard open localizes each value, so these coordinate identifications
commute with restrictions and glue to inverse sheaf maps. This description is
independent of the basis: it sends a functional to its localized evaluations.
For every boundary K_(q+1) → K_q, both induced maps are precomposition with
its localized matrix, so the degree identifications commute with boundaries.
Multiplication by -(-1)^q in the sheaf dual equals the sheafification of
multiplication by (-1)^(q+1) in the module dual. The extension isomorphisms
identify source cochain degree -q with K_q. Negative dual degrees have zero
objects on both sides, since the extended chain complex vanishes in positive
cochain degrees. Thus the degreewise maps give a complex isomorphism.
Transport along U.isoSpec is an equivalence and preserves all these maps.
There is no boundedness or regularity assumption: each degree is handled
separately, with no infinite sum. Rank zero terms, the zero ring and empty
charts use the unique maps between zero objects. -/
theorem affine_finite_free_dual_complex_comparison
    {Y : Scheme.{u}} (U : Y.affineOpens)
    (K : ChainComplex (ModuleCat.{u} Γ(Y, U.1)) ℕ)
    (hfree : ∀ q : ℕ, Module.Free Γ(Y, U.1) (K.X q))
    (hfinite : ∀ q : ℕ, Module.Finite Γ(Y, U.1) (K.X q)) :
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    let E := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (K.extend ComplexShape.embeddingDownNat)
    Nonempty (signedSheafDualComplex (R := U.1.toScheme.toRingedSpace.sheaf) E
      (SheafOfModules.unit U.1.toScheme.ringCatSheaf) ≅
      (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (ModuleCat.signedDualCochainComplex K)) := by sorry

end AlgebraicGeometry
