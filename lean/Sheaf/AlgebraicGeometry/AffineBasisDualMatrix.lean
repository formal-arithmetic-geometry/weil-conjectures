/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.LinearAlgebra.Dual.Basis
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Transposed entries for sheafified dual basis maps

Source: Stacks Project, schemes.tex, Tag 01HV, functoriality of localization;
Mathlib LinearAlgebra/Dual/Basis.lean, Basis.dualBasis_repr.
(blueprint: lem-sc-affine-basis-dual-matrix).
-/

@[expose] public section

universe u
open CategoryTheory Module
namespace AlgebraicGeometry

/-- The based affine module in free-sheaf coordinates.
Source: Stacks Project, Tag 01HV.
(blueprint: lem-sc-affine-basis-dual-matrix). -/
@[irreducible]
noncomputable def affineBasisCoordinatesIso {Y : Scheme.{u}} (U : Y.affineOpens)
    (M : ModuleCat.{u} Γ(Y, U.1)) {I : Type u} (b : Basis I Γ(Y, U.1) M) :
    (((tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj M) :
      SheafOfModules.{u} U.1.toScheme.ringCatSheaf) ≅
      SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) I :=
  (Scheme.Modules.restrictFunctor U.2.isoSpec.hom).mapIso
    ((tilde.functor Γ(Y, U.1)).mapIso b.repr.toModuleIso ≪≫
      tildeFinsupp (R := Γ(Y, U.1)) I) ≪≫
    Scheme.Modules.restrictFreeIso U.2.isoSpec.hom I

/-- The algebraic module dual in dual-basis free-sheaf coordinates.
Source: Stacks Project, Tag 01HV; Basis.dualBasis_repr.
(blueprint: lem-sc-affine-basis-dual-matrix). -/
@[irreducible]
noncomputable def affineDualBasisCoordinatesIso {Y : Scheme.{u}} (U : Y.affineOpens)
    (M : ModuleCat.{u} Γ(Y, U.1)) {I : Type u} [Finite I]
    (b : Basis I Γ(Y, U.1) M) :
    ((tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj
      (ModuleCat.of Γ(Y, U.1) (M ⟶ ModuleCat.of Γ(Y, U.1) Γ(Y, U.1))) :
        SheafOfModules.{u} U.1.toScheme.ringCatSheaf) ≅
      SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) I := by
  classical
  exact (Scheme.Modules.restrictFunctor U.2.isoSpec.hom).mapIso
    ((tilde.functor Γ(Y, U.1)).mapIso
      ((ModuleCat.homLinearEquiv.trans b.dualBasis.repr).toModuleIso) ≪≫
        tildeFinsupp (R := Γ(Y, U.1)) I) ≪≫
    Scheme.Modules.restrictFreeIso U.2.isoSpec.hom I

/-- Sheafification and restriction preserve the transposed entries of a dual map.
Source: Stacks Project, schemes.tex, Tag 01HV(4)-(5) and functoriality;
Basis.dualBasis_repr in Mathlib.LinearAlgebra.Dual.Basis.
(blueprint: lem-sc-affine-basis-dual-matrix).

Proof: Write a_ij = bM.repr (f (bN j)) i. The coefficient at j of the functional
bM.dualBasis i precomposed with f is a_ij, by dualBasis_repr. The basis repr
maps and their inverses therefore identify the two algebraic matrix components
with the same scalar endomorphism of A. The coproduct comparison tildeFinsupp
carries each sheafified single basis vector to the corresponding free generator:
this follows from its defining coconePointUniqueUpToIso and the injection
identities for that isomorphism. Its coordinate projections likewise agree by
finite coproduct extensionality. The restrictFreeIso has the same property,
by the generator identities for mapFreeIso and the natural isomorphism between
restriction and pullback. Apply the two functors to the equal scalar components;
functors preserve their compositions, so the displayed components are equal.
This proves the assertion on all opens without any choice of sections. The
argument uses no division or nonzero coefficient. For an empty basis there
are no pairs (i,j), and for a zero ring all scalar components are zero. -/
theorem affineBasisDualMatrix_component {Y : Scheme.{u}} (U : Y.affineOpens)
    (M N : ModuleCat.{u} Γ(Y, U.1)) {I J : Type u} [Finite I] [Finite J]
    [DecidableEq I] [DecidableEq J]
    (bM : Basis I Γ(Y, U.1) M) (bN : Basis J Γ(Y, U.1) N) (f : N ⟶ M)
    (i : I) (j : J) :
    let S := Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    let T := tilde.functor Γ(Y, U.1) ⋙ S
    let eM := affineBasisCoordinatesIso U M bM
    let eN := affineBasisCoordinatesIso U N bN
    let dM := affineDualBasisCoordinatesIso U M bM
    let dN := affineDualBasisCoordinatesIso U N bN
    SheafOfModules.ιFree i ≫ dM.inv ≫
        T.map (ModuleCat.ofHom (Linear.leftComp Γ(Y, U.1)
          (ModuleCat.of Γ(Y, U.1) Γ(Y, U.1)) f)) ≫ dN.hom ≫ Scheme.Modules.freeπ j =
      SheafOfModules.ιFree j ≫ eN.inv ≫ T.map f ≫ eM.hom ≫ Scheme.Modules.freeπ i :=
  by sorry

end AlgebraicGeometry
