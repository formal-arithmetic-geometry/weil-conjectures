/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.LinearAlgebra.Dual.Basis
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Finite basis dual comparison on an affine open

Source: Stacks Project, schemes.tex, Tag 01HV; duality.tex, Tag 0BQZ.
(blueprint: lem-sc-affine-finite-free-dual-naturality).
-/

@[expose] public section

universe u
open CategoryTheory Opposite Module
namespace AlgebraicGeometry

/-- The associated sheaf of a based module, transported to the affine open,
is the free sheaf on the same basis. All maps are constructed from the basis.
Source: Stacks Project, schemes.tex, Tag 01HV.
(blueprint: lem-sc-affine-finite-free-dual-naturality). -/
noncomputable def affineBasisSheafIso {Y : Scheme.{u}} (U : Y.affineOpens)
    (M : ModuleCat.{u} Γ(Y, U.1)) {I : Type u} (b : Basis I Γ(Y, U.1) M) :
    ((tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj M) ≅
      SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) I :=
  (Scheme.Modules.restrictFunctor U.2.isoSpec.hom).mapIso
    ((tilde.functor Γ(Y, U.1)).mapIso b.repr.toModuleIso ≪≫ tildeFinsupp I) ≪≫
    Scheme.Modules.restrictFreeIso U.2.isoSpec.hom I

/-- Explicit comparison of the internal dual and the sheafified module dual.
Use the basis and its dual basis, with the canonical dual of a finite free sheaf.
No data are selected from an unproved existence theorem.
Source: Stacks Project, duality.tex, Tag 0BQZ; schemes.tex, Tag 01HV.
(blueprint: lem-sc-affine-finite-free-dual-naturality). -/
noncomputable def affineBasisDualIso {Y : Scheme.{u}} (U : Y.affineOpens)
    (M : ModuleCat.{u} Γ(Y, U.1)) {I : Type u} [Fintype I]
    (b : Basis I Γ(Y, U.1) M) :
    SheafOfModules.homObj (R := U.1.toScheme.toRingedSpace.sheaf)
      ((tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj M)
      (SheafOfModules.unit U.1.toScheme.ringCatSheaf) ≅
    (tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj
      (ModuleCat.of Γ(Y, U.1) (M ⟶ ModuleCat.of Γ(Y, U.1) Γ(Y, U.1))) := by
  classical
  exact
    ((SheafOfModules.homFunctor U.1.toScheme.toRingedSpace.sheaf).flip.obj
      (SheafOfModules.unit U.1.toScheme.ringCatSheaf)).mapIso
        (affineBasisSheafIso U M b).symm.op ≪≫
      SheafOfModules.homObjFreeUnitIso I ≪≫
      ((Scheme.Modules.restrictFunctor U.2.isoSpec.hom).mapIso
        ((tilde.functor Γ(Y, U.1)).mapIso
          ((ModuleCat.homLinearEquiv.trans b.dualBasis.repr).toModuleIso) ≪≫
            tildeFinsupp I) ≪≫ Scheme.Modules.restrictFreeIso U.2.isoSpec.hom I).symm

/-- The finite basis dual comparisons commute with precomposition, for any
choices of bases on the two modules.
Source: Stacks Project, schemes.tex, Tag 01HV; duality.tex, Tag 0BQZ.
(blueprint: lem-sc-affine-finite-free-dual-naturality).

Proof: On a principal open D(g), the basis sheaf is the free module on the
localized basis. The free internal dual is identified with its coordinates by
evaluation on those generators. The dual-basis representation of a functional
has exactly these coordinates, by Basis.dualBasis_repr. Thus the displayed
comparison sends an internal functional to the vector of its evaluations,
regarded as the localized module dual. If f has matrix (a_ij) in the two bases,
precomposition on either side sends an evaluation vector (v_i) to
(sum_i a_ij v_i)_j. Localization preserves these finite sums and products, so
the two composites agree on D(g). They agree on all opens by the sheaf property,
since the principal opens form a basis. Transport by U.isoSpec preserves the
identity. This also proves independence of the basis. No nontriviality of the
ring is required: for rank zero or a zero ring all the same formulas hold and
the maps between zero modules are unique. -/
theorem affineBasisDualIso_naturality {Y : Scheme.{u}} (U : Y.affineOpens)
    (M N : ModuleCat.{u} Γ(Y, U.1)) {I J : Type u} [Fintype I] [Fintype J]
    (bM : Basis I Γ(Y, U.1) M) (bN : Basis J Γ(Y, U.1) N) (f : N ⟶ M) :
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    SheafOfModules.homObjMap (R := U.1.toScheme.toRingedSpace.sheaf)
        (T.map f) (𝟙 (SheafOfModules.unit U.1.toScheme.ringCatSheaf)) ≫
      (affineBasisDualIso U N bN).hom =
    (affineBasisDualIso U M bM).hom ≫
      T.map (ModuleCat.ofHom (Linear.leftComp Γ(Y, U.1)
        (ModuleCat.of Γ(Y, U.1) Γ(Y, U.1)) f)) := by sorry

end AlgebraicGeometry
