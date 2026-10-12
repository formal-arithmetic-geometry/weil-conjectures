/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.AlgebraicGeometry.StalkRestrictionWithinIso
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Simultaneous lifting of finitely many matrices of free sheaf morphisms

Source: lem-pc-perfect-locus, finite matrix extension near a point.
(blueprint: lem-pc-finite-free-stalk-finite-matrix-lift)
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- A finite family of maps between standard finite free sheaves lifts to one open.

Source: lem-pc-perfect-locus, extension of the finite calculation near a point;
lem-pc-finite-free-reverse-components-lift, proof steps 2 and 3.

Proof: PullbackFreeIso identifies the source and target of each f q with
standard free sheaves over Spec O_{Y,y}. Express f q as a matrix in these
standard bases, using freeMatrix. Its entries are global functions on
Spec O_{Y,y}, hence elements of O_{Y,y}, via the global-sections isomorphism
for Spec. For each entry choose an open neighbourhood of y inside V and a
section representing its germ. There are finitely many entries, since the
index type and every rank are finite. Take the intersection U of these opens
and restrict the representative sections to U. Use the restricted standard
bases, identified by restrictFreeIso, to define g q by the matrix of these
sections. Replace restriction by pullback, compose pullbacks, and use the
identity U.fromSpecStalkOfMem composed with Y.homOfLE equals V.fromSpecStalkOfMem,
proved by cancellation of V.ι. This gives exactly the natural comparison e
in the statement. The standard free inclusions and projections commute with
these comparisons: apply pullback_map_ιFree_pullbackFreeIso_hom and
pullbackFreeIso_hom_freeπ, and pullback composition to their unit factors.
Thus freeMatrix_pullback identifies the pulled-back entries of g with the
entries of e.hom followed by f followed by e.inv. The inclusions and coordinate
projections of a finite free sheaf determine a morphism, giving the required
equalities. Empty index types and zero ranks have no coefficients; take U=V
when the coefficient list is empty. There is no change of arbitrary bases,
complex, boundedness condition, or reverse-degree support in this lemma.
(blueprint: lem-pc-finite-free-stalk-finite-matrix-lift) -/
theorem exists_finite_free_matrices_of_stalk_local
    {Y : Scheme.{u}} {ι : Type v} [Finite ι]
    (y : Y) (V : Y.Opens) (hyV : y ∈ V)
    (r s : ι → ℕ)
    (f : ∀ q,
      (pullback (V.fromSpecStalkOfMem y hyV)).obj
          (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin (r q)))) ⟶
      (pullback (V.fromSpecStalkOfMem y hyV)).obj
          (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin (s q))))) :
    ∃ (U : Y.Opens) (hUV : U ≤ V) (hyU : y ∈ U),
      let R := restrictFunctor (Y.homOfLE hUV)
      let S := pullback (U.fromSpecStalkOfMem y hyU)
      let e := stalkRestrictionWithinIso y V hyV U hUV hyU
      ∃ (g : ∀ q,
        R.obj (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin (r q)))) ⟶
        R.obj (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin (s q))))),
        ∀ q, S.map (g q) =
          (e.app (SheafOfModules.free (R := V.toScheme.ringCatSheaf)
            (ULift.{u} (Fin (r q))))).hom ≫ f q ≫
          (e.app (SheafOfModules.free (R := V.toScheme.ringCatSheaf)
            (ULift.{u} (Fin (s q))))).inv := by sorry

end AlgebraicGeometry.Scheme.Modules
