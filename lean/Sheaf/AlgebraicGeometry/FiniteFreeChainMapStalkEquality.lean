/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Detecting equality of bounded finite free chain maps near a point

Source: lem-pc-perfect-locus, finite matrix equations after shrinking.
(blueprint: lem-pc-finite-free-chain-map-stalk-equality)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Equality of two fixed chain maps at the stalk holds on a smaller open.

Source: lem-pc-finite-free-stalk-homotopy-p-only, step 3, expanding the finite
calculation in lem-pc-perfect-locus (first two proof paragraphs).
(blueprint: lem-pc-finite-free-chain-map-stalk-equality)

Proof: Use the finite bases of P and their images under restriction, identified by
restrictFunctorIsoPullback and pullbackFreeIso. The degreewise differences a.f n-b.f n
are matrices of sections on U. Outside [0,d] their source is zero, so their components
are zero without shrinking. Within [0,d] there are finitely many entries. The equality
of the pulled-back chain maps says that the germs of these entries at y vanish, by
freeMatrix_pullback and the structure-ring stalk comparison for fromSpecStalkOfMem.
For each entry use the germ equality criterion to find an open containing y inside U
where it is zero. Intersect these finitely many opens, obtaining W. Restriction carries
the matrix to its restricted entries, so all component differences are zero on W.
Extensionality of morphisms of homological complexes gives the required equality.
The extra restriction through V merely transports the chosen bases; it imposes no
condition on a or b. The zero complex, rank zero, d=0, and U=V are covered by the same
argument, with an empty intersection taken to be U. -/
theorem exists_shrink_chainMap_eq_of_stalk
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (y : Y) (V U : Y.Opens) (hUV : U ≤ V) (hyU : y ∈ U)
    (a b :
      (((restrictFunctor (Y.homOfLE hUV)).mapHomologicalComplex _).obj
        (((restrictFunctor V.ι).mapHomologicalComplex _).obj P)) ⟶
      (((restrictFunctor (Y.homOfLE hUV)).mapHomologicalComplex _).obj
        (((restrictFunctor V.ι).mapHomologicalComplex _).obj P)))
    (heq : ((Modules.pullback (U.fromSpecStalkOfMem y hyU)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map a =
      ((Modules.pullback (U.fromSpecStalkOfMem y hyU)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map b) :
    ∃ (W : Y.Opens) (hWU : W ≤ U), y ∈ W ∧
      ((restrictFunctor (Y.homOfLE hWU)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map a =
      ((restrictFunctor (Y.homOfLE hWU)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map b := by sorry

end AlgebraicGeometry.Scheme.Modules
