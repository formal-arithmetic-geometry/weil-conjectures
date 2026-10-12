/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.Algebra.Homology.MixedTotalTensor
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.KFlatTensorQuasiIso
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat

/-!
# Quasi-isomorphisms for mixed total tensor

Source: Stacks Project, More on Algebra, Tags 064L and 06Y0.
(blueprint: lem-pc-mixed-tensor-kflat-quasi-iso)
-/

@[expose] public section

universe u

open CategoryTheory

namespace CochainComplex

/-- Mixed total tensor preserves quasi-isomorphisms in the two K-flat situations.
Source: Stacks Project, Tags 064L and 06Y0.
(blueprint: lem-pc-mixed-tensor-kflat-quasi-iso)

Proof: Restrict the A-complexes to R. The canonical associativity isomorphism
N ⊗_A (A ⊗_R E) ≅ N ⊗_R E, followed by signed symmetry on total complexes,
identifies the restriction of the mixed total with the ordinary total tensor.
Restriction of scalars is exact and reflects isomorphisms, so it detects
quasi-isomorphisms. For the first clause choose an R-K-flat resolution K → N
of the restricted complex. In the tensor square for a and this resolution,
the two vertical arrows and the top arrow are quasi-isomorphisms by K-flatness;
two-of-three gives the bottom arrow. For the second clause K-flatness of F
applied to the restricted quasi-isomorphism u gives the result directly.
The termwise identifications commute with the signed differentials and both
variable maps. No flatness of A over R is required. -/
theorem mixedTensor_kFlat_quasiIso {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) :
    let B := (ModuleCat.mixedTensor f).flip.map₂CochainComplex
    (∀ (N : CochainComplex (ModuleCat.{u} A) ℤ)
      (E E' : CochainComplex (ModuleCat.{u} R) ℤ) (a : E ⟶ E'),
      QuasiIso a → (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat E →
      (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat E' →
      QuasiIso ((B.map a).app N)) ∧
    (∀ (N N' : CochainComplex (ModuleCat.{u} A) ℤ) (u : N ⟶ N'),
      QuasiIso u → ∀ F : CochainComplex (ModuleCat.{u} R) ℤ,
      (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat F →
      QuasiIso ((B.obj F).map u)) := by sorry

end CochainComplex
