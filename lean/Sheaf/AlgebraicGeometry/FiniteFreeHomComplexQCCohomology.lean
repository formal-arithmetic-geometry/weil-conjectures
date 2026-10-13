/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Quasi-coherent cohomology of Hom from a finite free complex

Source: Stacks Project, Tags 0A6H (2) and 08I5, finite-column Hom calculation.
(blueprint: lem-sc-finite-free-hom-complex-qc-cohomology)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Hom from a bounded complex of finite free modules preserves quasi-coherent cohomology.

Source: Stacks Project, Tag 0A6H (2), using the finite-column calculation in Tag 08I5.

Proof: filter the finite source complex by its stupid truncations. The successive quotients
are single finite free modules placed in one degree. Applying internal Hom gives a finite
filtration, split in each degree, whose successive quotient complexes are shifts of finite
biproducts of the target complex. Finite free internal Hom is a finite biproduct, so its
cohomology is a finite biproduct of the target's cohomology and is quasi-coherent. Induct
along the finite filtration. For each short exact sequence of Hom complexes A → B → C,
the long exact sequence gives 0 → coker δ^(n-1) → H^n(B) → ker δ^n → 0, where
δ^(n-1) : H^(n-1)(C) → H^n(A) and δ^n : H^n(C) → H^(n+1)(A) are the connecting
maps. Kernels, cokernels, and extensions of quasi-coherent sheaves on a scheme are
quasi-coherent, so H^n(B) is quasi-coherent.
For the localized site of U, transport these facts through the exact equivalence with
module sheaves on U.toScheme. Transport back to obtain the stated property. Empty support
and rank zero give zero complexes and zero cohomology; no boundedness of the target is used.
(blueprint: lem-sc-finite-free-hom-complex-qc-cohomology). -/
theorem finiteFree_homComplex_qc_cohomology
    (X : Scheme.{u}) (U : X.Opens)
    (E I : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hEbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (E.X i))
    (hEfree : ∀ i : ℤ, ∃ r : ℕ, Nonempty (E.X i ≅ SheafOfModules.free
      (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r))))
    (hI : ∀ i : ℤ, (I.homology i).IsQuasicoherent) (n : ℤ) :
    ((homComplex (R := X.toRingedSpace.sheaf.over U) E I).homology n).IsQuasicoherent := by
  sorry

end AlgebraicGeometry
