/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.ChangeOfRingsComplex
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellation
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Change of rings preserves K-flat complexes

Source: Stacks Project, Cohomology on Sites, Lemma 21.18.1, Tag 0G7E.

Unlike `SheafOfModules.changeOfRings_isKFlat_of_flat_terms`, no flatness of the terms is
assumed: K-flatness of `K ⊗_R S` only uses the tensor cancellation
`U(N ⊗_S (M ⊗_R S)) ≅ UN ⊗_R M` and the exactness of restriction of scalars.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  {R S : Sheaf J CommRingCat.{max u v}} (φ : R ⟶ S)
  (K : CochainComplex (SheafOfModules.{max u v}
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)

end SheafOfModules
