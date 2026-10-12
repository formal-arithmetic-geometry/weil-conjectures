/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-!
# Filtered-colimit preservation by tensor totalization

The tensor-totalization clause of `lem-pc-module-filtered-colimits-tensor`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

set_option hygiene false in
local notation "Mod" R => SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

/-- Tensor totalization with a fixed complex preserves filtered colimits.
Source: Stacks Project, Modules on Sites, Lemma 03EP, together with the direct-sum
construction of total complexes (blueprint: lem-pc-module-filtered-colimits-tensor-preserves).

Proof: Tensoring with a fixed module is a left adjoint by
`lem-pc-sheaf-modules-tensor-closed`, using symmetry for the right tensor factor.
Colimits of complexes are computed degreewise. Thus, for each pair of degrees
(a,b), tensoring the degree-a colimit with P in degree b is canonically the
colimit of the corresponding tensors. In total degree n, take the coproduct
of these identifications over all pairs (a,b) with a+b=n. Interchanging the
filtered colimit and this coproduct gives a colimit cocone in degree n.
The identifications are natural in both degrees and commute with each tensor
differential; hence they commute with the signed sum defining the total
differential. Degreewise colimit cocones therefore assemble to a colimit
cocone of total complexes. It is the image of the original colimit cocone
under the displayed functor, so this proves preservation of the canonical
colimit, rather than just existence of an isomorphism of objects. No
boundedness or flatness is needed, since the totalization uses coproducts. -/
theorem preservesFilteredColimitsTensorTotal
    (C : Type u) [Category.{u} C] (J : GrothendieckTopology C)
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (I : Type u) [Category.{u} I] [IsFiltered I] :
    ∀ P : CochainComplex (Mod R) ℤ,
      PreservesColimitsOfShape I
        ((((@curriedTensor (Mod R) _ (monoidalCategory R)).mapBifunctorHomologicalComplex
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).flip.obj P) ⋙
          HomologicalComplex₂.totalFunctor (Mod R) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) (ComplexShape.up ℤ)) := by
  sorry

end SheafOfModules
