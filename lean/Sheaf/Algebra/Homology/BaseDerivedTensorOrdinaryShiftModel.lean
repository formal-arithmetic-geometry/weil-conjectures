/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
import Sheaf.CategoryTheory.RightKanExtensionCoherentShift

/-! # Transport of the ordinary derived tensor comparison

Source: Stacks Project, Tags 06Y6 and 08IB; an agent-written shift reduction
for the tensor inheritance in Tag 0DJA(1).
(blueprint: lem-pc-base-derived-tensor-ordinary-shift-model).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]

/-- Transport the derived model and its ordinary comparison over the tensor algebra.
Source: Stacks Project, Tag 06Y6 (exact derived tensor functor) and Tag 08IB
(base-change comparison). The following shift argument is an agent-written
algebraic ingredient for the tensor inheritance in Tag 0DJA(1).

Proof: keep the universal derived functor and its counit. Integer shift on the
homotopy and derived categories is an equivalence. Conjugating the derived
functor by these equivalences again derives ordinary extension, since the latter
commutes with shift. The universal property gives an isomorphism between the
conjugated functor and the original one, compatible with its counit. Restrict e
and apply this isomorphism and the homology shift map. In degree i+n this
identifies the derived B-cohomology of L with that of K in degree i. Give L the
E-cohomology modules of K reindexed by j-n, using the integer equality when
j=i+n. Naturality in a times the identity and cohomologyIso_smul make the
identification E-linear, giving eT. Transport ordinaryIso through e and the
termwise extension shift isomorphism; its formula on pure tensors is unchanged.
Define the comparison by the transported counit, and use counit compatibility
to obtain the ordinary square below. Its E-linearity follows from naturality
in a times the identity and B-linearity. Construct ordinaryToLocalized by its
coefficient formula, and transpose comparison followed by its homology map
under extension/restriction to fill the remaining model fields. These last
fields are not asserted to commute with shifts here. No arbitrary model
witness is selected. Zero complexes, n=0, nonflat coefficient maps and arbitrary
e are included: the proof uses equivalences and naturality, not invertibility
of the comparison.
(blueprint: lem-pc-base-derived-tensor-ordinary-shift-model). -/
theorem exists_baseDerivedTensor_ordinary_shift_model
    (K L : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) (e : L ≅ K⟦-n⟧)
    (mK : BaseDerivedTensorCohomologyModel R A B K C) (i : ℤ) :
    let F := (extendScalars.{u, u, u} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
      (.up ℤ)
    let eH := (HomologicalComplex.homologyFunctor (ModuleCat.{u} (A ⊗[R] B))
      (.up ℤ) (i + n)).mapIso (F.mapIso e ≪≫ (F.commShiftIso (-n)).app K) ≪≫
      (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} (A ⊗[R] B)) (-n) (i + n) i
        (by omega)).app (F.obj K)
    ∃ (mL : BaseDerivedTensorCohomologyModel R A B L C)
      (eT : mL.cohomology (i + n) ≅ mK.cohomology i),
      mL.comparison (i + n) ≫ eH.hom = eT.hom ≫ mK.comparison i := by sorry

end ModuleCat
