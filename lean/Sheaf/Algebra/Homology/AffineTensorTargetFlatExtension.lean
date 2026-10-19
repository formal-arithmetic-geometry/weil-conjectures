/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Algebra.Homology.RingTensorCohomology
public import Mathlib.RingTheory.TensorProduct.Basic

import WeilConjectures.Algebra.Homology.BaseTensorOrdinaryIso

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Flat extension of prescribed ordinary tensor cohomology lifts

Source: Stacks Project, Tags 0DJ8, 00DL and 00CS.
(blueprint: lem-pc-affine-tensor-target-flat-extension). -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct

namespace RingTensorCohomology

/-- Flat coefficient extension of any prescribed ordinary tensor-cohomology lift.
Source: Stacks Project, algebra.tex, Tag 00CS; more-algebra.tex, Tag 06Y6;
perfect.tex, Tag 0DJ8, target of the affine displayed localization identity.
(blueprint: lem-pc-affine-tensor-target-flat-extension)

Proof: in every degree, the balanced tensor identification sends b tensor x to
(1 tensor b) tensor x and its inverse sends (a tensor b) tensor x to b tensor ax.
These maps commute with the differential and all morphisms of A-complexes.
Applied to the functorial resolution, they identify target with restriction of
homology of P tensor_A (A tensor_R B). The supplied eT identifies the underlying
B-module of T with this homology. The equation hT identifies its A-action with
that on P; the two tensor-factor actions determine the entire tensor-algebra
module structure. Thus eT upgrades to the tensor-algebra cohomology identification.
Flat scalar extension along f is exact, so its natural homology comparison is
invertible. Finally tensor associativity identifies D tensor_C (C tensor_A P)
with D tensor_A P, where C = A tensor_R B. The equation hfA says the resulting
A-to-D scalar map is the given algebra map. Compose these natural isomorphisms.
This argument needs no primes, no global-to-local source comparison, and no
flatness of B over R. The zero complex and identity coefficient extension satisfy
the same formula; degrees are arbitrary integers, with no boundedness assumed. -/
theorem affineTensorTarget_flat_extension
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra A D] (i : ℤ)
    (T : CochainComplex (ModuleCat.{u} A) ℤ ⥤ ModuleCat.{u} (A ⊗[R] B))
    (eT : T ⋙ ModuleCat.restrictScalars Algebra.TensorProduct.includeRight.toRingHom ≅
      target R A B i)
    (hT : ∀ (M : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) (x : T.obj M),
      eT.hom.app M ((Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) • x) =
        (target R A B i).map (a • 𝟙 M) (eT.hom.app M x))
    (f : (A ⊗[R] B) →+* D) (hf : f.Flat)
    (hfA : ∀ a : A,
      f (Algebra.TensorProduct.includeLeft (S := R) a : A ⊗[R] B) = algebraMap A D a) :
    Nonempty (T ⋙ ModuleCat.extendScalars f ≅
      resolution A ⋙ extend A D ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} D) (.up ℤ) i) := by
  sorry

end RingTensorCohomology
