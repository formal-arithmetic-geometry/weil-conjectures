/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Flat.Basic

/-! # Tor-independent localized tensor comparison on left K-flat complexes

Source: Stacks Project, More on Algebra, Section 06Y5 and Tag 06Y6;
perfect.tex, Tag 08IB, the Tor-independent affine calculation.
(blueprint: lem-pc-tor-independent-kflat-localized-comparison).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace ModuleCat

/-- Tor independence of A and B over R suffices for the canonical localized
comparison on any A-K-flat complex. Only flatness of the final E-algebra is needed,
where E = A tensor over R B. The cohomology model may be any model with its recorded
universal counit and comparison equations; this asserts invertibility of its specified
map, not the existence of an unrelated isomorphism.

Source: Stacks Project, More on Algebra, Section 06Y5 and Tag 06Y6;
perfect.tex, Tag 08IB, the Tor-independent affine calculation.
(blueprint: lem-pc-tor-independent-kflat-localized-comparison).

Proof:
1. Resolve B[0] over R by a bounded-above projective complex F with augmentation
   F -> B[0]. Its tensor with A has degree-zero cohomology A tensor_R B and
   negative-degree cohomology Tor_i^R(A,B), by balancedness and tensor symmetry.
   To verify balancedness, resolve both modules projectively and use the two
   filtrations of their double tensor complex; its diagonals are finite in each
   degree because both resolutions are bounded above. The hypothesis makes the augmentation
   A tensor_R F -> E[0] a quasi-isomorphism, as a complex of A-modules.
2. Tensor this augmentation with Q over A. The cone is acyclic by step 1;
   A-K-flatness of Q makes its total tensor with this cone acyclic. Tensor and cone
   commute, so the resulting augmentation is a quasi-isomorphism. The mixed tensor
   associator identifies its source with Q tensor_R F and its target with
   Q tensor_A E = Q tensor_R B, with the usual signed total differentials.
3. Since F is R-K-flat, balanced derived tensor computes Q tensor_R^L B by
   Q tensor_R F, even if Q is not R-K-flat. The augmentation of step 2 is the
   derived-to-ordinary counit: both arise by applying tensor to F -> B[0].
   The balanced comparison is natural for multiplication by A and by B.
   Thus it respects the E-action on cohomology. The model's comparison_eq and
   cohomologyIso_smul identify its comparison with this map on cohomology.
   Forgetting to B-modules reflects isomorphisms, so comparison is an E-module
   isomorphism in every degree.
4. D is E-flat, so extension E -> D preserves the cycles/boundaries exact
   sequences and their quotient, giving its canonical homology isomorphism.
   Tensor associativity identifies D tensor_E (E tensor_A Q) with D tensor_A Q.
   On pure tensors this is the map in ordinaryToLocalized_tmul. By localized_eq
   and the scalar-extension adjunction, localizedComparison is exactly extension
   of comparison followed by this homology isomorphism and associativity. All
   three are invertible. No boundedness of Q or flatness of A or B over R is used;
   the zero complex and zero coefficient rings satisfy the same cone argument. -/
theorem localizedComparison_isIso_of_torIndependent_kFlat
    {R A B D : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (hTor : ∀ i : ℕ, 0 < i →
      IsZero (((CategoryTheory.Tor' (ModuleCat.{u} R) i).obj (ModuleCat.of R A)).obj
        (ModuleCat.of R B)))
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ L : CochainComplex (ModuleCat.{u} A) ℤ, L.Acyclic →
      (CochainComplex.mapBifunctor L Q (MonoidalCategory.curriedTensor _)).Acyclic)
    (hD : Module.Flat (A ⊗[R] B) D)
    (M : BaseDerivedTensorCohomologyModel R A B Q D) :
    ∀ i : ℤ, IsIso (M.localizedComparison i) := by sorry

end ModuleCat
