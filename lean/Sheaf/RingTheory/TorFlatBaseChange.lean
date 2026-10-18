/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.RingTheory.TorCoefficientModule
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.Algebra.Homology.FreeResolutionSesSplit

/-!
# Tor base change along a flat coefficient extension

Source: Stacks Project, Algebra, Tags 00LY, 00M7 and 00M8, with the fixed-base
coefficient adaptation (blueprint: lem-trf-tor-flat-base-change).

The coefficient modules and coefficient map are the existing declarations in
`Sheaf.RingTheory.TorCoefficientModule`. We extend that canonical map using
`LinearMap.liftBaseChange` and the tensor symmetry.

## Main definitions and statements

* `torFlatBaseChange_scalarTower`: compatibility of the existing coefficient actions.
* `torCoefficientBaseChange`, `torFlatBaseChangeMap`: the canonical tensor extensions.
* `tor_flat_base_change`: bijectivity and faithful-flat detection of vanishing.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- The existing coefficient A-action and coefficient B-action on Tor form a tower.

Proof: both actions are functorial images of multiplication on B. The identity
mul_(g(a)*b) = mul_g(a) composed with mul_b is preserved by the Tor functor.
Evaluating this identity gives (a • b) • x = a • (b • x).
Source: Stacks Project, Algebra, Tag 00M7, item (1); node proof steps 1 and 4
(blueprint: lem-trf-tor-flat-base-change).
-/
theorem torFlatBaseChange_scalarTower
    {R A B M : Type u} [CommRing R] [CommRing A] [CommRing B]
    [AddCommGroup M] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [Module R M] (n : ℕ) :
    letI : Module B (torCoefficientModule R A (ModuleCat.of R M) B n) :=
      (torCoefficientModule R B (ModuleCat.of R M) B n).isModule
    IsScalarTower A B (torCoefficientModule R A (ModuleCat.of R M) B n) := by
  sorry

/-- The canonical B-linear extension of the existing coefficient map on Tor.
It sends b tensor t to b • Tor(M,g)(t) by `LinearMap.liftBaseChange_tmul`.
Source: Stacks Project, Algebra, Tags 00LY, 00M7 and 00M8; node proof step 4
(blueprint: lem-trf-tor-flat-base-change).
-/
noncomputable def torCoefficientBaseChange
    {R A B M : Type u} [CommRing R] [CommRing A] [CommRing B]
    [AddCommGroup M] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [Module R M] (n : ℕ) :
    letI : Module B (torCoefficientModule R A (ModuleCat.of R M) B n) :=
      (torCoefficientModule R B (ModuleCat.of R M) B n).isModule
    TensorProduct A B (torCoefficientModule R A (ModuleCat.of R M) A n) →ₗ[B]
      torCoefficientModule R A (ModuleCat.of R M) B n := by
  letI : Module B (torCoefficientModule R A (ModuleCat.of R M) B n) :=
    (torCoefficientModule R B (ModuleCat.of R M) B n).isModule
  letI := torFlatBaseChange_scalarTower (R := R) (A := A) (B := B) (M := M) n
  exact LinearMap.liftBaseChange B
    (torCoefficientLinearMap R A (ModuleCat.of R M) A B n (Algebra.ofId A B))

/-- The node's canonical coefficient map on Tor tensor B, using tensor symmetry.
It sends t tensor b to b • Tor(M,g)(t). Under the symmetry the source has its
usual B-action, and this map is the B-linear extension just constructed.
Source: Stacks Project, Algebra, Tags 00LY, 00M7 and 00M8; node proof step 4
(blueprint: lem-trf-tor-flat-base-change).
-/
noncomputable def torFlatBaseChangeMap
    {R A B M : Type u} [CommRing R] [CommRing A] [CommRing B]
    [AddCommGroup M] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [Module R M] (n : ℕ) :
    TensorProduct A (torCoefficientModule R A (ModuleCat.of R M) A n) B →ₗ[A]
      torCoefficientModule R A (ModuleCat.of R M) B n := by
  letI : Module B (torCoefficientModule R A (ModuleCat.of R M) B n) :=
    (torCoefficientModule R B (ModuleCat.of R M) B n).isModule
  letI := torFlatBaseChange_scalarTower (R := R) (A := A) (B := B) (M := M) n
  exact ((torCoefficientBaseChange (R := R) (A := A) (B := B) (M := M) n).restrictScalars A).comp
    (TensorProduct.comm A _ B).toLinearMap

/-- Flat coefficient extension makes the canonical Tor coefficient map bijective,
and faithfully flat extension detects Tor vanishing.

Proof (the five steps of the node):
1. Choose a free R-resolution P of M using lem-weil-pbc-free-resolution-ses-split
   on 0 → M → M → 0 → 0. Let C = P tensor_R A and D = P tensor_R B, without
   augmentations and with degree -1 zero. By def-weil-pbc-tor-modules their
   homologies are the indicated Tor modules, with their coefficient actions.
2. The tensor universal property (def-weil-pbc-module-tensor-product) gives the
   B-linear chain isomorphism (P tensor_R A) tensor_A B → P tensor_R B sending
   (p tensor a) tensor b to p tensor g(a)b. Its inverse sends p tensor b to
   (p tensor 1) tensor b. Balancing, inverse identities, and compatibility with
   differentials hold on these generators.
3. Flatness and lem-weil-pbc-flat-tensor-exact make - tensor_A B exact and additive.
   Apply clause (c) of lem-sp-exact-functor-preserves-homology to obtain
   H_n(C) tensor_A B ≅ H_n(C tensor_A B), sending [z] tensor b to [z tensor b].
   Only three terms are used; degree zero uses C_{-1} = 0.
4. Compose with homology of the step-2 isomorphism. A cycle sum p_i tensor a_i
   maps to the class of sum p_i tensor g(a_i)b. Functoriality of Tor identifies
   this with b • Tor(M,g)([z]), the defining formula of `torFlatBaseChangeMap`.
   Tensor generators determine the map, so it is this canonical map that is bijective.
5. If B is faithfully flat and Tor(M,B) vanishes, step 4 implies
   T tensor_A B = 0 for T = Tor(M,A). Switch the tensor factors. Reflection of
   exactness by def-weil-pbc-faithfully-flat-ring-map, applied to 0 → T → 0,
   shows that T = 0.

Source: Stacks Project, Algebra, Tags 00LY, 00HD, 00HB and 00M8, adapted to fixed R;
homology Tag 010N (blueprint: lem-trf-tor-flat-base-change).
-/
theorem tor_flat_base_change
    {R A B M : Type u} [CommRing R] [CommRing A] [CommRing B]
    [AddCommGroup M] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [Module R M]
    (hf : Module.Flat A B) (n : ℕ) :
    Function.Bijective (torFlatBaseChangeMap (R := R) (A := A) (B := B) (M := M) n) ∧
    (Module.FaithfullyFlat A B →
      IsZero (torCoefficientModule R A (ModuleCat.of R M) B n) →
      IsZero (torCoefficientModule R A (ModuleCat.of R M) A n)) := by
  sorry

end ModuleCat
