/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q76
-/
module

public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.MixedTotalTensor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Maps
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.CategoryTheory.Monoidal.Tor
import WeilConjectures.CategoryTheory.TruncationTriangle
import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Algebra.Homology.DerivedTensorModuleTorComparison
import WeilConjectures.Algebra.Category.ModuleCat.TorSymmetry
import WeilConjectures.AlgebraicGeometry.TorLongExactFirstVariable

/-! # Flat module lifts and bounded-above derived lifts

Source: Stacks Project, examples-defos.tex, Tags 0DZ1 and 0DZ2, including the
free-resolution footnote in 0DZ2.
(blueprint: lem-sfb-flat-module-derived-lift-criterion).

A pushout square of commutative rings encodes P = P' tensor_{A'} A. Scalar
extension is the published ordinary derived change of rings, computed on K-flat
complexes. Kernel modules are presented by injective additive maps whose images
are the specified ideals and whose action equations prescribe quotient actions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

/-- Flat module lifts are equivalent to bounded-above derived lifts, with no
finite generation or Noetherian hypothesis.

Source: Stacks Project, Tag 0DZ1, lemma-lift-equivalence-module-derived.
(blueprint: lem-sfb-flat-module-derived-lift-criterion).

Proof (steps 1--5 of the node):
1. For an A'-flat lift L, take L[0]. The flat-algebra derived tensor exchange
   identifies its derived reduction with the ordinary reduction M[0]. Flat tensor
   exactness proves this using a free A'-resolution of A.
2. The truncation triangle, the derived tensor upper bound, the homology exact
   sequence and the degree-zero Tor comparison give, for E in degrees at most t,
   H^t(E tensor^L V) = H^t(E) tensor V.
3. The kernel J of P' -> P is IP', and J^r = 0. If T tensor P = 0, then
   T = JT = J^rT = 0, without finite generation. A largest positive cohomology
   degree of the bounded-above lift would contradict step 2. Thus C' is in
   degrees at most zero; this argument includes M = 0.
4. Set L = H^0(C'). Step 2 gives its prescribed reduction. Tensor the triangle
   tau_{<=-1} C' -> C' -> L[0] with P. The upper bound and homology exact sequence
   give a surjection H^-1(C' tensor^L P) -> Tor_1^{P'}(L,P), so this Tor vanishes.
5. Flat-algebra tensor exchange and Tor symmetry give Tor_1^{A'}(A,L) = 0.
   The first-variable Tor exact sequence makes I tensor L -> L injective.
   Its quotient L/IL = M is A-flat. The nilpotent-ideal module-flatness criterion
   gives A'-flatness. Ordinary tensor balancing identifies reduction over P'
   with reduction over A', including its P-module structure. -/
theorem flat_module_lift_iff_boundedAbove_derived_lift
    {Ap A Pp P : Type u} [CommRing Ap] [CommRing A] [CommRing Pp] [CommRing P]
    (q : Ap →+* A) (f : Ap →+* Pp) (g : A →+* P) (p : Pp →+* P)
    (hq : Function.Surjective q) (hI : IsNilpotent (RingHom.ker q)) (hf : f.Flat)
    (hsquare : IsPushout (CommRingCat.ofHom q) (CommRingCat.ofHom f)
      (CommRingCat.ofHom g) (CommRingCat.ofHom p))
    (M : ModuleCat.{u} P) (hM : Module.Flat A ((restrictScalars g).obj M)) :
    (∃ L : ModuleCat.{u} Pp, Module.Flat Ap ((restrictScalars f).obj L) ∧
      Nonempty ((extendScalars p).obj L ≅ M)) ↔
    (∃ Cp : DerivedCategory (ModuleCat.{u} Pp), (∃ b : ℤ, Cp.IsLE b) ∧
      Nonempty ((ordinaryDerivedExtendScalars p).obj Cp ≅
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj M))) := by
  sorry

/-- The canonical derived-to-ordinary tensor map on two degree-zero modules.
It is the lax monoidal comparison of Q, followed by the two canonical
single-complex identifications. No arbitrary map or resolution is chosen.

Source: Stacks Project, Tag 0DZ2, free-A-resolution footnote, and Section 06Y5.
(blueprint: lem-sfb-flat-module-derived-lift-criterion). -/
def flatLiftModuleTensorComparison {P : Type u} [CommRing P]
    (M J : ModuleCat.{u} P) :
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj M) ⊗
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj J) ⟶
      DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj (M ⊗ J)) :=
  Functor.LaxMonoidal.μ DerivedCategory.Q
      ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj M)
      ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj J) ≫
    DerivedCategory.Q.map
      ((CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) J
        ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj M)).hom ≫
        (HomologicalComplex.singleMapHomologicalComplex (tensorRight J) (.up ℤ) 0).hom.app M)

/-- The square-zero kernel identification and invertibility of the canonical
comparison from derived tensor to ordinary tensor, as an assertion in D(P).

Source: Stacks Project, Tag 0DZ2, lemma-lift-equivalence-module, square-zero proof
and its explicit free-A-resolution footnote.
(blueprint: lem-sfb-flat-module-derived-lift-criterion).

Proof (steps 6--7 of the node):
6. Tensor 0 -> I -> A' -> A -> 0 with the A'-flat algebra P'. Flat tensor
   exactness identifies IP' with I tensor_{A'} P'. Since I^2 = 0, balancing
   descends this to P tensor_A I, with the pure-tensor formula below. The same
   injection test after base change proves P is A-flat.
7. Apply flat-algebra derived tensor exchange to (A,P,I,M[0]). A free A-resolution
   F -> I becomes an augmented resolution M tensor_A F -> M tensor_A I because
   M is A-flat. The augmentation clause of the exchange identifies this map
   with the canonical derived-to-ordinary comparison. Transport the kernel
   identification from step 6; hence the specified lax monoidal comparison of Q
   is invertible. The single-complex tensor identification gives (M tensor_P J)[0].
   Tensoring theta with M gives its displayed ordinary balancing identification
   with (M tensor_A I)[0], encoded by mixedTensor. -/
theorem squareZero_kernel_tensor_comparison_of_flat
    {Ap A Pp P : Type u} [CommRing Ap] [CommRing A] [CommRing Pp] [CommRing P]
    (q : Ap →+* A) (f : Ap →+* Pp) (g : A →+* P) (p : Pp →+* P)
    (hq : Function.Surjective q) (hI : RingHom.ker q ^ 2 = ⊥) (hf : f.Flat)
    (hsquare : IsPushout (CommRingCat.ofHom q) (CommRingCat.ofHom f)
      (CommRingCat.ofHom g) (CommRingCat.ofHom p))
    (M : ModuleCat.{u} P) (hM : Module.Flat A ((restrictScalars g).obj M))
    (I : ModuleCat.{u} A) (i : I →+ Ap) (hi : Function.Injective i)
    (hiker : Set.range i = RingHom.ker q)
    (hiaction : ∀ (a : Ap) (x : I), i (q a • x) = a * i x)
    (J : ModuleCat.{u} P) (j : J →+ Pp) (hj : Function.Injective j)
    (hjker : Set.range j = Ideal.map f (RingHom.ker q))
    (hjaction : ∀ (a : Pp) (x : J), j (p a • x) = a * j x) :
    ∃ θ : (extendScalars g).obj I ≅ J,
      (∀ (a : Pp) (x : I), j (θ.hom (p a ⊗ₜ[A, g] x)) = a * f (i x)) ∧
      IsIso (flatLiftModuleTensorComparison M J) ∧
      ∃ e : M ⊗ J ≅ ((mixedTensor g).obj M).obj I,
        ∀ (m : M) (y : (extendScalars g).obj I),
          e.hom (m ⊗ₜ[P] θ.hom y) = m ⊗ₜ[P] y := by
  sorry

end ModuleCat
