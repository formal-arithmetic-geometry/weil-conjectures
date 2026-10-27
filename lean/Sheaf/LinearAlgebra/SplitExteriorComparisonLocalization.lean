/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.LinearAlgebra.ExteriorTopDirectSum
import WeilConjectures.LinearAlgebra.ExteriorPowerLocalization
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Split exact sequences and their top exterior comparison

Source: Stacks Project, Tag 0FJB (`lemma-det-ses`), first proof, omitted verification;
Algebra, Tags 00DK, 00DL and 0C6F for localization.
(blueprint: lem-trf-split-exterior-comparison-localization).

The separate statements record splitting before freeness, the unique arbitrary-lift wedge
map, its section construction, normalized localization comparisons and their cocycles,
and the three empty-wedge cases. No coefficient ring is assumed nontrivial.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w z a b

open scoped TensorProduct

namespace exteriorPower

variable {R : Type u} [CommRing R]
variable {U : Type v} [AddCommGroup U] [Module R U]
variable {V : Type w} [AddCommGroup V] [Module R V]
variable {W : Type z} [AddCommGroup W] [Module R W]

/-- The arbitrary-lift characterization of the exact-sequence wedge map, with the kernel
block first. This formula quantifies over all tuples, not just a chosen basis.
Source: Stacks Project, Tag 0FJB, first proof.
(blueprint: lem-trf-split-exterior-comparison-localization). -/
def IsSplitExteriorComparison (i : U →ₗ[R] V) (p : V →ₗ[R] W) (r s : ℕ)
    (θ : ((⋀[R]^r U) ⊗[R] (⋀[R]^s W)) →ₗ[R] (⋀[R]^(r + s) V)) : Prop :=
  ∀ (x : Fin r → U) (y : Fin s → W) (l : Fin s → V),
    (∀ k, p (l k) = y k) →
      θ ((ιMulti R r x) ⊗ₜ[R] (ιMulti R s y)) =
        ιMulti R (r + s) (Fin.append (fun j ↦ i (x j)) l)

/-- Projectivity supplies a section; every section gives the specified direct-sum
isomorphism and its inverse formula, before any freeness assumption.
Source: Stacks Project, Tag 0FJB, first proof, splitting step.
(blueprint: lem-trf-split-exterior-comparison-localization).

Proof: lift id_W along p by def-weil-pbc-projective-module. For any section σ,
v-σ(p(v)) lies in ker p = im i. Injectivity gives its unique preimage q(v).
Applying i proves q additive and linear. The identities qi=id, qσ=0, pi=0,
pσ=id and iq+σp=id prove the two inverse identities. -/
theorem splitExterior_exists_section [Module.Projective R W]
    (i : U →ₗ[R] V) (p : V →ₗ[R] W) (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p) :
    (∃ σ : W →ₗ[R] V, p.comp σ = LinearMap.id) ∧
    ∀ (σ : W →ₗ[R] V), p.comp σ = LinearMap.id →
      ∃! t : (U × W) ≃ₗ[R] V,
        (∀ (x : U) (y : W), t (x, y) = i x + σ y) ∧
        (∀ q : V, (t.symm q).2 = p q ∧ i (t.symm q).1 = q - σ (p q)) := sorry

/-- Both inverse maps and the section localize in the tensor model A tensor M of M_T.
The last equation specifies localization of t on pure tensors; the inverse is precisely
localization of its first component together with localization of p.
Source: Stacks Project, Tag 0FJB; Algebra, Tags 00DK and 00DL.
(blueprint: lem-trf-split-exterior-comparison-localization).

Proof: localize the five splitting identities in splitExterior_exists_section, using
h(m/a)=h(m)/a. Localization preserves composition and identities. The coordinate
fraction maps identify localization of U × W with U_T × W_T. The localized inverse
identities give injectivity, surjectivity and exactness, including when 0 belongs to T. -/
theorem splitExterior_split_localization
    (i : U →ₗ[R] V) (p : V →ₗ[R] W) (σ : W →ₗ[R] V)
    (hσ : p.comp σ = LinearMap.id) (t : (U × W) ≃ₗ[R] V)
    (ht : ∀ (x : U) (y : W), t (x, y) = i x + σ y)
    (hp : ∀ q : V, (t.symm q).2 = p q)
    {A : Type a} [CommRing A] [Algebra R A] (T : Submonoid R) [IsLocalization T A] :
    Function.Injective (i.baseChange A) ∧ Function.Surjective (p.baseChange A) ∧
    Function.Exact (i.baseChange A) (p.baseChange A) ∧
    (p.baseChange A).comp (σ.baseChange A) = LinearMap.id ∧
    ∃ tA : ((A ⊗[R] U) × (A ⊗[R] W)) ≃ₗ[A] (A ⊗[R] V),
      (∀ x y, tA (x, y) = i.baseChange A x + σ.baseChange A y) ∧
      (∀ q, tA.symm q =
        (((LinearMap.fst R U W).comp t.symm.toLinearMap).baseChange A q,
          p.baseChange A q)) ∧
      (∀ (a₀ : A) (x : U) (y : W),
        tA (a₀ ⊗ₜ[R] x, a₀ ⊗ₜ[R] y) = a₀ ⊗ₜ[R] t (x, y)) := sorry

/-- The arbitrary-lift formula determines a unique isomorphism. It has no basis or section
parameter, so replacement bases and replacement sections yield the same map.
Source: Stacks Project, Tag 0FJB, first proof.
(blueprint: lem-trf-split-exterior-comparison-localization).

Proof: split the sequence using projectivity of the free quotient. Apply
lem-sc-exterior-top-direct-sum and exteriorPower.map to the splitting isomorphism.
Exterior maps preserve identities and composition on spanning pure wedges. This gives
an isomorphism and the formula with the section as lift. Any other lift differs by i(a).
Multilinear expansion puts r+1 kernel vectors in every error term; that wedge is zero
by lem-weil-pbc-exterior-power-free-basis. Pure wedges and pure tensors span, giving
uniqueness, section independence and basis independence. Alternation uses x wedge x=0,
never division by 2. Empty blocks and the zero ring are allowed. -/
theorem existsUnique_splitExteriorComparison
    (i : U →ₗ[R] V) (p : V →ₗ[R] W) (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p)
    (r s : ℕ) (bU : Module.Basis (Fin r) R U) (bW : Module.Basis (Fin s) R W) :
    ∃! θ : ((⋀[R]^r U) ⊗[R] (⋀[R]^s W)) ≃ₗ[R] (⋀[R]^(r + s) V),
      IsSplitExteriorComparison i p r s θ.toLinearMap := sorry

/-- For every section the canonical map is exactly exteriorPower(t) composed with the
canonical concatenation comparison c. Characterizing c on all pure wedges fixes c uniquely.
Source: Stacks Project, Tag 0FJB, first proof, and lem-sc-exterior-top-direct-sum.
(blueprint: lem-trf-split-exterior-comparison-localization).

Proof: on each spanning pure tensor c concatenates the two inclusion blocks; map(t)
applies i to the first and σ to the second. Since pσ=id, the arbitrary-lift formula
for θ gives the same wedge. Equality on spanning tensors proves the equality of maps. -/
theorem splitExteriorComparison_section_composite
    (i : U →ₗ[R] V) (p : V →ₗ[R] W) (r s : ℕ)
    (σ : W →ₗ[R] V) (hσ : p.comp σ = LinearMap.id)
    (t : (U × W) ≃ₗ[R] V) (ht : ∀ x y, t (x, y) = i x + σ y)
    (c : ((⋀[R]^r U) ⊗[R] (⋀[R]^s W)) ≃ₗ[R] (⋀[R]^(r + s) (U × W)))
    (hc : ∀ (x : Fin r → U) (y : Fin s → W),
      c ((ιMulti R r x) ⊗ₜ[R] (ιMulti R s y)) =
        ιMulti R (r + s) (Fin.append (fun j ↦ (x j, 0)) (fun k ↦ (0, y k))))
    (θ : ((⋀[R]^r U) ⊗[R] (⋀[R]^s W)) ≃ₗ[R] (⋀[R]^(r + s) V))
    (hθ : IsSplitExteriorComparison i p r s θ.toLinearMap) :
    θ.toLinearMap = (map (r + s) t.toLinearMap).comp c.toLinearMap := sorry

/-- Normalized exterior and tensor comparisons for this split-exterior construction.
Each field is fixed on spanning wedges or tensors, so these are canonical comparisons,
not arbitrary choices of isomorphisms. The module localizations use their tensor models.
Source: Stacks Project, Algebra, Tags 00DK, 00DL and 0C6F.
(blueprint: lem-trf-split-exterior-comparison-localization). -/
structure SplitExteriorScalarComparison (R : Type u) (A : Type a)
    [CommRing R] [CommRing A] [Algebra R A]
    (U : Type v) (V : Type w) (W : Type z)
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (r s : ℕ) where
  /-- Exterior localization of the kernel block. -/
  kernel : (A ⊗[R] (⋀[R]^r U)) ≃ₗ[A] (⋀[A]^r (A ⊗[R] U))
  /-- Its normalization on pure wedges. -/
  kernel_wedge : ∀ (a₀ : A) (x : Fin r → U),
    kernel (a₀ ⊗ₜ[R] ιMulti R r x) = a₀ • ιMulti A r (fun j ↦ 1 ⊗ₜ[R] x j)
  /-- Exterior localization of the middle module. -/
  middle : (A ⊗[R] (⋀[R]^(r + s) V)) ≃ₗ[A] (⋀[A]^(r + s) (A ⊗[R] V))
  /-- Its normalization on pure wedges. -/
  middle_wedge : ∀ (a₀ : A) (x : Fin (r + s) → V),
    middle (a₀ ⊗ₜ[R] ιMulti R (r + s) x) =
      a₀ • ιMulti A (r + s) (fun j ↦ 1 ⊗ₜ[R] x j)
  /-- Exterior localization of the quotient block. -/
  quotient : (A ⊗[R] (⋀[R]^s W)) ≃ₗ[A] (⋀[A]^s (A ⊗[R] W))
  /-- Its normalization on pure wedges. -/
  quotient_wedge : ∀ (a₀ : A) (y : Fin s → W),
    quotient (a₀ ⊗ₜ[R] ιMulti R s y) = a₀ • ιMulti A s (fun k ↦ 1 ⊗ₜ[R] y k)
  /-- Tensor localization followed by the two exterior comparisons. -/
  tensor : (A ⊗[R] ((⋀[R]^r U) ⊗[R] (⋀[R]^s W))) ≃ₗ[A]
    ((⋀[A]^r (A ⊗[R] U)) ⊗[A] (⋀[A]^s (A ⊗[R] W)))
  /-- Its normalization, with the scalar put in the first factor. -/
  tensor_pure : ∀ (a₀ : A) (x : ⋀[R]^r U) (y : ⋀[R]^s W),
    tensor (a₀ ⊗ₜ[R] (x ⊗ₜ[R] y)) =
      kernel (a₀ ⊗ₜ[R] x) ⊗ₜ[A] quotient (1 ⊗ₜ[R] y)

/-- The normalized comparisons exist uniquely, also for a localization containing zero.
Source: Stacks Project, Algebra, Tags 00DK, 00DL and 0C6F.
(blueprint: lem-trf-split-exterior-comparison-localization).

Proof: the canonical exterior map sends a wedge to the wedge of localized vectors.
new-v2-exterior-power-localization identifies it as a localization in each degree.
The universal properties identify this with A tensor the exterior power, with exactly
the displayed normalization. Tensor localization (lem-weil-pbc-localization-tensor-product)
and the two exterior comparisons give tensor. Spanning wedges and tensors prove uniqueness.
The tensor model is localization by isLocalizedModule_iff_isBaseChange. -/
theorem existsUnique_splitExteriorScalarComparison
    {A : Type a} [CommRing A] [Algebra R A] (T : Submonoid R) [IsLocalization T A]
    (r s : ℕ) : ∃ C : SplitExteriorScalarComparison R A U V W r s,
      ∀ D : SplitExteriorScalarComparison R A U V W r s, D = C := sorry

/-- Under the normalized exterior and tensor identifications, A tensor θ is the same
arbitrary-lift construction on the localized split exact sequence.
Source: Stacks Project, Tag 0FJB, first proof; Algebra, Tags 00DK, 00DL and 0C6F.
(blueprint: lem-trf-split-exterior-comparison-localization).

Proof: localizing the splitting identities gives a split exact sequence. Localizing
basis coordinate isomorphisms gives finite bases of the same lengths. On tensors of
pure wedges with scalar 1, both maps give the wedge of localized kernel vectors followed
by the localized section lifts. These span after scalar extension, so the maps agree.
The arbitrary-lift formula and uniqueness identify the result with every localized
section and every localized basis; the argument includes empty wedges and zero rings. -/
theorem splitExteriorComparison_localization
    (i : U →ₗ[R] V) (p : V →ₗ[R] W) (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p)
    (r s : ℕ) (bU : Module.Basis (Fin r) R U) (bW : Module.Basis (Fin s) R W)
    {A : Type a} [CommRing A] [Algebra R A] (T : Submonoid R) [IsLocalization T A]
    (C : SplitExteriorScalarComparison R A U V W r s)
    (θ : ((⋀[R]^r U) ⊗[R] (⋀[R]^s W)) ≃ₗ[R] (⋀[R]^(r + s) V))
    (hθ : IsSplitExteriorComparison i p r s θ.toLinearMap) :
    ∃ θA : ((⋀[A]^r (A ⊗[R] U)) ⊗[A] (⋀[A]^s (A ⊗[R] W))) ≃ₗ[A]
        (⋀[A]^(r + s) (A ⊗[R] V)),
      IsSplitExteriorComparison (i.baseChange A) (p.baseChange A) r s θA.toLinearMap ∧
      C.middle.toLinearMap.comp (θ.toLinearMap.baseChange A) =
        θA.toLinearMap.comp C.tensor.toLinearMap := sorry

/-- Successive localization has the same normalized comparisons as direct localization.
The first equality is the exterior cocycle, the second the tensor cocycle, and the third
is the iterated scalar extension of θ under these identifications.
Source: Stacks Project, Algebra, Tags 00DK, 00DL and 0C6F; Tag 0FJB, first proof.
(blueprint: lem-trf-split-exterior-comparison-localization).

Proof: cancelBaseChange sends b tensor (a tensor m) to (b a) tensor m. On original
vectors every exterior comparison sends wedges to wedges of their final images.
The tensor comparison does the same on tensors of wedges. The direct and successive
maps therefore agree on spanning generators. Applying this to θ(x) proves the third
equality; together with splitExteriorComparison_localization this gives compatibility
of the localization equality with every second localization. No finiteness is needed
for the comparison cocycles themselves. -/
theorem splitExteriorComparison_successive_localization
    {A : Type a} {B : Type b} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (T : Submonoid R) [IsLocalization T A]
    (S : Submonoid A) [IsLocalization S B]
    (r s : ℕ)
    (C : SplitExteriorScalarComparison R A U V W r s)
    (D : SplitExteriorScalarComparison A B (A ⊗[R] U) (A ⊗[R] V) (A ⊗[R] W) r s)
    (E : SplitExteriorScalarComparison R B U V W r s)
    (θ : ((⋀[R]^r U) ⊗[R] (⋀[R]^s W)) →ₗ[R] (⋀[R]^(r + s) V)) :
    (∀ (b₀ : B) (a₀ : A) (q : ⋀[R]^(r + s) V),
      map (r + s) (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B V).toLinearMap
        (D.middle (b₀ ⊗ₜ[A] C.middle (a₀ ⊗ₜ[R] q))) =
          E.middle ((b₀ * algebraMap A B a₀) ⊗ₜ[R] q)) ∧
    (∀ (b₀ : B) (a₀ : A) (q : (⋀[R]^r U) ⊗[R] (⋀[R]^s W)),
      TensorProduct.map
        (map r (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B U).toLinearMap)
        (map s (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B W).toLinearMap)
        (D.tensor (b₀ ⊗ₜ[A] C.tensor (a₀ ⊗ₜ[R] q))) =
          E.tensor ((b₀ * algebraMap A B a₀) ⊗ₜ[R] q)) ∧
    (∀ (b₀ : B) (a₀ : A) (q : (⋀[R]^r U) ⊗[R] (⋀[R]^s W)),
      map (r + s) (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B V).toLinearMap
        (D.middle ((C.middle.toLinearMap.baseChange B)
          (((θ.baseChange A).baseChange B) (b₀ ⊗ₜ[A] (a₀ ⊗ₜ[R] q))))) =
          E.middle (θ.baseChange B ((b₀ * algebraMap A B a₀) ⊗ₜ[R] q))) := sorry

/-- With an empty kernel basis, p is an isomorphism and θ is the left unit map followed
by the exterior power of its inverse. Equality in the ambient exterior algebra avoids
a cast along 0+s=s; its homogeneous inclusion is injective.
Source: Stacks Project, Tag 0FJB, first proof, empty-wedge case.
(blueprint: lem-trf-split-exterior-comparison-localization).

Proof: an empty basis forces U=0, so exactness makes p injective and surjectivity
makes it an isomorphism. Its inverse is the unique section. The concatenation formula
on spanning wedges reduces to scalar multiplication by the empty wedge coefficient. -/
theorem splitExteriorComparison_zero_left
    (i : U →ₗ[R] V) (p : V →ₗ[R] W) (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p)
    (s : ℕ) (bU : Module.Basis (Fin 0) R U) (bW : Module.Basis (Fin s) R W)
    (θ : ((⋀[R]^0 U) ⊗[R] (⋀[R]^s W)) ≃ₗ[R] (⋀[R]^(0 + s) V))
    (hθ : IsSplitExteriorComparison i p 0 s θ.toLinearMap) :
    ∃ e : V ≃ₗ[R] W, e.toLinearMap = p ∧
      ∀ (a₀ : R) (q : ⋀[R]^s W),
        (θ (((zeroEquiv R U).symm a₀) ⊗ₜ[R] q) : ExteriorAlgebra R V) =
          a₀ • (map s e.symm.toLinearMap q : ExteriorAlgebra R V) := sorry

/-- With an empty quotient basis, θ is the right unit map followed by exteriorPower(i),
and i itself is an isomorphism. Source: Stacks Project, Tag 0FJB, empty-wedge case.
(blueprint: lem-trf-split-exterior-comparison-localization).

Proof: the empty basis gives W=0, so exactness makes i surjective; it is already
injective. In the pure-wedge formula the lift block is empty, leaving the exterior
map of i. The scalar coefficient of the empty quotient wedge gives the right unit map. -/
theorem splitExteriorComparison_zero_right
    (i : U →ₗ[R] V) (p : V →ₗ[R] W) (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p)
    (r : ℕ) (bU : Module.Basis (Fin r) R U) (bW : Module.Basis (Fin 0) R W)
    (θ : ((⋀[R]^r U) ⊗[R] (⋀[R]^0 W)) ≃ₗ[R] (⋀[R]^(r + 0) V))
    (hθ : IsSplitExteriorComparison i p r 0 θ.toLinearMap) :
    (∃ e : U ≃ₗ[R] V, e.toLinearMap = i) ∧
    ∀ (a₀ : R) (q : ⋀[R]^r U),
      (θ (q ⊗ₜ[R] (zeroEquiv R W).symm a₀) : ExteriorAlgebra R V) =
        a₀ • (map r i q : ExteriorAlgebra R V) := sorry

/-- With both bases empty, the map is multiplication R tensor R to R.
Source: Stacks Project, Tag 0FJB, first proof, empty-wedge case.
(blueprint: lem-trf-split-exterior-comparison-localization).

Proof: the two empty wedges are 1. The arbitrary-lift formula sends their tensor to 1;
linearity in the two scalar coefficients gives a b, including in the zero ring. -/
theorem splitExteriorComparison_zero_zero
    (i : U →ₗ[R] V) (p : V →ₗ[R] W)
    (θ : ((⋀[R]^0 U) ⊗[R] (⋀[R]^0 W)) ≃ₗ[R] (⋀[R]^(0 + 0) V))
    (hθ : IsSplitExteriorComparison i p 0 0 θ.toLinearMap) (a₀ b₀ : R) :
    zeroEquiv R V (θ ((zeroEquiv R U).symm a₀ ⊗ₜ[R] (zeroEquiv R W).symm b₀)) =
      a₀ * b₀ := sorry

end exteriorPower
