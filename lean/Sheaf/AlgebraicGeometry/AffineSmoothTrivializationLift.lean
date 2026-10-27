/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Ideal.Quotient.Basic
import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.AlgebraicGeometry.FirstOrderThickeningBaseChange
import WeilConjectures.AlgebraicGeometry.ThickeningAffineScheme
import Sheaf.AlgebraicGeometry.AffineFormallySmooth
import WeilConjectures.RingTheory.NakayamaNilpotent
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Lifting marked trivializations of smooth affine deformations

Source: Stacks Project, More on Morphisms, Tags 06AD, 02H0 and 02H4;
Algebra, Tags 00DV and 00HL; Examples of Deformation Problems, Tag 0DZN
(blueprint: lem-sfb-affine-smooth-trivialization-lift).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A specified trivialization modulo a nilpotent ideal of a flat deformation of a
smooth affine scheme lifts to a trivialization over the base ring. No affineness
or finite-presentation assumption on the deformation is required.

Source: Stacks Project, More on Morphisms, Tags 06AD, 02H0 and 02H4;
Algebra, Tags 00DV and 00HL; the affine lifting input behind Examples of
Deformation Problems, Tag 0DZN
(blueprint: lem-sfb-affine-smooth-trivialization-lift).

The hypothesis `hθ₀` says that the given isomorphism is over `Spec (R ⧸ I)`.
The first conclusion makes `θ` an isomorphism over `Spec R`. The second says
that its restriction has the same projection to `T` as `θ₀`. Together with
`hθ₀`, equality of the projections to `Spec (R ⧸ I)` and the pullback universal
property identify the restriction with exactly the specified `θ₀`.

Proof:
1. Write `T = Spec A`. The special fibre of `D` is affine via `θ₀` and
   `lem-weil-pbc-fibre-product-affine-spectra`. For `1 ≤ j < N`, the kernel of
   `R/I^(j+1) → R/I^j` is square zero. By
   `lem-weil-pbc-first-order-thickening-base-change` the corresponding fibres
   of `D` form first order thickenings. Apply
   `lem-weil-pbc-thickening-affine-scheme` successively to get `D = Spec C`.
2. By `lem-weil-pbc-flat-ring-map-iff-flat-affine`, `C` is flat over `R`.
   Set `J = IC` and `P = A ⊗[k] R`. The affine fibre-product and
   `lem-weil-pbc-tensor-quotient-base-change` identifications turn `θ₀` into an
   isomorphism `α₀ : A ⊗[k] (R/I) ≃ C/J` over `R/I`.
3. Smoothness implies formal smoothness. Using
   `lem-weil-pbc-affine-formally-smooth-iff-ring-lifting`, lift
   `a ↦ α₀(a ⊗ 1)` successively through `C/J^j`, whose successive kernels
   are square zero, to a map `u : A → C`. Extend scalars by the tensor
   universal property to `α : P → C`, `a ⊗ r ↦ u(a)r`. Its reduction is `α₀`.
4. Apply `lem-weil-pbc-nakayama-nilpotent` to the underlying `R`-linear map:
   surjectivity of `α₀` implies surjectivity of `α`, without finite generation.
5. Identify `(R/I) ⊗[R] M` with `M/IM` by `r ⊗ m ↦ rm` and inverse
   `m ↦ 1 ⊗ m`. Bilinearity and `1 ⊗ im = i ⊗ m = 0` prove well-definedness;
   the composites are identities on generators, naturally in `M`.
6. Put `K = ker α`. Flatness of `C` and
   `lem-weil-pbc-flat-quotient-tensor-injective` give an injection
   `K/IK → P/IP` with image the kernel of `α₀`. Thus `K/IK = 0`, so
   `K = IK = 0` by nilpotent Nakayama. Hence `α` is bijective.
7. The inverse of `α` respects ring operations and scalars by injectivity of
   `α`. Take spectra to obtain `θ`. The affine fibre-product and quotient-tensor
   formulas identify its restriction with `Spec α₀ = θ₀`, giving the stated
   projection equation. For `N = 1`, the inductions are empty and `I = 0`.
   If `T` is empty, nilpotent Nakayama gives `C = 0`. If `R = 0`, both schemes
   over `Spec R` are empty. These cases require no extra hypotheses. -/
theorem exists_affine_smooth_trivialization_lift
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (I : Ideal R) (N : ℕ) (hN : 1 ≤ N) (hI : I ^ N = ⊥)
    (T : Scheme.{u}) [IsAffine T] (t : T ⟶ Spec (CommRingCat.of k)) [Smooth t]
    (D : Scheme.{u}) (d : D ⟶ Spec (CommRingCat.of R)) [Flat d]
    (θ₀ : pullback d (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≅
      pullback t (Spec.map (CommRingCat.ofHom (algebraMap k (R ⧸ I)))))
    (hθ₀ : θ₀.hom ≫ pullback.snd t
        (Spec.map (CommRingCat.ofHom (algebraMap k (R ⧸ I)))) =
      pullback.snd d (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) :
    ∃ θ : D ≅ pullback t (Spec.map (CommRingCat.ofHom (algebraMap k R))),
      θ.hom ≫ pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap k R))) = d ∧
      pullback.fst d (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫
          θ.hom ≫ pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap k R))) =
        θ₀.hom ≫ pullback.fst t
          (Spec.map (CommRingCat.ofHom (algebraMap k (R ⧸ I)))) := by
  sorry

end AlgebraicGeometry
