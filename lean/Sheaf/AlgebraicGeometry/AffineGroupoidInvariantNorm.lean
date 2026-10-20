/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.AlgebraicGeometry.SchemeGroupoidLaws
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeNormCharts
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Invariance of the source norm of a target pullback

Source: Stacks Project, Groupoid Schemes, Tag 03BH, `lemma-determinant-trick`,
and Divisors, Tag 0BD2, `lemma-finite-locally-free-has-norm`
(blueprint: lem-a1-affine-groupoid-invariant-norm).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The source norm of a target pullback belongs to the invariant subring.
Source: Stacks Project, Tag 03BH, `lemma-determinant-trick`, with the norm of
Tag 0BD2 (blueprint: lem-a1-affine-groupoid-invariant-norm).

Here `n` is the norm section, specified by exactly the local finite-free determinant
charts of `exists_finiteLocallyFree_norm_charts` for `W = ⊤` and the section corresponding
to `t`-sharp of `f`. The hypothesis `hn` characterizes that section, rather than assuming
that the source algebra is globally free. `Scheme.ΓSpecIso` identifies coordinate-ring
elements with global sections; `Spec.preimage` gives the source and target ring maps.

Proof:
1. Put `P = pullback s t`, with projections `p₀`, `p₁`. The groupoid laws give
   `c ≫ s = p₁ ≫ s` and `c ≫ t = p₀ ≫ t`. Besides the defining pullback square
   with top `p₀` and bottom `t`, the square with top `c` and bottom `s` is a pullback.
   Indeed `(a,b) ↦ (c(a,b),b)` is an isomorphism from `P` to `pullback s s`, with
   inverse `(h,b) ↦ (c(h,i(b)),b)`. Associativity, the inverse laws and the identity
   laws show both composites are identities; the pullback universal property makes
   these morphisms. Thus `p₁` is a base change of `s` in two ways. For `a = t♯(f)`,
   the target-composition law says `c♯(a) = p₀♯(a)`.
2. Use the charts in `hn`, as supplied by `lem-pd-finite-locally-free-norm-charts`.
   Refine intersections of their source and target inverse images to affine opens `W`
   of `Spec B`. The two pullback squares identify the section algebra over `p₁⁻¹(W)`
   with the scalar extensions of the two chart algebras; these are the tensor-product
   identifications of `lem-weil-pbc-fibre-product-affine-spectra`. A basis of either
   chart algebra pulls back to a basis, and its multiplication matrix is obtained by
   applying the base ring map entrywise. The Leibniz determinant formula
   (`def-weil-pbc-matrix-determinant`) then identifies the restrictions of `s♯(n)`
   and `t♯(n)` with the determinants of multiplication by `c♯(a)` and `p₀♯(a)` on
   the same algebra.
3. These endomorphisms agree by step 1. Their determinants agree in any bases by
   `def-weil-endomorphism-determinant`. Equality on the affine cover of `Spec B`
   gives equality of global sections by the structure-sheaf equality axiom
   (`def-pc-scheme`). Hence `s♯(n) = t♯(n)`, exactly membership in `RingHom.eqLocus`.
   The calculation is local on finite-free charts, permits varying ranks and
   nilpotents, and uses determinant `1` on rank-zero charts. -/
theorem affineGroupoid_invariant_norm
    (A B : CommRingCat.{u}) (s t : Spec B ⟶ Spec A) (e : Spec A ⟶ Spec B)
    (i : Spec B ⟶ Spec B) (c : pullback s t ⟶ Spec B)
    (hG : Scheme.IsGroupoid s t e i c) [s.IsFiniteLocallyFree] [t.IsFiniteLocallyFree]
    (f n : A)
    (hn : ∀ x : Spec A, ∃ V : (Spec A).Opens, x ∈ V ∧ IsAffineOpen V ∧
      (letI := (s.app V).hom.toAlgebra
       Module.Free Γ(Spec A, V) Γ(Spec B, s ⁻¹ᵁ V) ∧
       Module.Finite Γ(Spec A, V) Γ(Spec B, s ⁻¹ᵁ V) ∧
       (Spec A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
           ((Scheme.ΓSpecIso A).inv n) =
         Algebra.norm Γ(Spec A, V)
           ((Spec B).presheaf.map (homOfLE (le_top : s ⁻¹ᵁ V ≤ ⊤)).op
             ((Scheme.ΓSpecIso B).inv ((Spec.preimage t).hom f))))) :
    n ∈ RingHom.eqLocus (Spec.preimage s).hom (Spec.preimage t).hom := by
  sorry

end AlgebraicGeometry
