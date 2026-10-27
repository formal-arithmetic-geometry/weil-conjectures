/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q108
-/
module

public import Sheaf.AlgebraicGeometry.AffinePGLAction
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Adjoin.Tower

/-!
# Power lifting and finite generation for PGL invariants

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
§§9.1–9.2, Theorems 9.7.5–9.7.6 and 6.3.3
(blueprint: lem-sfb-pgl-geometric-reductivity).

The three statements give finite generation, positive-power lifting, and its
homogeneous refinement. No restriction on the characteristic is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.AffinePGL

variable {k : Type u} [Field k] {r : ℕ}
variable {E : Type u} [CommRing E] [Algebra k E]
variable {F : Type u} [CommRing F] [Algebra k F]

/-- Equivariance is the commutation of Spec f with the actions on all T-points.
The premise identifies x with Spec f composed with y, so no choice of a lift or
of an over-category morphism is involved. Source: Alper §9.2, Lemma 9.2.5(3)
(blueprint: lem-sfb-pgl-geometric-reductivity). -/
def Action.IsEquivariant (D : Action k E r) (D' : Action k F r) (f : E →ₐ[k] F) : Prop :=
  ∀ (T : Over (Spec (.of k))) (g : PGLLinearization.Matrices k r T)
    (x : T ⟶ affineOver k E) (y : T ⟶ affineOver k F),
    y.left ≫ Spec.map (CommRingCat.ofHom f.toRingHom) = x.left →
      (D'.act T g y).left ≫ Spec.map (CommRingCat.ofHom f.toRingHom) =
        (D.act T g x).left

/-- The graph of the canonical grading G_m action on T-points: a homogeneous
coordinate of degree n is multiplied by a^n. The direct-sum decomposition makes
the translated point unique and defines it on every coordinate by a finite sum.
All test schemes and units of their global sections are included. Source: the
graded refinement of Alper Lemma 9.2.5(3)
(blueprint: lem-sfb-pgl-geometric-reductivity). -/
def IsGradingTranslate (𝒜 : ℕ → Submodule k E) [GradedAlgebra 𝒜]
    (T : Over (Spec (.of k))) (a : Γ(T.left, ⊤)ˣ)
    (x y : T ⟶ affineOver k E) : Prop :=
  ∀ (n : ℕ) (e : E), e ∈ 𝒜 n →
    evaluation y e = (a : Γ(T.left, ⊤)) ^ n * evaluation x e

/-- Degree preservation means commuting with the canonical grading G_m action,
expressed using its graph on all scheme-valued points. This tests universal
units, not only k-points, so detects degrees over finite fields and nilpotents.
Source: the graded refinement of Alper Lemma 9.2.5(3)
(blueprint: lem-sfb-pgl-geometric-reductivity). -/
def Action.PreservesDegrees (D : Action k E r) (𝒜 : ℕ → Submodule k E)
    [GradedAlgebra 𝒜] : Prop :=
  ∀ (T : Over (Spec (.of k))) (g : PGLLinearization.Matrices k r T)
    (a : Γ(T.left, ⊤)ˣ) (x y : T ⟶ affineOver k E),
    IsGradingTranslate 𝒜 T a x y →
      IsGradingTranslate 𝒜 T a (D.act T g x) (D.act T g y)

/-- Finite generation of the invariant algebra. Source: Alper Theorems 9.7.5–9.7.6
and 6.3.3 (blueprint: lem-sfb-pgl-geometric-reductivity).

Proof plan, following the node's twelve steps:
1. PGL is reductive, including r = 1 (lem-sfb-pgl-reductive-structure), so Haboush
   gives invariant symmetric powers (lem-sfb-haboush-symmetric-power-lift).
2. For a surjection D → D' and invariant b, use the finite subrepresentation of
   the inverse image of kb (lem-sfb-comodule-finite-subrepresentation). The map
   V → kb gives an equivariant surjection to k; multiply its invariant symmetric
   power to lift b^N. For b = 0 use a = 0, N = 1. Tensor exactness over the field
   justifies kernels (lem-weil-pbc-module-over-field-flat and
   lem-weil-pbc-flat-tensor-exact).
3. In the graded case project to degree Nd to obtain a homogeneous invariant lift.
4. Simultaneously induct on stable ideals: D^G is of finite type and invariants
   of finite equivariant D-modules are finite. Noetherianity and maximal conditions
   come from lem-wf-affine-noetherian-components and
   lem-weil-pbc-noetherian-finite-module-acc. Invariants preserve kernels.
5. Power lifting makes (D/I)^G integral over the image of D^G. Finite algebra
   generators give module finiteness (lem-sc-finite-generated-integral-subring);
   Artin–Tate makes that image of finite type
   (lem-sfb-artin-tate-subalgebra-finite-type).
6. For nonzero stable I,J with IJ = 0, apply induction to D/I,D/J. Choose a finite
   type subalgebra B of D^G surjecting onto both image rings. I^G and (D/I)^G are
   finite over B, so kernel/image generators make D^G finite over B. Submodule
   finiteness uses lem-weil-pbc-noetherian-submodule-finite.
7. Apply the same kernel/image argument to IM and M/IM to finish the finite
   module assertion in this two-ideal case.
8. A nonzero invariant zero divisor f yields I = fD and J = Ann(f), reducing to
   steps 6–7. Otherwise every nonzero invariant is regular. Invariant units have
   invariant inverses, and tensor exactness gives D^G ∩ fD = fD^G.
9. For each proper nonzero ideal K of D^G choose nonzero f in K. Induction and
   step 5 make D^G/fD^G of finite type. Lift generators of K/fD^G and add f.
   Thus every ideal of D^G is finite and D^G is Noetherian.
10. Power lifting makes Spec D → Spec D^G universally submersive
    (lem-sfb-power-lifting-quotient-submersive). Apply the Noetherian subring
    criterion (lem-sfb-noetherian-subring-finite-type-submersion).
11. For the remaining module assertion induct on equivariant quotients of M.
    A nonzero invariant s gives Ds = D/Ann(s); its invariants are finite by the
    algebra induction and step 5, or are D^G if Ann(s) = 0. The quotient M/Ds and
    kernel/image generators finish the induction.
12. Apply finite generation to E; steps 2–3 give the other two declarations.
No averaging, reducedness or characteristic hypothesis is used. -/
theorem invariants_finiteType (_hr : 1 ≤ r) [Algebra.FiniteType k E]
    (D : Action k E r) :
    letI := D.constants.toAlgebra
    Algebra.FiniteType k D.invariants := by
  sorry

/-- Positive powers of invariant elements lift along surjective equivariant maps.
Source: Alper Lemma 9.2.5(3) and Theorems 9.7.5–9.7.6
(blueprint: lem-sfb-pgl-geometric-reductivity).
Proof: steps 1–2 of the node. For b = 0 take N = 1 and a = 0. Otherwise take a
finite rational submodule of the inverse image of kb containing a lift of b.
Its equivariant surjection to k admits an invariant symmetric-power lift by
Haboush; multiplication gives a with image b^N. Flatness over k preserves the
kernels used to form the submodule. -/
theorem exists_invariant_power_lift (_hr : 1 ≤ r)
    [Algebra.FiniteType k E] [Algebra.FiniteType k F]
    (D : Action k E r) (D' : Action k F r) (f : E →ₐ[k] F)
    (hf : Function.Surjective f) (heq : D.IsEquivariant D' f)
    (b : F) (hb : b ∈ D'.invariants) :
    ∃ (N : ℕ) (_ : 0 < N) (a : E), a ∈ D.invariants ∧ f a = b ^ N := by
  sorry

/-- The power lift can be chosen homogeneous of degree Nd. Source: the graded
refinement of Alper Lemma 9.2.5(3)
(blueprint: lem-sfb-pgl-geometric-reductivity).
Proof: step 3 of the node. Apply the preceding power-lifting statement and
project its lift to degree Nd. Degree preservation of the coaction makes every
homogeneous component invariant. Since f is graded and b^N has degree Nd, this
component still maps to b^N. This includes degree zero and b = 0. -/
theorem exists_homogeneous_invariant_power_lift (_hr : 1 ≤ r)
    [Algebra.FiniteType k E] [Algebra.FiniteType k F]
    (D : Action k E r) (D' : Action k F r) (f : E →ₐ[k] F)
    (hf : Function.Surjective f) (heq : D.IsEquivariant D' f)
    (𝒜 : ℕ → Submodule k E) (ℬ : ℕ → Submodule k F)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (hD : D.PreservesDegrees 𝒜) (hD' : D'.PreservesDegrees ℬ)
    (hgraded : ∀ (n : ℕ) (a : E), a ∈ 𝒜 n → f a ∈ ℬ n)
    (d : ℕ) (b : F) (hb : b ∈ D'.invariants) (hbd : b ∈ ℬ d) :
    ∃ (N : ℕ) (_ : 0 < N) (a : E),
      a ∈ D.invariants ∧ a ∈ 𝒜 (N * d) ∧ f a = b ^ N := by
  sorry

end AlgebraicGeometry.AffinePGL
