/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

/-!
# The one-term Tor-acyclic tensor comparison

Source: Stacks Project, Tag 08IB, final affine calculation; More on Algebra,
Section 15.60 (Tag 06XY), independence of K-flat resolutions.
(blueprint: lem-pc-single-support-tor-acyclic-tensor).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex

namespace CochainComplex

/-- For a complex supported in one degree, positive Tor vanishing suffices for
any K-flat resolution to compute its ordinary tensor product.

Source: Stacks Project, Tag 08IB, final affine Tor calculation, and Tag 06XY,
Lemmas 15.60.7 and 15.60.12. The following fills in the one-term calculation
of the parent node; it is not an assertion of the entire bounded-complex result.
(blueprint: lem-pc-single-support-tor-acyclic-tensor).

Proof:
1. The support hypothesis identifies Q with the single complex on Q.X k in
   degree k, using the identity in degree k and the unique maps between zero
   objects in the other degrees. All its differentials are zero.
2. Take a projective resolution of Q.X k, reindex it in cochain degrees k-i,
   and augment it to Q. Its terms are flat and it is bounded above, hence K-flat
   by the bounded-flat K-flat lemma. After tensoring with B its cohomology in
   degree k-i is Tor_i(Q.X k,B). Its degree-k augmentation is an isomorphism by
   right exactness of tensor and the Tor-zero comparison. In degrees above k
   both complexes are zero. Thus its tensor augmentation is a quasi-isomorphism.
3. This calculation applies to the given f, not just the projective resolution:
   choose a common K-flat refinement of the two resolutions in the homotopy
   category. The transition quasi-isomorphisms remain quasi-isomorphisms after
   tensoring with B (Tag 06XY, Lemma 15.60.12); their augmentation square commutes
   up to homotopy. Tensor preserves that homotopy, so two-out-of-three gives the
   result for f. This also covers Q=0 and an unbounded K-flat source P. -/
theorem quasiIso_tensor_of_single_support_tor_acyclic
    {R : Type u} [CommRing R] {B : Type u} [CommRing B] [Algebra R B]
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) (k : ℤ)
    (hsupport : ∀ n : ℤ, n ≠ k → IsZero (Q.X n))
    (hTor : ∀ i : ℕ, 0 < i →
      IsZero (((Tor' (ModuleCat.{u} R) i).obj (Q.X k)).obj (ModuleCat.of R B)))
    (P : CochainComplex.KFlat (ModuleCat.{u} R)) (f : P.obj ⟶ Q)
    (hf : QuasiIso f) :
    QuasiIso ((((tensoringRight (ModuleCat.{u} R)).obj (ModuleCat.of R B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f) := by sorry

end CochainComplex
