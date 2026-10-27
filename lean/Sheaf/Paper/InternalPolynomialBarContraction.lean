/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q113
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.Paper.RationalPolynomialBarContraction
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify

import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-! # Internal extension of the rational polynomial bar contraction

Source: latest blueprint, six-functors basics, direct-images proof, paragraph (3),
agent polynomial-bar reduction of the trivial lattice case, internal finite-matrix step
(blueprint: lem-sfb-internal-polynomial-bar-contraction).

The models below are specified by their coproduct universal properties and by formulas
on every injection. They are unique up to the specified coproduct identifications.
No identification of sections of an internal coproduct with sectionwise direct sums is used.
The rational differential, ordered inclusion and signed projection are the recorded ones.
- Potential homotopies are quantified universally, not chosen from a bare existence result.
- All finite columns are actual finitely supported functions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite Profinite.CondensedAction
open scoped BigOperators

namespace InternalPolynomialBar

/-- Extend one finite rational column on coproduct injections, using scalar endomorphisms
of the regular internal module. This is a finite sum of actual internal module morphisms.
Source: internal finite-matrix extension, proof step 3, below latest blueprint direct-images
paragraph (3) (blueprint: lem-sfb-internal-polynomial-bar-contraction). -/
def finiteColumn (A : Profinite.CondensedRing.{u}) [IsCommMonObj A.X]
    {J : Type v} {N : Modules A} (s : ℚ → End (Mod.regular A.X))
    (ι : J → (Mod.regular A.X ⟶ N)) (c : J →₀ ℚ) : Mod.regular A.X ⟶ N :=
  c.sum fun j t ↦ s t ≫ ι j

/-- Every rational contraction extends internally by its finite monomial columns.

Source: agent polynomial-bar reduction, internal finite-matrix extension, below latest
blueprint direct-images paragraph (3)
(blueprint: lem-sfb-internal-polynomial-bar-contraction).

Proof (the five steps of the node):
1. Use the small-site size convention and condensed-module Grothendieck infrastructure
   to form the coproducts indexed by all monomials and by subsets of fixed cardinality.
   Their universal properties, `def-weil-pbc-category-colimit`, detect equality on injections.
2. Restrict each rational global section along S -> *. Multiplication by this section
   commutes with every restriction and with the regular A-action, since A is commutative.
   This gives s, with addition, multiplication and unit inherited from the given ring map.
3. For p and h use `finiteColumn` on the columns of the rational maps of
   `lem-sfb-rational-polynomial-bar-contraction`. Do the same for d and i; substitution
   expands each monomial finitely, and the ordered inclusion has a single coefficient 1.
   This constructs the specified maps without a sectionwise-coproduct assertion.
4. Finite double sums show extension preserves sums, compositions and identities.
   Extend the rational identities to obtain d²=0, di=0, pd=0, pi=1 and dh+hd=1-ip,
   including the separate degree-zero homotopy identity. Define the complexes from d²=0.
5. Extend the complexes and maps by zero to integer degrees. The displayed homotopy
   gives the homotopy equivalence with the prescribed maps. Localization from
   `def-weil-abstract-derived-category` sends these maps to inverse isomorphisms.
   For the zero ring all regular modules and coproducts are zero. When r=0 the exterior
   terms in positive degree vanish, and the polynomial constant differential alternates
   between zero in even degrees and identity in odd degrees. For n>r the exterior
   index is empty. Every column is finite; neither flatness nor completeness is used.
-/
theorem contraction (A : Profinite.CondensedRing.{u}) [IsCommMonObj A.X]
    (φ : ℚ →+* (InternalAbelianSheafModule.sectionRings
      (coherentTopology Profinite.{u}) A.X).obj (op (⊤_ Profinite.{u})))
    (r : ℕ)
    (h : ∀ n : ℕ, RationalPolynomialBar.P ℚ r (n + 1) →ₗ[ℚ]
      RationalPolynomialBar.P ℚ r n)
    (hzero : (h 0).comp (RationalPolynomialBar.differential ℚ r 0) =
      LinearMap.id - (RationalPolynomialBar.inclusion ℚ r 0).comp
        (RationalPolynomialBar.projection ℚ r 0))
    (hsucc : ∀ n : ℕ,
      (RationalPolynomialBar.differential ℚ r n).comp (h n) +
        (h (n + 1)).comp (RationalPolynomialBar.differential ℚ r (n + 1)) =
          LinearMap.id - (RationalPolynomialBar.inclusion ℚ r (n + 1)).comp
            (RationalPolynomialBar.projection ℚ r (n + 1))) :
    ∃ (s : ℚ → End (Mod.regular A.X))
      (P K : CochainComplex (Modules A) ℕ)
      (ι : ∀ n : ℕ, ((Fin n × Fin r) →₀ ℕ) → (Mod.regular A.X ⟶ P.X n))
      (κ : ∀ n : ℕ, RationalPolynomialBar.ExteriorIndex r n →
        (Mod.regular A.X ⟶ K.X n))
      (i : K ⟶ P) (p : P ⟶ K) (H : ∀ n : ℕ, P.X (n + 1) ⟶ P.X n),
      (∀ (c : ℚ) (S : Profinite.{u})
        (a : (InternalAbelianSheafModule.sectionRings
          (coherentTopology Profinite.{u}) A.X).obj (op S)),
        ((s c).hom.hom.app (op S)).hom a =
          ((InternalAbelianSheafModule.sectionRings
            (coherentTopology Profinite.{u}) A.X).map (terminal.from S).op).hom (φ c) * a) ∧
      (∀ n : ℕ, Nonempty (IsColimit (Cofan.mk (P.X n) (ι n)))) ∧
      (∀ n : ℕ, Nonempty (IsColimit (Cofan.mk (K.X n) (κ n)))) ∧
      (∀ n : ℕ, K.d n (n + 1) = 0) ∧
      (∀ (n : ℕ) (m : (Fin n × Fin r) →₀ ℕ),
        ι n m ≫ P.d n (n + 1) = finiteColumn A s (ι (n + 1))
          (AddMonoidAlgebra.coeff
            (RationalPolynomialBar.differential ℚ r n (MvPolynomial.monomial m 1)))) ∧
      (∀ (n : ℕ) (I : RationalPolynomialBar.ExteriorIndex r n),
        κ n I ≫ i.f n = finiteColumn A s (ι n)
          (AddMonoidAlgebra.coeff
            (RationalPolynomialBar.inclusion ℚ r n (Finsupp.single I 1)))) ∧
      (∀ (n : ℕ) (m : (Fin n × Fin r) →₀ ℕ),
        ι n m ≫ p.f n = finiteColumn A s (κ n)
          (RationalPolynomialBar.projection ℚ r n (MvPolynomial.monomial m 1))) ∧
      (∀ (n : ℕ) (m : (Fin (n + 1) × Fin r) →₀ ℕ),
        ι (n + 1) m ≫ H n = finiteColumn A s (ι n)
          (AddMonoidAlgebra.coeff (h n (MvPolynomial.monomial m 1)))) ∧
      (∀ n : ℕ, i.f n ≫ P.d n (n + 1) = 0) ∧
      (∀ n : ℕ, P.d n (n + 1) ≫ p.f (n + 1) = 0) ∧
      i ≫ p = 𝟙 K ∧
      P.d 0 1 ≫ H 0 = 𝟙 (P.X 0) - p.f 0 ≫ i.f 0 ∧
      (∀ n : ℕ, H n ≫ P.d n (n + 1) + P.d (n + 1) (n + 2) ≫ H (n + 1) =
        𝟙 (P.X (n + 1)) - p.f (n + 1) ≫ i.f (n + 1)) ∧
      (∃ e : HomotopyEquiv (K.extend ComplexShape.embeddingUpNat)
          (P.extend ComplexShape.embeddingUpNat),
        e.hom = HomologicalComplex.extendMap i ComplexShape.embeddingUpNat ∧
        e.inv = HomologicalComplex.extendMap p ComplexShape.embeddingUpNat) ∧
      (∀ [HasDerivedCategory.{u + 2} (Modules A)],
        ∃ e : (DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat)) ≅
            (DerivedCategory.Q.obj (P.extend ComplexShape.embeddingUpNat)),
          e.hom = DerivedCategory.Q.map
            (HomologicalComplex.extendMap i ComplexShape.embeddingUpNat) ∧
          e.inv = DerivedCategory.Q.map
            (HomologicalComplex.extendMap p ComplexShape.embeddingUpNat)) := by
  sorry

end InternalPolynomialBar
