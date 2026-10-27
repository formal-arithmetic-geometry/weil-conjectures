/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution
public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.LatticeAlgebraDerivedCup
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.CategoryTheory.CondensedActionTensor
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.CondensedDerivedCup

/-! # Flat twisted Koszul chain pairing for lattice algebras

Source: Stacks Project, Tag 06YQ, lemma-bounded-flat-K-flat; the explicit lattice
calculation expanding paragraph (3) of the current blueprint direct-images proof
(blueprint: lem-sfb-lattice-flat-twisted-chain-pairing).

The existing Koszul coordinates fix every differential and every sign. A chain morphism
from the signed tensor total expresses precisely the graded Leibniz identity.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace Profinite.DiscreteLattice
namespace FlatTwisted

variable {R : Profinite.CondensedRing.{u}} [IsCommMonObj R.X] {r : ℕ}

/-- Apply the recorded trivial-action functor degreewise to the original Koszul complex.
Source: direct-images paragraph (3), lattice calculation, step 3
(blueprint: lem-sfb-lattice-flat-twisted-chain-pairing). -/
abbrev trivialKoszul (K : KoszulModel R r) (B : DerivedCup.Algebra R r) :=
  ((DerivedCup.trivial R r).mapHomologicalComplex (.up ℤ)).obj (K.functor.obj B.X)

/-- The pairing is specified on each pair of finite subset summands. Its source is the
ordinary signed tensor total, so being a chain morphism is the twisted Leibniz rule.
The two unit equations are written in every homogeneous degree, using the actual
single-complex coordinate rather than an arbitrary unit identification.
Source: direct-images paragraph (3), lattice calculation, steps 4--6
(blueprint: lem-sfb-lattice-flat-twisted-chain-pairing). -/
structure Pairing (K : KoszulModel R r) (B : DerivedCup.Algebra R r) where
  /-- The internal R-bilinear chain multiplication. -/
  star : K.functor.obj B.X ⊗ K.functor.obj B.X ⟶ K.functor.obj B.X
  /-- The coefficient of every ordered disjoint partition, with exactly its twist and sign. -/
  coordinates : ∀ (p q : ℤ) (A : Subsets r p) (C : Subsets r q)
    (I : Subsets r (p + q)),
    ((biproduct.ι _ A ≫ (K.coordinates B.X p).inv) ⊗ₘ
        (biproduct.ι _ C ≫ (K.coordinates B.X q).inv)) ≫
      HomologicalComplex.ιTensorObj _ _ p q (p + q) rfl ≫ star.f (p + q) ≫
        (K.coordinates B.X (p + q)).hom ≫ biproduct.π _ I =
    if Disjoint A.val C.val ∧ A.val ∪ C.val = I.val then
      ((-1 : ℤ) ^ ((A.val.product C.val).filter (fun ac ↦ ac.2 < ac.1)).card) •
        ((𝟙 B.X.V ⊗ₘ B.X.ρ (∏ i ∈ A.val, generator i)) ≫
          (MonObj.mul (X := B.X)).hom)
    else 0
  /-- The algebra unit, as a chain morphism from R[0]. -/
  unit : (HomologicalComplex.single (Modules R) (.up ℤ) 0).obj (𝟙_ (Modules R)) ⟶
    K.functor.obj B.X
  /-- In degree zero this is the original algebra unit 1_B. -/
  unitCoordinates : ∀ I : Subsets r 0,
    unit.f 0 ≫ (K.coordinates B.X 0).hom ≫ biproduct.π _ I =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (Modules R))).hom ≫
        (MonObj.one (X := B.X)).hom
  /-- Multiplying on the left by the unit is the identity, in every degree. -/
  leftUnit : ∀ p : ℤ,
    (unit.f 0 ⊗ₘ 𝟙 ((K.functor.obj B.X).X p)) ≫
      HomologicalComplex.ιTensorObj _ _ 0 p p (zero_add p) ≫ star.f p =
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (Modules R))).hom ⊗ₘ
      𝟙 ((K.functor.obj B.X).X p)) ≫ (λ_ ((K.functor.obj B.X).X p)).hom
  /-- Multiplying on the right by the unit is the identity, in every degree. -/
  rightUnit : ∀ p : ℤ,
    (𝟙 ((K.functor.obj B.X).X p) ⊗ₘ unit.f 0) ≫
      HomologicalComplex.ιTensorObj _ _ p 0 p (add_zero p) ≫ star.f p =
    (𝟙 ((K.functor.obj B.X).X p) ⊗ₘ
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (Modules R))).hom) ≫
        (ρ_ ((K.functor.obj B.X).X p)).hom

/-- Flat lattice algebras have bounded flat-term K-flat Koszul complexes, with the
specified twisted chain pairing and two-sided unit. Ordinary total tensors of these
complexes and their units compute the canonical ordinary derived tensors.
Source: Stacks Tag 06YQ, lemma-bounded-flat-K-flat, and the explicit lattice calculation
below paragraph (3) of the current blueprint direct-images proof
(blueprint: lem-sfb-lattice-flat-twisted-chain-pairing).

Proof, following all seven DAG steps:
1. Use the internal/section-module equivalence and the balanced sheaf tensor. Every
Koszul term is a finite direct sum of B, or zero outside [0,r]. Its tensor functor is
therefore a finite direct sum of the exact functor B tensor -, giving flat terms.
2. Apply bounded-above-flat K-flatness on the coherent profinite ringed site (Tag 06YQ).
This gives acyclic total tensor with every acyclic complex, including unbounded ones.
3. Forgetting the action is exact, detects exactness and has the canonical diagonal
strong tensor comparison. It identifies the underlying total of tK tensor A with
K tensor UA. The sums are finite in each degree. Hence tK is bounded, flat-term and
K-flat as well, without assuming that forgetting preserves injectives.
4. The balanced maps x tensor y maps to x T_A(y) are natural on the site. Sum them
with the inversion signs over the disjoint subset partitions to obtain star.
5. For J=A disjoint-union C disjoint-union {i}, write N for the inversion count,
a for the number of elements of A below i, and c for that number in C. The three
Leibniz signs have exponents N+a+c, (N+c)+a and p+N+(p-a)+c, equal modulo two.
The values (T_i x-x) T_A T_i y and x T_A(T_i y-y) add to
(T_i-1)(x T_A y). Summing proves the chain-map identity with the signed total.
6. Each T_i fixes 1_B, so the degree-zero algebra unit is closed. The partitions
A=empty and C=empty give its two unit laws. For r=0 these are ordinary multiplication
and unit on B[0]. The zero ring, zero algebra and characteristic two obey the same
integral formulas, with no division or nonvanishing assumption.
7. The canonical K-flat derived tensor comparison is invertible on these flat-term
K-flat representatives, both in modules and in the action category. The regular unit
complex is itself flat and K-flat since tensoring with it is the identity. Thus all
displayed ordinary-to-derived tensor comparisons, including those with units, invert. -/
theorem lattice_flat_twisted_chain_pairing
    (K : KoszulModel R r) (B : DerivedCup.Algebra R r) [IsCommMonObj B.X]
    (hflat : exactFunctor (Modules R) (Modules R) (tensorLeft B.X.V)) :
    (∀ a : ℤ, ObjectProperty.flat ((K.functor.obj B.X).X a)) ∧
    (∀ a : ℤ, a < 0 ∨ (r : ℤ) < a → IsZero ((K.functor.obj B.X).X a)) ∧
    (∀ A : CochainComplex (Modules R) ℤ,
      A.Acyclic → (K.functor.obj B.X ⊗ A).Acyclic) ∧
    (∀ a : ℤ, ObjectProperty.flat ((trivialKoszul K B).X a)) ∧
    (∀ a : ℤ, a < 0 ∨ (r : ℤ) < a → IsZero ((trivialKoszul K B).X a)) ∧
    (∀ A : CochainComplex (Equivariant R r) ℤ,
      A.Acyclic → (trivialKoszul K B ⊗ A).Acyclic) ∧
    Nonempty (Pairing K B) ∧
    (∀ P Q : CochainComplex (Modules R) ℤ,
      (P = K.functor.obj B.X ∨
        P = (HomologicalComplex.single (Modules R) (.up ℤ) 0).obj (𝟙_ (Modules R))) →
      (Q = K.functor.obj B.X ∨
        Q = (HomologicalComplex.single (Modules R) (.up ℤ) 0).obj (𝟙_ (Modules R))) →
      IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q.{u + 2} P Q)) ∧
    (∀ P Q : CochainComplex (Equivariant R r) ℤ,
      (P = trivialKoszul K B ∨
        P = ((DerivedCup.trivial R r).mapHomologicalComplex (.up ℤ)).obj
          ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj (𝟙_ (Modules R)))) →
      (Q = trivialKoszul K B ∨
        Q = ((DerivedCup.trivial R r).mapHomologicalComplex (.up ℤ)).obj
          ((HomologicalComplex.single (Modules R) (.up ℤ) 0).obj (𝟙_ (Modules R)))) →
      IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q.{u + 2} P Q)) := by
  sorry

end FlatTwisted
end Profinite.DiscreteLattice
