/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.RingTheory.DerivedCompleteModuleComplex
public import Sheaf.Algebra.Homology.DerivedChangeOfRings
import Sheaf.RingTheory.RingPseudoCoherent
import Sheaf.Algebra.Homology.KFlatTelescopeClosure

/-!
# Perfect inverse-limit reconstruction over a complete ring

Source: Stacks Project, More on Algebra, Tag 09AW, lemma-Rlim-perfect-gives-complete
(blueprint: lem-weil-pbc-rlim-perfect-complete).

The index `n : ℕ` denotes level `n + 1`. Derived scalar extension is specified by its
universal property as the left adjoint to exact restriction of scalars. We allow any
realization of this adjunction; all maps below are its adjoint transposes, so no arbitrary
comparison map is supplied. The derived limit includes its Roos triangle and projections.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Exact restriction from the `(n+1)`st quotient to the complete ring.
Source: Stacks Project, Tag 09AW
(blueprint: lem-weil-pbc-rlim-perfect-complete). -/
noncomputable def adicLevelRestriction {A : Type u} [CommRing A] (I : Ideal A)
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [∀ n : ℕ, HasDerivedCategory.{u} (ModuleCat.{u} (A ⧸ I ^ (n + 1)))] (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))) ⥤
      DerivedCategory (ModuleCat.{u} A) :=
  (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1)))).mapDerivedCategory

/-- Exact restriction between consecutive quotient rings.
Source: Stacks Project, Tag 09AW
(blueprint: lem-weil-pbc-rlim-perfect-complete). -/
noncomputable def adicStepRestriction {A : Type u} [CommRing A] (I : Ideal A)
    [∀ n : ℕ, HasDerivedCategory.{u} (ModuleCat.{u} (A ⧸ I ^ (n + 1)))] (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))) ⥤
      DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1 + 1))) :=
  (ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc I (n + 1))).mapDerivedCategory

/-- The canonical identification of iterated restriction with direct restriction.
Source: Stacks Project, Tag 09AW; both underived maps send every element to itself.
(blueprint: lem-weil-pbc-rlim-perfect-complete). -/
noncomputable def adicRestrictionComp {A : Type u} [CommRing A] (I : Ideal A)
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [∀ n : ℕ, HasDerivedCategory.{u} (ModuleCat.{u} (A ⧸ I ^ (n + 1)))] (n : ℕ) :
    adicLevelRestriction I n ≅ adicStepRestriction I n ⋙ adicLevelRestriction I (n + 1) :=
  Functor.mapDerivedCategoryNatIso
    (ModuleCat.restrictScalarsComp'
      (Ideal.Quotient.mk (I ^ (n + 1 + 1)))
      (Ideal.Quotient.factorPowSucc I (n + 1))
      (Ideal.Quotient.mk (I ^ (n + 1)))
      (Ideal.Quotient.factor_comp_mk (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).symm) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Restrict a supplied transition in `D(A/I^(n+2))` to `D(A)`.
Source: Stacks Project, Tag 09AW
(blueprint: lem-weil-pbc-rlim-perfect-complete). -/
noncomputable def adicTowerTransition {A : Type u} [CommRing A] (I : Ideal A)
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [∀ n : ℕ, HasDerivedCategory.{u} (ModuleCat.{u} (A ⧸ I ^ (n + 1)))]
    (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))))
    (t : ∀ n : ℕ, K (n + 1) ⟶ (adicStepRestriction I n).obj (K n)) (n : ℕ) :
    (adicLevelRestriction I (n + 1)).obj (K (n + 1)) ⟶
      (adicLevelRestriction I n).obj (K n) :=
  (adicLevelRestriction I (n + 1)).map (t n) ≫ (adicRestrictionComp I n).inv.app (K n)

/-- The canonical reduction map: transpose the projection of the specified Roos triangle.
Source: Stacks Project, Tag 09AW
(blueprint: lem-weil-pbc-rlim-perfect-complete). -/
noncomputable def adicLimitReduction {A : Type u} [CommRing A] (I : Ideal A)
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [∀ n : ℕ, HasDerivedCategory.{u} (ModuleCat.{u} (A ⧸ I ^ (n + 1)))]
    (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))))
    [HasProduct (fun n : ℕ ↦ (adicLevelRestriction I n).obj (K n))]
    (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))))
    (adj : ∀ n : ℕ, L n ⊣ adicLevelRestriction I n)
    (C : DerivedCategory (ModuleCat.{u} A))
    (p : C ⟶ ∏ᶜ (fun n : ℕ ↦ (adicLevelRestriction I n).obj (K n))) (n : ℕ) :
    (L n).obj C ⟶ K n :=
  ((adj n).homEquiv C (K n)).symm (p ≫ Pi.π _ n)

/-- Perfect compatible reductions reconstruct a perfect, derived complete object, and its
projection-induced reductions are isomorphisms compatible with the transition maps.
Source: Stacks Project, More on Algebra, Tag 09AW
(blueprint: lem-weil-pbc-rlim-perfect-complete).

Proof:
1. Represent `K 0` by a bounded finite-projective complex. Successively add contractible
   two-term complements, starting at the top degree, to make a bounded-above finite-free
   representative. Each degree changes only twice, so the contracting homotopies assemble.
   Thus `K 0` is pseudo-coherent (`def-pc-ring-pseudo-coherent-complex`).
2. The quotient transitions are surjective with square-zero kernels. Completeness identifies
   their inverse limit with `A`. Apply `lem-weil-pbc-pseudocoherent-inverse-ring-reconstruction`
   to obtain compatible finite-free models and a bounded-above finite-free limit model,
   with projection-induced reduction isomorphisms. In particular the limit is pseudo-coherent.
3. Every maximal ideal contains `I` by `lem-weil-pbc-adic-complete-jacobson-radical`.
   Tensor the finite-free models with each residue field. K-flatness
   (`lem-pc-kflat-closure`) and derived change of rings (`lem-pur-derived-change-of-rings`)
   identify this with tensoring the bounded finite-projective model of `K 0`. Its fixed
   interval bounds all these residue-field cohomologies uniformly.
4. Apply `lem-weil-pbc-pseudocoherent-maximal-fibre-perfect` to conclude perfectness.
5. For `f ∈ I`, multiplication by `f^(n+1)` on the restricted `K n` is zero. Apply
   `lem-weil-pbc-nilpotent-torsion-derived-limit-complete` to obtain derived completeness
   in the vanishing sense of `def-weil-point-derived-complete-module-complex`.
6. Projections of the strict inverse-limit model commute with every transition. The
   reduction maps send `x ⊗ a` to `a` times the projection of `x`, so the same equalities
   hold after reduction and passage to the derived category. Adjoint transposition identifies
   these maps with `adicLimitReduction`; iterating the displayed consecutive-level equality
   gives compatibility for all pairs of levels. -/
theorem rlim_perfect_complete {A : Type u} [CommRing A] (I : Ideal A)
    [IsAdicComplete I A]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [∀ n : ℕ, HasDerivedCategory.{u} (ModuleCat.{u} (A ⧸ I ^ (n + 1)))]
    (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))))
    (t : ∀ n : ℕ, K (n + 1) ⟶ (adicStepRestriction I n).obj (K n))
    (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))))
    (adj : ∀ n : ℕ, L n ⊣ adicLevelRestriction I n)
    (B : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1 + 1))) ⥤
      DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))))
    (badj : ∀ n : ℕ, B n ⊣ adicStepRestriction I n)
    (hbase : ∀ n : ℕ, IsIso (((badj n).homEquiv (K (n + 1)) (K n)).symm (t n)))
    (hperfect : IsPerfect (K 0))
    [HasProduct (fun n : ℕ ↦ (adicLevelRestriction I n).obj (K n))]
    (C : DerivedCategory (ModuleCat.{u} A))
    (p : C ⟶ ∏ᶜ (fun n : ℕ ↦ (adicLevelRestriction I n).obj (K n)))
    (δ : ∏ᶜ (fun n : ℕ ↦ (adicLevelRestriction I n).obj (K n)) ⟶ C⟦(1 : ℤ)⟧)
    (hlim : IsDerivedLimitTriangle (adicTowerTransition I K t) C p δ) :
    IsPerfect C ∧ IsDerivedComplete I C ∧
      (∀ n : ℕ, IsIso (adicLimitReduction I K L adj C p n)) ∧
      ∀ n : ℕ,
        (adj (n + 1)).unit.app C ≫
            (adicLevelRestriction I (n + 1)).map (adicLimitReduction I K L adj C p (n + 1)) ≫
            adicTowerTransition I K t n =
          (adj n).unit.app C ≫
            (adicLevelRestriction I n).map (adicLimitReduction I K L adj C p n) := by
  sorry

end DerivedCategory
