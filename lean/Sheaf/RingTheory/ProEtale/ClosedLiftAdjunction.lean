/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.RingTheory.ProEtale.ClosedLiftMap
public import Sheaf.RingTheory.IndPrincipalZariski
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.RingTheory.IndEtaleStability
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.RingTheory.FinitePresentation
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import WeilConjectures.RingTheory.ProEtale.ClosedLift

/-! # The closed-lift adjunction on ind-etale algebras

Source: Stacks Project, Tag 097P, proof of `lemma-lift-ind-etale`, final two paragraphs;
blueprint, smooth purity, `lem-exc-closed-lift-adjunction`
(blueprint: lem-exc-closed-lift-adjunction).

The adjunction is expressed by its natural family of Hom equivalences. Naturality is
written on quotient representatives; the quotient maps are surjective, so these are
exactly the two naturality identities on Hom sets. No category or reduction functor is
redefined. The explicit quotient algebra structure is Mathlib's canonical one.
-/

@[expose] public section

universe u

open CategoryTheory

namespace Algebra.ClosedLift

/-- Reduction is left adjoint to the closed lift, expressed as a natural Hom equivalence.
Source: Stacks Project, Tag 097P, final two proof paragraphs
(blueprint: lem-exc-closed-lift-adjunction).

The first identity specifies the map on every quotient class. The second is naturality
under precomposition in `D`, and the third is naturality under postcomposition in `C`.
The final two identities say that the specified closed-lift maps preserve identities and
composition. Together with ind-etaleness of the reduction and the existing ind-etaleness
instance for `ClosedLift`, this is the Hom-set definition of the claimed adjunction.

Proof plan:
1. The indexing category is small and filtered (lem-exc-closed-lift-filtered), with etale
finite-presentation terms, so its colimit is ind-etale. Reduction is quotient base change,
so lem-weil-pbc-ind-etale-stability makes it ind-etale. The composite of any map to the
lift with `toAlgHom` kills the extended ideal, hence descends to the quotient.
2. For etale finite-presentation `D`, choose a finite presentation
(def-weil-pbc-finitely-presented-algebra). A map from its reduction supplies an indexing
object and hence a coprojection to the lift. Compatible presentation isomorphisms in the
indexing category show independence of this choice.
3. For uniqueness, use lem-weil-pbc-filtered-colimit-algebras-elementwise to view the
algebra colimit as a ring colimit. Then
lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit factors a map from `D`
through a stage. Its compatibility with the retained map makes this an indexing morphism;
the cocone relation identifies the map with the coprojection from step 2.
4. Present general ind-etale `D` as a small filtered colimit of etale algebras. The unique
finite-stage lifts commute with transitions by step 3. The universal property
(def-weil-pbc-category-colimit) gives a unique lift from `D`, proving bijectivity.
5. The formula on representatives gives contravariant naturality. For covariance,
`ι_map` gives compatibility of the retained maps on every coprojection; the colimit
universal property gives compatibility globally. The same argument proves identity and
composition for `map`.
6. The inverse Hom equivalences define reduction left adjoint to the closed lift.
The image of the identity is the specified reduction map, so this is the counit;
lem-exc-closed-lift-reduction identifies it as an isomorphism. -/
theorem exists_natural_homEquiv (A : Type u) [CommRing A] (I : Ideal A) :
    ∃ β : ∀ (D C : CommAlgCat.{u} A) [Algebra (A ⧸ I) C]
      [IsScalarTower A (A ⧸ I) C] [Algebra.IndEtale A D]
      [Algebra.IndEtale (A ⧸ I) C],
      (D →ₐ[A] ClosedLift A C) ≃
        @AlgHom (A ⧸ I) (D ⧸ I.map (algebraMap A D)) C _ _ _
          (Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map) _,
    ∀ (D C : CommAlgCat.{u} A) [Algebra (A ⧸ I) C]
      [IsScalarTower A (A ⧸ I) C] [Algebra.IndEtale A D]
      [Algebra.IndEtale (A ⧸ I) C],
      @Algebra.IndEtale (A ⧸ I) (D ⧸ I.map (algebraMap A D)) _ _
        (Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map) ∧
      (∀ (f : D →ₐ[A] ClosedLift A C) (d : D),
        β D C f (Ideal.Quotient.mk _ d) = toAlgHom A C (f d)) ∧
      (∀ (D' : CommAlgCat.{u} A) [Algebra.IndEtale A D']
        (r : D' →ₐ[A] D) (f : D →ₐ[A] ClosedLift A C) (d : D'),
        β D' C (f.comp r) (Ideal.Quotient.mk _ d) =
          β D C f (Ideal.Quotient.mk _ (r d))) ∧
      (∀ (C' : CommAlgCat.{u} A) [Algebra (A ⧸ I) C']
        [IsScalarTower A (A ⧸ I) C'] [Algebra.IndEtale (A ⧸ I) C']
        (φ : C →ₐ[A ⧸ I] C') (f : D →ₐ[A] ClosedLift A C) (d : D),
        β D C' ((map (φ.restrictScalars A)).comp f) (Ideal.Quotient.mk _ d) =
          φ (β D C f (Ideal.Quotient.mk _ d))) ∧
      map (AlgHom.id A C) = AlgHom.id A (ClosedLift A C) ∧
      (∀ (C' C'' : CommAlgCat.{u} A) [Algebra (A ⧸ I) C']
        [Algebra (A ⧸ I) C''] [IsScalarTower A (A ⧸ I) C']
        [IsScalarTower A (A ⧸ I) C''] [Algebra.IndEtale (A ⧸ I) C']
        [Algebra.IndEtale (A ⧸ I) C'']
        (φ : C →ₐ[A ⧸ I] C') (ψ : C' →ₐ[A ⧸ I] C''),
        map ((ψ.comp φ).restrictScalars A) =
          (map (ψ.restrictScalars A)).comp (map (φ.restrictScalars A))) := sorry

end Algebra.ClosedLift
