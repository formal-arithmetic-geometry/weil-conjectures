/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TruncationHypercohomology
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero
import Mathlib.Algebra.Homology.SpectralSequence.Basic
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.CategoryTheory.TruncationDescends
import WeilConjectures.CategoryTheory.CanonicalFiltration

/-! # The canonical edge for acyclic cohomology objects

Source: Stacks Project, sites-cohomology.tex, Tag 0D7U, lemma-equivalence-bounded;
the truncation spectral sequence of Tags 0D7S/0D7T.
(blueprint: lem-fd-acyclic-heart-edge).

The normalization below specifies the edge by its composite with the canonical
truncation inclusion. Under column collapse this is precisely the quotient to
the zeroth graded piece followed by the canonical abutment identification Theta.
-/

@[expose] public section

set_option autoImplicit false

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  [IsGrothendieckAbelian.{v₁} A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [IsGrothendieckAbelian.{v₂} B] [HasDerivedCategory.{w₂} B]

/-- The degree-zero second-page identification, with an object placed in degree q.
This is exactly the shift and ordinary-derived comparison in thm-sp-truncation-e2,
followed by the inverse of the degree-zero augmentation.
Source: Stacks Tags 05TD and 0D7U (blueprint: lem-fd-acyclic-heart-edge). -/
noncomputable def acyclicHeartSingleIso (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] (X : A) (q : ℤ) :
    (DerivedCategory.homologyFunctor B q).obj
        (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor A q).obj X)) ≅ F.obj X :=
  (DerivedCategory.homologyFunctor B q).mapIso
      (F.rightDerivedFunctor.mapIso
        (((DerivedCategory.singleFunctors A).shiftIso (-q) q 0 (by omega)).app X).symm) ≪≫
    (DerivedCategory.homologyFunctor B q).mapIso
      ((F.rightDerivedFunctor.commShiftIso (-q)).app
        ((DerivedCategory.singleFunctor A 0).obj X)) ≪≫
    ((DerivedCategory.homologyFunctor B 0).shiftIso (-q) q 0 (by omega)).app
      (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor A 0).obj X)) ≪≫
    F.homologyRightDerivedFunctorObjSingleFunctorIso X 0 ≪≫ F.rightDerivedZeroIsoSelf.app X

/-- The type of edge families on bounded-below objects with F-acyclic cohomology.
The proof argument records precisely the positive-degree acyclicity assumption.
Source: Stacks Tag 0D7U (blueprint: lem-fd-acyclic-heart-edge). -/
def AcyclicHeartEdgeFamily (F : A ⥤ B) [F.Additive] :=
  ∀ (L : DerivedCategory.Plus A),
    (∀ (j : ℤ) (p : ℕ), 0 < p →
      IsZero ((F.rightDerived p).obj ((DerivedCategory.homologyFunctor A j).obj L.obj))) →
    ∀ q : ℤ, (DerivedCategory.homologyFunctor B q).obj
        (F.rightDerivedFunctor.obj L.obj) ⟶
      F.obj ((DerivedCategory.homologyFunctor A q).obj L.obj)

/-- Normalize an edge on every bounded-below representative and every representing
isomorphism. The left side precomposes with c_q, the derived truncation inclusion.
The right side is the map g of the truncation couple, with its bridge isomorphisms
cancelled, followed by the second-page degree-zero comparison. Thus this condition
specifies the quotient/Theta edge, rather than an unspecified isomorphism.
Source: Stacks Tag 0D7U and thm-sp-truncation-e2, part 6
(blueprint: lem-fd-acyclic-heart-edge). -/
def IsAcyclicHeartEdge (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (edge : F.AcyclicHeartEdgeFamily) : Prop :=
  ∀ (L : DerivedCategory.Plus A)
    (h : ∀ (j : ℤ) (p : ℕ), 0 < p →
      IsZero ((F.rightDerived p).obj ((DerivedCategory.homologyFunctor A j).obj L.obj)))
    (K : CochainComplex.Plus A) (e : DerivedCategory.Q.obj K.obj ≅ L.obj) (q : ℤ),
    (DerivedCategory.homologyFunctor B q).map
        (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE q))) ≫
      (DerivedCategory.homologyFunctor B q).map (F.rightDerivedFunctor.map e.hom) ≫
      edge L h q =
    (DerivedCategory.homologyFunctor B q).map
        (F.rightDerivedFunctor.map (DerivedCategory.Q.map (TruncationCouple.projection K q))) ≫
      (F.acyclicHeartSingleIso (K.obj.homology q) q).hom ≫
      F.map (((DerivedCategory.homologyFunctorFactors A q).app K.obj).inv ≫
        (DerivedCategory.homologyFunctor A q).map e.hom)

/-- The canonical acyclic-heart edge is invertible and natural, including in compatible
morphisms of the derived-functor data. Compatibility is imposed only on shifted single
objects, by their degree-zero augmentation comparisons, not on the edge to be proved.
Source: Stacks Tag 0D7U, lemma-equivalence-bounded, spectral-sequence argument
(blueprint: lem-fd-acyclic-heart-edge).

Proof:
1. Choose a lower bound a and a bounded-below representative K of L. Apply
   thm-sp-truncation-e2. Grothendieck categories have enough injectives, so
   lem-weil-pbc-left-exact-injective-resolution-degree-zero identifies R^0F with F.
2. Every nonzero column of E_2 vanishes by acyclicity or negative vanishing.
   Induct on the page: each differential has zero source or zero target, so
   all pages identify canonically with E_2 and E_infinity does too.
3. In total degree n the filtration is finite, F^0=H^n and F^N=0 for
   N=max(1,n-a+1). Every positive graded piece vanishes. Finite descending
   induction gives F^1=0; no upper bound on the cohomology of L is needed.
4. The quotient H^n -> gr^0, Theta, the stable-page comparison and R^0F=F
   are isomorphisms. Part 6 of thm-sp-truncation-e2 identifies this composite
   with the normalized equation above: precomposition with c_n gives g.
   The invertibility of c_n also gives uniqueness of the normalized family.
5. Truncation triangles and their inclusions descend naturally through Q by
   lem-weil-pbc-truncation-descends and the localization universal property.
   Induced maps of couples commute with images, kernels, quotients, c_n and
   Theta. Passing to a common lower bound and stable page proves independence
   of the bound and representative, including the case of the identity map.
6. The degree-zero comparison is natural by the augmentation/kernel square.
   Composing these squares proves naturality for every derived morphism.
   A compatible transformation of derived functors gives the same squares on
   the truncation inclusion and projection; its single-object compatibility
   finishes the data square. Cancel c_n to obtain the asserted edge equation. -/
theorem exists_acyclicHeartEdge (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] :
    ∃! edge : F.AcyclicHeartEdgeFamily,
      F.IsAcyclicHeartEdge edge ∧
      (∀ (L : DerivedCategory.Plus A)
        (h : ∀ (j : ℤ) (p : ℕ), 0 < p →
          IsZero ((F.rightDerived p).obj ((DerivedCategory.homologyFunctor A j).obj L.obj)))
        (q : ℤ), IsIso (edge L h q)) ∧
      (∀ (L M : DerivedCategory.Plus A)
        (hL : ∀ (j : ℤ) (p : ℕ), 0 < p →
          IsZero ((F.rightDerived p).obj ((DerivedCategory.homologyFunctor A j).obj L.obj)))
        (hM : ∀ (j : ℤ) (p : ℕ), 0 < p →
          IsZero ((F.rightDerived p).obj ((DerivedCategory.homologyFunctor A j).obj M.obj)))
        (f : L ⟶ M) (q : ℤ),
        (DerivedCategory.homologyFunctor B q).map (F.rightDerivedFunctor.map f.hom) ≫
          edge M hM q =
        edge L hL q ≫ F.map ((DerivedCategory.homologyFunctor A q).map f.hom)) ∧
      (∀ (K : CochainComplex.Plus A)
        (hK : ∀ (j : ℤ) (p : ℕ), 0 < p →
          IsZero ((F.rightDerived p).obj (K.obj.homology j))),
        (∀ n : ℤ,
          imageSubobject ((DerivedCategory.homologyFunctor B n).map
            (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE n)))) = ⊤ ∧
          imageSubobject ((DerivedCategory.homologyFunctor B n).map
            (F.rightDerivedFunctor.map (DerivedCategory.Q.map (K.obj.ιTruncLE (n - 1))))) =
              ⊥) ∧
        (∀ X : BigradedExactCouple B 0, X.E = TruncationCouple.E F K →
          (∀ (r : ℕ) (p q : ℤ), 2 ≤ r → p ≠ 0 → IsZero (X.page r p q)) ∧
          (∀ (r : ℕ) (q : ℤ), X.cycleBoundaryTower.Z r 0 q = ⊤ ∧
            X.cycleBoundaryTower.B r 0 q = ⊥))) ∧
      (∀ (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G]
        (τ : F ⟶ G) (ρ : F.rightDerivedFunctor ⟶ G.rightDerivedFunctor),
        (∀ (X : A) (q : ℤ),
          (DerivedCategory.homologyFunctor B q).map
              (ρ.app ((DerivedCategory.singleFunctor A q).obj X)) ≫
            (G.acyclicHeartSingleIso X q).hom =
          (F.acyclicHeartSingleIso X q).hom ≫ τ.app X) →
        ∀ (edgeG : G.AcyclicHeartEdgeFamily), G.IsAcyclicHeartEdge edgeG →
        ∀ (L : DerivedCategory.Plus A)
          (hF : ∀ (j : ℤ) (p : ℕ), 0 < p →
            IsZero ((F.rightDerived p).obj ((DerivedCategory.homologyFunctor A j).obj L.obj)))
          (hG : ∀ (j : ℤ) (p : ℕ), 0 < p →
            IsZero ((G.rightDerived p).obj ((DerivedCategory.homologyFunctor A j).obj L.obj)))
          (q : ℤ),
          (DerivedCategory.homologyFunctor B q).map (ρ.app L.obj) ≫ edgeG L hG q =
            edge L hF q ≫ τ.app ((DerivedCategory.homologyFunctor A q).obj L.obj)) := by
  sorry

end CategoryTheory.Functor
