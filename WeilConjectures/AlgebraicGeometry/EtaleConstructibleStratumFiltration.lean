/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleLocallyConstantPerfectComplex
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.EtaleGenericImmersionProjection
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # Finite perfect-stratum devissage on the ordinary etale site

Source: Bhatt--Scholze, The pro-etale topology for schemes, Definition 6.3.1,
Lemmas 6.3.3 and 6.3.9, pp. 45--47; Stacks Project, Tags 09BI and 095L
(blueprint: lem-per-etale-constructible-stratum-filtration).

Both the finite triangle tower and its replete triangulated generation formulation
are stated. The published `immersionLowerShriek` is the exact closed direct image
followed by exact open extension by zero, applied termwise on derived categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Etale

/-- A bounded constructible finite-Tor complex has a finite constructible
stratification and a triangle tower with shifted perfect local-system quotients.
Source: Bhatt--Scholze, Definition 6.3.1 and Lemma 6.3.3, pp. 45--46;
Stacks Project, Tags 09BI, 095L, 09Y5 and 005L
(blueprint: lem-per-etale-constructible-stratum-filtration).

Proof:
1. Choose a common finite refinement for the finitely many constructible cohomology
sheaves, using new-det-lem-coefficient-heart-common-stratification-refinement.
Order connected strata with open prefixes. Give each difference its reduced closed
structure inside its prefix using lem-weil-pbc-reduced-induced-closed-subscheme.
Noetherianity makes the locally closed images constructible; use
lem-weil-pbc-noetherian-scheme-closed-subsets-minimal. For empty X take no strata.
2. Restrict K to each stratum. Exact inverse image commutes with cohomology by
prop-weil-pbc-inverse-image-modules-exact and
lem-weil-pbc-exact-functor-complex-cohomology. Image refinement preserves finite lisse
cohomology by lem-weil-pbc-refinement-preserves-finite-lisse. Identity scalar change
in lem-coef-etale-domain-pullback-calculus preserves bounded constructibility and
its Tor interval.
3. Apply lem-per-etale-lisse-ctf-perfect-local-model on every connected stratum.
This gives the etale local bounded finite-projective coefficient models; it does
not assert that the individual cohomology modules are projective.
4. Apply lem-cbc-open-closed-recollement inside each prefix open, then apply exact
open extension by zero to X. Exact derived functors preserve distinguished triangles
by lem-weil-pbc-exact-functor-derived-factorization. The composition identifications
are lem-cbc-extension-zero-composition and lem-weil-pbc-inverse-image-composition.
The three terms are successive open-supported pieces and closed-in-open extensions
of the stratum restrictions.
5. The empty open gives the zero object; the total open gives K using the identity
inverse-image and extension-by-zero identifications. These triangles form the tower.
The quotients in this construction have shift zero, which is an allowed shift.
-/
theorem exists_etaleConstructibleStratumFiltration
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X] (K : DerivedCategoryModule A X)
    (_hK : DerivedCategory.isBoundedConstructible A X K)
    (_hTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A X a b K) :
    ∃ T : Scheme.FiniteLocallyClosedStratification X,
      (∀ i : Fin T.n, Topology.IsConstructible (T.stratum i)) ∧
      ∃ (U : Fin T.n → X.Opens)
        (c : ∀ i : Fin T.n, T.domain i ⟶ (U i).toScheme)
        (hc : ∀ i : Fin T.n, IsClosedImmersion (c i))
        (P : ∀ i : Fin T.n, DerivedCategoryModule A (T.domain i))
        (s : Fin T.n → ℤ) (F : Fin (T.n + 1) → DerivedCategoryModule A X),
        (∀ i : Fin T.n, c i ≫ (U i).ι = T.immersion i) ∧
        (∀ i : Fin T.n, ∃ a b : ℤ, (P i).IsGE a ∧ (P i).IsLE b) ∧
        (∀ i : Fin T.n, IsLocallyConstantPerfectEtaleComplex A (T.domain i) (P i)) ∧
        IsZero (F 0) ∧ Nonempty (F (Fin.last T.n) ≅ K) ∧
        ∀ i : Fin T.n,
          ∃ (f : F i.castSucc ⟶ F i.succ)
            (g : F i.succ ⟶
              ((@immersionLowerShriek A _ _ _ _ (c i) (U i).ι (hc i) _).obj (P i))⟦s i⟧)
            (h : ((@immersionLowerShriek A _ _ _ _ (c i) (U i).ι (hc i) _).obj (P i))⟦s i⟧ ⟶
              (F i.castSucc)⟦(1 : ℤ)⟧),
            Triangle.mk f g h ∈ distTriang (DerivedCategoryModule A X) := by
  sorry

/-- Membership in the smallest replete triangulated subcategory containing every
constructible locally closed extension of a bounded locally constant perfect complex.
The universal property is quantified over object properties; no retract closure is used.
Source: Bhatt--Scholze, Lemmas 6.3.3 and 6.3.9, pp. 45--46
(blueprint: lem-per-etale-constructible-stratum-filtration).

Proof: apply the finite triangle tower of the preceding declaration. A replete
triangulated subcategory contains zero and all shifts of its specified generators.
Induct along the tower, using rotation and closure under cones at each triangle.
The final isomorphism transports membership to K. This is step 5 of the DAG proof,
using def-weil-triangulated-category and the tower from steps 1--4.
-/
theorem etaleConstructible_mem_perfectStratum_triangulated
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X] (K : DerivedCategoryModule A X)
    (_hK : DerivedCategory.isBoundedConstructible A X K)
    (_hTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A X a b K)
    (W : ObjectProperty (DerivedCategoryModule A X))
    [W.IsClosedUnderIsomorphisms] [W.IsTriangulated]
    (_hW : ∀ (U : X.Opens) (S : Scheme.{u}) (c : S ⟶ U.toScheme)
      (hc : IsClosedImmersion c), Topology.IsConstructible (Set.range (c ≫ U.ι)) →
      ∀ P : DerivedCategoryModule A S,
        (∃ a b : ℤ, P.IsGE a ∧ P.IsLE b) →
        IsLocallyConstantPerfectEtaleComplex A S P →
        W ((@immersionLowerShriek A _ _ _ _ c U.ι hc _).obj P)) : W K := by
  sorry

end AlgebraicGeometry.Etale
