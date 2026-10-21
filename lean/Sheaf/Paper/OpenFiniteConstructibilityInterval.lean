/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Sheaf.AlgebraicGeometry.ProEtaleModulePullbackComposition
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Topology.Constructible
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Open extension preserves finite constructibility and cohomological intervals

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.7.7, open factor;
Stacks Project, Tags 09AH and 09BN
(blueprint: lem-sf-open-finite-constructibility-interval).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Open extension preserves bounded finite-torsion constructibility and each supplied
cohomological interval. Cohomology commutes with the canonical exact extension by zero.
Every given witnessing stratification extends by the reduced closed complement, retaining
its immersed strata over the ambient scheme and finite locally constant restrictions.
An arbitrary collection of empty strata may be omitted. The immediately applied instance
lambda supplies the proved finite-ring witness and the existing small-site sheafification
transport at its fixed coefficient size; it introduces no additional hypothesis or definition.

Source: Bhatt--Scholze, Lemma 6.7.7, preservation by the open factor;
Stacks Project, Tags 09AH and 09BN
(blueprint: lem-sf-open-finite-constructibility-interval).

Proof, following the six steps of the node:
1. Noetherian opens are quasi-compact (lem-weil-pbc-noetherian-open-subscheme-noetherian),
so j is quasi-compact by the affine criterion (def-weil-finite-type-morphism). Choose the
reduced closed complement (lem-weil-pbc-reduced-induced-closed-subscheme). Identify
inverse-image constant coefficients (lem-pur-proetale-constant-coefficient-comparison)
and apply lem-weil-pbc-proetale-ringed-open-closed.
2. Exactness and lem-sf-exact-functor-derived-triangulated give termwise derived extension.
The exact-functor cohomology comparison (lem-weil-pbc-exact-functor-complex-cohomology)
is natural in representatives and descends through quasi-isomorphisms.
3. Keep every original stratum immersion, composed with j, and add the reduced complement.
Locally closed subsets of an open remain locally closed in the ambient scheme
(def-weil-locally-closed-subset, def-weil-closed-immersion). The Noetherian topology
(lem-weil-pbc-noetherian-scheme-closed-subsets-minimal) makes all these subsets constructible
(def-weil-constructible-subset). Omitting any chosen empty strata preserves disjointness
and coverage, giving the stratification
(def-constructible-stratification).
4. Constant-coefficient pullback composition (lem-pur-proetale-module-pullback-composition)
and the open unit identify restrictions on the original strata with the original sheaves.
The complementary restriction is zero by lem-weil-pbc-proetale-ringed-open-closed.
5. Transport each local constant model and its finite stalks through these isomorphisms.
The complement has the constant zero module with singleton stalks
(def-weil-proetale-locally-constant-sheaf, def-weil-proetale-constructible-sheaf).
The cohomology comparison transports these witnesses to the output cohomology.
6. Outside [a,b], input cohomology is zero and additive extension preserves zero.
The output therefore has the same interval (def-weil-cohomological-support), finite
cohomological support, and constructible cohomology (def-weil-finite-torsion-constructibility).
This includes the empty open, the identity open, zero complexes, and empty strata. -/
theorem open_finite_constructibility_interval
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {U V : Scheme.{u}} [IsNoetherian V] (j : U ⟶ V) [IsOpenImmersion j]
    (_hl : ∀ v : V, IsUnit (l : V.presheaf.stalk v))
    (a b : ℤ) (_hab : a ≤ b)
    (C : proEtaleDerivedCategory U (Padic.coefficientExtensionRing l E n))
    (_hC : intrinsicFiniteTorsionConstructible l E n hn U C)
    (_hC_support : proEtaleCohomologicalSupport C ⊆ Set.Icc a b) :
    (fun [hfin : Finite (Padic.coefficientExtensionRing l E n)]
      [hU : (ProEt.topology U).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
      [hV : (ProEt.topology V).WEqualsLocallyBijective AddCommGrpCat.{u + 1}] ↦
      intrinsicFiniteTorsionConstructible l E n hn V
        ((sfIntrinsicExtensionByZero j
          (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.obj
        C) ∧
        proEtaleCohomologicalSupport
          ((sfIntrinsicExtensionByZero j
            (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.obj
          C) ⊆ Set.Icc a b ∧
        (∀ r : ℤ, Nonempty
          (((DerivedCategory.homologyFunctor
            (proEtaleRingModules V
              (proEtaleConstantRing V (Padic.coefficientExtensionRing l E n))) r).obj
                ((sfIntrinsicExtensionByZero j
                  (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.obj
                C)) ≅
            (sfIntrinsicExtensionByZero j
              (Padic.coefficientExtensionRing l E n)).obj
                ((DerivedCategory.homologyFunctor
                  (proEtaleRingModules U
                    (proEtaleConstantRing U (Padic.coefficientExtensionRing l E n))) r).obj C))) ∧
        (∀ (r : ℤ) (S : FiniteLocallyClosedStratification U),
          (∀ k : Fin S.n, Topology.IsConstructible (S.stratum k)) →
          (∀ k : Fin S.n, IsLocallyConstantProEtaleModuleSheafOfUniverses
            (S.domain k) (Padic.coefficientExtensionRing l E n)
              (proEtaleConstantModulePullback (S.immersion k)
                (Padic.coefficientExtensionRing l E n)
                ((DerivedCategory.homologyFunctor
                  (proEtaleRingModules U
                    (proEtaleConstantRing U (Padic.coefficientExtensionRing l E n))) r).obj C))) →
          (∀ (k : Fin S.n) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
            (x : Spec (.of Ω) ⟶ S.domain k),
            Finite (proEtaleGeometricModuleStalk x
              (proEtaleConstantRing (S.domain k) (Padic.coefficientExtensionRing l E n))
              (proEtaleConstantModulePullback (S.immersion k)
                (Padic.coefficientExtensionRing l E n)
                ((DerivedCategory.homologyFunctor
                  (proEtaleRingModules U
                    (proEtaleConstantRing U (Padic.coefficientExtensionRing l E n))) r).obj C)))) →
          ∀ (Z : Scheme.{u}) (i : Z ⟶ V) [IsClosedImmersion i] [IsReduced Z],
            Set.range i = (Set.range j)ᶜ →
            (∀ omitted : Set (Option (Fin S.n)),
              (∀ q ∈ omitted, match q with
                | none => IsEmpty Z
                | some h => IsEmpty (S.domain h)) →
              ∃ (T : FiniteLocallyClosedStratification V)
                  (e : Fin T.n ≃ {q : Option (Fin S.n) // q ∉ omitted}),
                (∀ k : Fin T.n, Topology.IsConstructible (T.stratum k)) ∧
                (∀ k : Fin T.n, match (e k).val with
                  | none => Nonempty (Over.mk (T.immersion k) ≅ Over.mk i)
                  | some h => Nonempty (Over.mk (T.immersion k) ≅
                      Over.mk (S.immersion h ≫ j))) ∧
                (∀ k : Fin T.n, IsLocallyConstantProEtaleModuleSheafOfUniverses
                  (T.domain k) (Padic.coefficientExtensionRing l E n)
                    (proEtaleConstantModulePullback (T.immersion k)
                      (Padic.coefficientExtensionRing l E n)
                      ((DerivedCategory.homologyFunctor
                        (proEtaleRingModules V
                          (proEtaleConstantRing V (Padic.coefficientExtensionRing l E n))) r).obj
                            ((sfIntrinsicExtensionByZero j
                              (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.obj
                            C)))) ∧
                (∀ (k : Fin T.n) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
                  (x : Spec (.of Ω) ⟶ T.domain k),
                  Finite (proEtaleGeometricModuleStalk x
                    (proEtaleConstantRing (T.domain k) (Padic.coefficientExtensionRing l E n))
                    (proEtaleConstantModulePullback (T.immersion k)
                      (Padic.coefficientExtensionRing l E n)
                      ((DerivedCategory.homologyFunctor
                        (proEtaleRingModules V
                          (proEtaleConstantRing V (Padic.coefficientExtensionRing l E n))) r).obj
                            ((sfIntrinsicExtensionByZero j
                              (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.obj
                            C)))))) ∧
            IsZero (proEtaleConstantModulePullback i (Padic.coefficientExtensionRing l E n)
              ((DerivedCategory.homologyFunctor
                (proEtaleRingModules V
                  (proEtaleConstantRing V (Padic.coefficientExtensionRing l E n))) r).obj
                    ((sfIntrinsicExtensionByZero j
                      (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.obj
                    C)))))
      (hfin := Padic.finite_coefficientExtensionRing l E n hn)
      (hU := WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} U)
      (hV := WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} V) := by
  sorry

end AlgebraicGeometry.Scheme
