/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerDescent
import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerAdjunct
import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTorIntervals
import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionLevelConstructible

/-! # Strict representatives for the normalized reduction tower

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-integral-towers,
`sk-prop-sp-integral-towers-reduction.md` and its proof, Construction,
Normalization, and Constructibility (blueprint: det-sp-reduction-tower-normalized).

Index n denotes positive exponent n+1. The existing reduction data retain the
completed integral coefficients, the ordinary derived category of strict towers,
the specified reduction adjuncts, and the qcqs constructibility assertions.
The statement below additionally spells out the strict complex and the comparison
on representatives, including arbitrary morphisms in the derived category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The strict complex of towers obtained by applying ordinary coefficient extension
in every degree: its differential is ordinary.map of the original differential.
Its levels and quotient transitions are fixed by r.level and r.transition.
Source: blueprint latest, integral-towers-reduction, Construction
(blueprint: det-sp-reduction-tower-normalized). -/
abbrev spReductionStrictComplex (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) :
    CochainComplex (spIntegralSectionModules l E T) ℤ ⥤
      CochainComplex (spCoefficientTowers l E T) ℤ :=
  letI := r.additive
  r.ordinary.mapHomologicalComplex (.up ℤ)

/-- Reduction exists with its strict K-flat model, normalized transitions, and uniform
constructible finite-Tor bounds. The first extra clause identifies the strict
complex's level differentials with d_P tensor 1 using the actual scalar-extension
level isomorphisms. The second gives the representative comparison with its specified
counit. The third characterizes transport of every derived morphism between such
representatives; in particular the identity of a represented object determines the
comparison between any two representatives. The last clause includes all Tor
intervals, even empty intervals a>b, under precisely the qcqs constructibility
hypotheses: the cohomological support bound is asserted for every a,b, and the levelwise
Tor amplitude for ordered a<=b (the recorded predicate HasProEtaleTorAmplitude includes
a<=b; for a>b the vanishing of all levels is the empty-interval Tor statement).

Source: blueprint latest, sk-prop-sp-integral-towers-reduction, all three paragraphs
(blueprint: det-sp-reduction-tower-normalized).

Proof:
1. Identify the section-ring realization of the pulled-back condensed integer ring
with the completed ring using the multiplicative integral-limit comparison. Its
projections are the specified quotient coefficient maps.
2. Apply strict tensor presentation descent to obtain ordinary, level, transition,
red, and counit. Naturality of level applied to P.d identifies each differential
with d_P tensor 1. The transition formula on local pure tensors identifies the
strict transitions with 1 tensor the quotient map, since these tensors locally
generate the sheafified scalar extension.
3. Descent computes on K-flat complexes, so counit.app P is invertible, in
particular for the flat-term K-flat representatives of the source. Transport a
derived morphism by these invertible counits. Cancellation proves uniqueness;
the same formula respects identities and composition and the naturality square
for chain maps. Thus it is independent of representatives and natural for roofs.
4. The reduction adjunct normalization lemma identifies every actual reduction
map, including equal indices, with successive scalar-extension associativity.
5. For qcqs T and bounded constructible M, the Tor interval lemma gives finite
integral Tor amplitude and preserves each ordered interval both as Tor amplitude
and as cohomological support at every level. The level constructibility lemma
gives constructible finite-level homology. Choose an ordered finite interval;
these assertions give the normalized constructible finite-Tor tower predicate.
6. If a>b, the Tor test against the integral unit forces M=0; its reductions are
zero, so every level homology vanishes, which is the cohomological support assertion
for this remaining case (the Tor amplitude conjunct is only asserted for a<=b).
-/
theorem sp_reduction_tower_normalized_strict (D : SpCoefficientTowersAbelian l E T) :
    ∃ r : SpReductionTower l E T D,
      (∀ (P : CochainComplex (spIntegralSectionModules l E T) ℤ) (n : ℕ) (i j : ℤ),
        (r.level n).hom.app (P.X i) ≫
            (D.scalar (spIntegralReductionScalar l E T r.coefficient n)).model.E.map
              (P.d i j) =
          (spCoefficientEvaluation l E T D.equivalence n).map
              (r.ordinary.map (P.d i j)) ≫ (r.level n).hom.app (P.X j)) ∧
      (∀ (P : CochainComplex (spIntegralSectionModules l E T) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T) P →
        (∀ i : ℤ, SheafOfModules.IsFlatOnSite
          (C := T.ProEt) (J := Scheme.ProEt.topology T)
          (R := spIntegralSectionRing l E T) (P.X i)) →
        ∃ e : r.red.obj (DerivedCategory.Q.obj P) ≅
            (spTowerLocalization l E T D).obj ((spReductionStrictComplex l E T D r).obj P),
          e.hom = r.counit.app P) ∧
      (∀ (P P' : CochainComplex (spIntegralSectionModules l E T) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T) P →
        CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T) P' →
        (∀ i : ℤ, SheafOfModules.IsFlatOnSite
          (C := T.ProEt) (J := Scheme.ProEt.topology T)
          (R := spIntegralSectionRing l E T) (P.X i)) →
        (∀ i : ℤ, SheafOfModules.IsFlatOnSite
          (C := T.ProEt) (J := Scheme.ProEt.topology T)
          (R := spIntegralSectionRing l E T) (P'.X i)) →
        ∀ f : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj P',
          ∃! g : (spTowerLocalization l E T D).obj
                ((spReductionStrictComplex l E T D r).obj P) ⟶
              (spTowerLocalization l E T D).obj
                ((spReductionStrictComplex l E T D r).obj P'),
            r.counit.app P ≫ g = r.red.map f ≫ r.counit.app P') ∧
      (CompactSpace T → QuasiSeparatedSpace T →
        ∀ M : DerivedCategory (spIntegralSectionModules l E T),
          constantModelBoundedConstructible (spIntegralCondensed l E) T
            ((spIntegralInternalization l E T).obj M) →
          ∀ a b : ℤ,
            DerivedCategory.torAmplitudeIn _ a b ((spIntegralInternalization l E T).obj M) →
            ∀ n : ℕ,
              (a ≤ b → Scheme.HasProEtaleTorAmplitude T
                (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))
                ((spDerivedCoefficientEvaluation l E T D n).obj (r.red.obj M)) a b) ∧
              ∀ i : ℤ, (i < a ∨ b < i) → IsZero
                ((@DerivedCategory.homologyFunctor
                  (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T
                    (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))))
                  _ _ (HasDerivedCategory.standard _) i).obj
                  ((spDerivedCoefficientEvaluation l E T D n).obj (r.red.obj M)))) := by
  sorry

end AlgebraicGeometry.ProEtale
