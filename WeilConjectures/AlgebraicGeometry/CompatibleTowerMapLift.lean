/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityNormalizedTowers
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.CategoryTheory.SequentialSemilinearDerivedDiagrams

/-!
# Unique lifting of compatible finite coefficient-tower isomorphisms

Source: latest blueprint, part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
`sk-lem-sp-tower-equivalence.proof.md`, Adjunction and Counit paragraphs,
specialized to degree-zero coefficient modules
(blueprint: lem-pur-compatible-tower-map-lift).

Index n denotes the positive coefficient level n+1. Transitions are the adjoints
of the recorded canonical reductions, with their actual restriction of scalars.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The actual adjacent derived transition, obtained by transposing the canonical
reduction through the recorded scalar-extension/restriction adjunction. Its
representative normalization follows from `D.ordinaryReduction_eq` and
`D.reduction_rep`: on complexes it is the original strict semilinear transition.
Source: latest blueprint, tower equivalence, Adjunction paragraph
(blueprint: lem-pur-compatible-tower-map-lift). -/
def spTowerMapLiftTransition (D : SpCoefficientTowersAbelian l E T)
    (K : spDerivedCoefficientTowers l E T D) (n : ℕ) :
    (spDerivedCoefficientEvaluation l E T D (n + 1)).obj K ⟶
      (systemRestriction (spCoefficientCommRings l E T) (Nat.le_succ n)).mapDerivedCategory.obj
        ((spDerivedCoefficientEvaluation l E T D n).obj K) :=
  letI := D.hasDerived
  (systemDerivedTensorAdj.{u + 1, u, u + 1}
    D.scalar (spCoefficientCommRings l E T) (Nat.le_succ n)).homEquiv _ _
      ((D.reduction (Nat.le_succ n)).app K)

/-- Compatible finite isomorphisms between normalized constructible towers whose
levels are the degree-zero coefficient module lift to a unique ambient derived
morphism; the lift is an isomorphism. Uniqueness ranges over all ambient morphisms.
Source: latest blueprint, tower equivalence, Adjunction and Counit paragraphs
(blueprint: lem-pur-compatible-tower-map-lift).

Proof:
1. Uncurry through the sectionwise normalized equivalence in D. The coefficient
   towers are exactly the strict varying-coefficient systems of
   `sequentialSemilinearDerivedDiagrams`, and its evaluations and transitions
   agree with the recorded ones. The given degree-zero models give the common
   lower cohomological bound zero for both towers.
2. Exact restriction of scalars sends a degree-zero module to its restricted
   degree-zero module. Standard t-structure orthogonality (Stacks 06XS,
   lemma-negative-exts with a=b=0 and shift -1) therefore kills every group
   Hom(C_(n+1), V_n D_n[-1]), hence their product Q^(-1).
3. The given squares say precisely that the vertex family lies in ker d^0.
   The five-term mapping sequence of the sequential theorem now identifies
   ambient Hom bijectively with that kernel, giving existence and uniqueness
   of the prescribed lift. Joint detection of isomorphisms by the evaluations,
   in the same theorem, makes the lift an isomorphism.
No exactness of infinite products or flatness of the quotient maps is assumed. -/
theorem sp_compatible_tower_map_lift [IsNoetherian T]
    (D : SpCoefficientTowersAbelian l E T)
    (C K : spNormalizedConstructibleTorTowerCategory l E T D)
    (_hC : ∀ n : ℕ, Nonempty
      ((spDerivedCoefficientEvaluation l E T D n).obj C.obj ≅
        (@DerivedCategory.singleFunctor
          (SheafOfModules.{u + 1} (spCoefficientRing l E T n))
          _ _ (HasDerivedCategory.standard _) 0).obj
            (SheafOfModules.unit (spCoefficientRing l E T n))))
    (_hK : ∀ n : ℕ, Nonempty
      ((spDerivedCoefficientEvaluation l E T D n).obj K.obj ≅
        (@DerivedCategory.singleFunctor
          (SheafOfModules.{u + 1} (spCoefficientRing l E T n))
          _ _ (HasDerivedCategory.standard _) 0).obj
            (SheafOfModules.unit (spCoefficientRing l E T n))))
    (f : ∀ n : ℕ, (spDerivedCoefficientEvaluation l E T D n).obj C.obj ≅
      (spDerivedCoefficientEvaluation l E T D n).obj K.obj)
    (_hf : ∀ n : ℕ,
      spTowerMapLiftTransition l E T D C.obj n ≫
          (systemRestriction (spCoefficientCommRings l E T) (Nat.le_succ n)).mapDerivedCategory.map
            (f n).hom =
        (f (n + 1)).hom ≫ spTowerMapLiftTransition l E T D K.obj n) :
    ∃ g : C.obj ⟶ K.obj,
      (∀ n : ℕ, (spDerivedCoefficientEvaluation l E T D n).map g = (f n).hom) ∧
      IsIso g ∧
      ∀ g' : C.obj ⟶ K.obj,
        (∀ n : ℕ, (spDerivedCoefficientEvaluation l E T D n).map g' = (f n).hom) →
          g' = g := by
  sorry

end AlgebraicGeometry.ProEtale
