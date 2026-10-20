/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
public import Mathlib.AlgebraicGeometry.Scheme
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel
import Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose
import Sheaf.AlgebraicGeometry.EtaleLocalDualInterval
import Sheaf.CategoryTheory.RingedSitePerfectDuality
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.SixFunctors.EtaleFiniteProjectivePullbackHom
import Sheaf.SixFunctors.EtaleHomComplexPullback
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated

/-!
Finite-projective internal-Hom exchange on an étale stratum.

Source: literature/stacks-project/cohomology.tex, Tags 08DM and 08DQ, and Tag 0GM7(1).
The proof is the chartwise strictly-perfect Hom calculation, the finite truncation interval
argument, and descent of the evaluation-induced comparison. This Q79 delivery revalidates
the landed statement without changing its signature. -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- On a finite-coefficient étale site, pullback of internal Hom from a locally bounded
finite-projective constant model is an isomorphism, with the indicated cohomological bound.
Source: literature/stacks-project/cohomology.tex, Tags 08DM and 08DQ and Tag 0GM7(1)
(blueprint: lem-sf-etale-generic-perfect-hom).

Proof (deferred): refine the given étale cover and represent `P` on each chart by the
bounded complex `E` in the hypothesis.  The chart pullbacks represent `P'` by exactness of
constant-coefficient inverse image, and the derived tensor pullback comparison is the
canonical comparison from `leftDerivedUpperStarTensorIso`.  The bounded-free Hom model
and the termwise finite-projective pullback-Hom identity identify the chart map with the
map induced by the displayed evaluation formula.  The finite truncation filtration of
`N`, together with the dual interval `[-b,-a]`, gives the two cohomological intervals
`[c-b,d-a]`; exact inverse image gives the same interval after pullback.  These local
isomorphisms agree on refinements by naturality of evaluation and transpose, so the
cover-local isomorphism criterion gives the global `β` and its displayed equation. -/
theorem etaleGenericPerfectHom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S S' : Scheme.{u}} (g : S' ⟶ S)
    (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d)
    (P N : DerivedCategoryModule A S)
    (hP : ∃ U : Scheme.Cover.{u} Scheme.etalePrecoverage S,
      ∀ i : U.I₀,
        ∃ E : CochainComplex
            (Sheaf (U.X i).smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
          Nonempty
            (DerivedCategory.Q.obj E ≅
              (Etale.upperStar (ModuleCat.{u + 1} A) (U.f i)).mapDerivedCategory.obj P) ∧
          (∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) ∧
          (∀ n : ℤ, ∃ r : ℕ,
            ∃ ι : E.X n ⟶
                (constantSheaf (U.X i).smallEtaleTopology
                  (ModuleCat.{u + 1} A)).obj
                  (ModuleCat.of A (Fin r → A)),
            ∃ π :
                (constantSheaf (U.X i).smallEtaleTopology
                  (ModuleCat.{u + 1} A)).obj
                  (ModuleCat.of A (Fin r → A)) ⟶ E.X n,
              ι ≫ π = 𝟙 (E.X n)))
    (hN : ∀ n : ℤ, n < c ∨ d < n →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) n).obj N)) :
    let H : DerivedCategoryModule A S :=
      ((RHom(S)[ModuleCat.{u + 1} A]).obj (op P)).obj N
    let P' : DerivedCategoryModule A S' :=
      (Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).obj P
    let N' : DerivedCategoryModule A S' :=
      (Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).obj N
    let H' : DerivedCategoryModule A S' :=
      ((RHom(S')[ModuleCat.{u + 1} A]).obj (op P')).obj N'
    let ev :
        ((derivedTensor (ModuleCat.{u + 1} A) S).obj H).obj P ⟶ N := by
      simpa [H] using
        ((derivedTensorSymmetry (ModuleCat.{u + 1} A) S).hom.app H).app P ≫
          (derivedTensorHomAdjunction (ModuleCat.{u + 1} A) P).counit.app N
    let ev' :
        ((derivedTensor (ModuleCat.{u + 1} A) S').obj H').obj P' ⟶ N' := by
      simpa [H', P', N'] using
        ((derivedTensorSymmetry (ModuleCat.{u + 1} A) S').hom.app H').app P' ≫
          (derivedTensorHomAdjunction (ModuleCat.{u + 1} A)
            ((Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).obj P)).counit.app
            ((Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).obj N)
    ((∀ n : ℤ, n < c - b ∨ d - a < n →
        IsZero ((DerivedCategory.homologyFunctor
          (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) n).obj H)) ∧
      (∀ n : ℤ, n < c - b ∨ d - a < n →
        IsZero ((DerivedCategory.homologyFunctor
          (Sheaf S'.smallEtaleTopology (ModuleCat.{u + 1} A)) n).obj H')) ∧
      ∃ β : (Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).obj
          (((RHom(S)[ModuleCat.{u + 1} A]).obj (op P)).obj N) ≅
          ((RHom(S')[ModuleCat.{u + 1} A]).obj (op P')).obj N',
        ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g
            (((RHom(S)[ModuleCat.{u + 1} A]).obj (op P)).obj N) P).inv ≫
            (Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).map ev) =
          ((derivedTensor (ModuleCat.{u + 1} A) S').map β.hom).app
            ((Functor.leftDerivedFunctor ((g)^*[ModuleCat.{u + 1} A])).obj P) ≫ ev') := by
  sorry

end AlgebraicGeometry.Etale
