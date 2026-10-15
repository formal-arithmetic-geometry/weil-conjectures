/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.CumulativeUniversalBaseChangeProperty
public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
public import Sheaf.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum
import Sheaf.AlgebraicGeometry.SmoothBaseChange.CoefficientHigherDirectImageZero
import Sheaf.AlgebraicGeometry.SmoothBaseChange.PrimeCyclicDetection
import Sheaf.AlgebraicGeometry.IntegralPushforwardBaseChangeArrow

/-!
# A universal base-change failure over a geometric generic point

Source: Stacks Project, Tag 0F08, Lemma 59.88.7; blueprint sec-smooth-base-change,
sk-lem-universal-datum (blueprint: sbc-lem-bc-universal-test).

The conclusion uses abelian sheaves with constant value the additive group of `ZMod d`.
Its higher direct image is written as the homology of the bounded-below derived direct
image on a sheaf in degree zero. This avoids replacing the cyclic group by `Λ/dΛ` for
an arbitrary coefficient ring. The `ULift` only implements the small-site size convention.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- A failure of universal base change in the first possible positive degree has a
geometric generic-point witness with nonzero cyclic abelian higher direct image.
Source: Stacks Project, Tag 0F08, Lemma 59.88.7; blueprint sec-smooth-base-change,
sk-lem-universal-datum (blueprint: sbc-lem-bc-universal-test).

Proof:
1. By `sbc-lem-bc-failure-field`, choose an affine base change, a field point and an
   `n`-annihilated sheaf witnessing failure. The horizontal map is qcqs because both
   its source and target are affine (`lem-weil-pbc-affine-scheme-qcqs` and
   `lem-weil-pbc-qcqs-morphism-permanence`).
2. Pass to an algebraic closure of the field. Its spectrum map is integral and surjective;
   `sbc-lem-bc-integral-surjective` and the universal degree-`q-1` hypothesis preserve failure.
3. Apply `lem-sbc-normalization-algclosed-field` to obtain the affine integral normal base
   with algebraically closed function field and the displayed field embedding. Pull back
   the total space. By `lem-sbc-integral-pushforward-base-change-arrow`, an isomorphism
   after normalization would imply the old isomorphism; thus failure persists.
4. Universality gives the lower-degree property on this base change. By
   `sbc-lem-bc-injectivity` the failing arrow is mono, so its target is nonzero. Its
   horizontal projection is qcqs by base-change permanence.
5. Regard the sheaf as a `ZMod n`-module. Apply
   `lem-sbc-coefficient-higher-direct-image-zero` and `lem-sbc-prime-cyclic-detection`:
   there is a prime `r` dividing `n` with nonzero higher direct image of the constant
   module `P_r/(r)`, where `P_r = ULift (ZMod r)`.
6. Multiplication by `r` in `P_r` vanishes, so this quotient has underlying additive
   group `ZMod r`. Restriction of scalars and the canonical equivalence of integer
   modules with abelian groups identify its higher direct image with the one below;
   constant sheafification preserves the coefficient isomorphism. Take `d = r`.
Normality is written as integral closedness of every stalk; integrality already makes
these stalks domains. The morphism induced by `i` is dominant since its image is the
generic point, and every map from a field to a field is injective. -/
theorem exists_universalBaseChangeFailure_cyclic_datum
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(S, ⊤))) (q : ℕ) (hq : 1 ≤ q)
    (hprev : CumulativeUniversalBaseChangeProperty f n hn hinv (q - 1))
    (hfail : ¬ UniversalBaseChangeProperty (ULift.{u + 1} (ZMod n)) f (q : ℤ)) :
    ∃ (S' X' : Scheme.{u}) (a : S' ⟶ S) (b : X' ⟶ X) (f' : X' ⟶ S')
      (_ : ChosenCartesianSquare b f' f a) (_ : IsAffine S') (_ : IsIntegral S')
      (_ : ∀ x : S', IsIntegrallyClosed (S'.presheaf.stalk x))
      (_ : IsAlgClosed S'.functionField) (K : Type u) (_ : Field K) (_ : IsAlgClosed K)
      (i : S'.functionField ⟶ CommRingCat.of K) (Y : Scheme.{u})
      (e : Y ⟶ Spec (.of K)) (h : Y ⟶ X')
      (_ : ChosenCartesianSquare h e f'
        (Spec.map i ≫ S'.fromSpecStalk (genericPoint S'))) (d : ℕ),
      d ∣ n ∧ ¬ IsZero
        ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
                (AddCommGrpCat.of (ULift.{u + 1} (ZMod d))))))) := by
  sorry

end AlgebraicGeometry.Etale
