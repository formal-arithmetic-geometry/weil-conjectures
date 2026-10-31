/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.OpenDirectImageFiniteCoefficients
import WeilConjectures.Compactification.Defs
import WeilConjectures.Compactification.Dense
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import WeilConjectures.AlgebraicGeometry.ProEtaleDirectImageComparison

/-!
# Finite-coefficient base change along a product projection

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-lem-tf-independent-base-change/_section.md, current order 3435
(the node retains historical main-20261023 order 2394)
(blueprint: sk-lem-tf-independent-base-change).

The exchange is the published ambient ringed mate with the canonical constant-ring
identifications. Bounded constructibility is expressed by the essential image of the
published finite-ring etale comparison, in the intrinsic constant-ring presentation.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The chosen Cartesian square of the first projections and `f × id_T`.
Its pullback identification is the universal one supplied by the product square,
then preserved by the forgetful functor from schemes over the base.
Source: blueprint order 3435, the definitions of h, p_X and p_Y
(blueprint: sk-lem-tf-independent-base-change). -/
def finiteProductProjectionSquare (D : WeilConjectures.FiniteFieldDatum.{u})
    {X Y : Over (Spec (.of D.k))} (f : X ⟶ Y) (T : Over (Spec (.of D.k))) :
    ChosenCartesianSquare (prod.fst : X ⨯ T ⟶ X).left
      (prod.map f (𝟙 T)).left f.left (prod.fst : Y ⨯ T ⟶ Y).left :=
  { toCommSq := ((IsPullback.of_prod_fst_with_id f T).map (Over.forget _)).toCommSq
    isoPullback := ((IsPullback.of_prod_fst_with_id f T).map (Over.forget _)).isoPullback
    hom_fst := ((IsPullback.of_prod_fst_with_id f T).map (Over.forget _)).isoPullback_hom_fst
    hom_snd := ((IsPullback.of_prod_fst_with_id f T).map (Over.forget _)).isoPullback_hom_snd }

/-- Base change along a product projection with finite commutative primary coefficients.
Source: blueprint order 3435, sk-lem-tf-independent-base-change, displayed exchange
(blueprint: sk-lem-tf-independent-base-change).

Proof:
1. Finite-type cancellation and separated cancellation make f separated of finite type.
   The separated finite-type Y over the affine field spectrum is qcqs. Apply Nagata
   compactification to factor f as an open immersion j followed by a proper map fbar
   (lemma-nagata-finite-type-to-separated-target, lem-weil-pbc-separated-cancellation,
   lem-weil-pbc-qcqs-over-affine, sk-thm-nagata-compactification,
   def-nagata-compactification).
2. Composition and the diagonal factorization make Xbar separated of finite type over k.
   The product squares for j and fbar are Cartesian, and j and its base change are qcqs
   (lem-sfb-finite-type-composition-base-change, def-weil-proper-morphism,
   lem-weil-pbc-closed-immersion-base-change, lem-weil-pbc-closed-immersion-comp,
   lem-pc-separated-quasi-separated, lem-weil-pbc-qcqs-morphism-permanence).
3. Choose a bounded constructible etale origin L of M using
   lem-weil-pbc-finite-ring-constructible-derived-origin. Some positive power of l kills A
   and is invertible in k. Open-image finiteness and qcqs direct-image comparison show
   N = Rj_*M is bounded constructible (cor-fin-deligne-open-finite-coefficients,
   sk-thm-pe-direct-image-comparison).
4. Apply det-geo-open-finiteness-base-change to j, T and L. The canonical comparison
   equation of lem-weil-pbc-transport-identifies-exchange identifies its etale exchange
   with the pro-etale exchange, so the latter is invertible at M. This permits singular T.
5. Apply det-tf-ibc-proper-step to fbar and N, obtaining invertibility of the proper
   factor's ordinary finite-coefficient exchange.
6. Under the canonical direct-image composition isomorphisms, det-tf-ibc-pasting
   identifies the requested map with these two exchanges, the second sent through
   the proper direct-image functor. Functors preserve inverses, so their composite
   and hence the specified ambient exchange at M is invertible.
-/
theorem isIso_finiteProductProjectionExchange
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) (_hl : l.Prime)
    (_hne : l ≠ ringChar D.k) (A : Type u) [CommRing A] [Finite A]
    (_hA : ∃ n : ℕ, 0 < n ∧ ((l ^ n : ℕ) : A) = 0)
    (X Y T : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (f : X ⟶ Y) (M : proEtaleDerivedCategory X.left A)
    (_hM : (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} A) X.left) ⋙
      ProEtale.finiteCoefficientIntrinsicDerivedComparison X.left A).essImage M) :
    IsIso ((proEtaleAmbientRingedExchange (finiteProductProjectionSquare D f T)
      (proEtaleConstantRing X.left A) (proEtaleConstantRing Y.left A)
      (proEtaleConstantRing (X ⨯ T).left A) (proEtaleConstantRing (Y ⨯ T).left A)
      (proEtaleConstantRingComparison f.left A)
      (proEtaleConstantRingComparison (prod.fst : Y ⨯ T ⟶ Y).left A)
      (proEtaleConstantRingComparison (prod.fst : X ⨯ T ⟶ X).left A)
      (proEtaleConstantRingComparison (prod.map f (𝟙 T)).left A)
      ((heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq
        (prod.fst : X ⨯ T ⟶ X).left f.left A)).trans
        ((congr_arg_heq
          (fun q : (X ⨯ T).left ⟶ Y.left ↦ proEtaleConstantRingComparison q A)
          (finiteProductProjectionSquare D f T).w).trans
          (heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq
            (prod.map f (𝟙 T)).left (prod.fst : Y ⨯ T ⟶ Y).left A)).symm))).app M) := by
  sorry

end AlgebraicGeometry.Scheme
