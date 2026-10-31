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
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import WeilConjectures.AlgebraicGeometry.OpenDirectImageFiniteCoefficients
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.AlgebraicGeometry.OpenDirectImageFieldBaseChange
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientModulePullbackComposition
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import WeilConjectures.AlgebraicGeometry.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.IntegralFinitePullbackComposition
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingMap
import WeilConjectures.AlgebraicGeometry.BaseChangeMapAbelianAndSets
import WeilConjectures.AlgebraicGeometry.ProEtaleDirectImageComparison
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Product-projection exchange through a compactification

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-lem-tf-independent-base-change/det-tf-ibc-pasting.md, order 3437;
Stacks Project, Tag 0E46 (blueprint: det-tf-ibc-pasting).

The helpers specialize the published ambient exchange and construct its canonical
right-adjoint composition maps. The supplied factorization is written as `j ≫ p`.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The ambient unit--square--counit exchange for the product with `T`.
The chosen square is the universal product square, forgotten from schemes over the base;
all four scalar identifications are the published constant-section comparisons.
Source: blueprint order 3437, first displayed arrow; Stacks Tag 0E46
(blueprint: det-tf-ibc-pasting). -/
def compactificationProductExchange (A : Type u) [CommRing A]
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) (T : Over S) :=
  proEtaleAmbientRingedExchange
    { toCommSq := ((IsPullback.of_prod_fst_with_id f T).map (Over.forget S)).toCommSq
      isoPullback := ((IsPullback.of_prod_fst_with_id f T).map (Over.forget S)).isoPullback
      hom_fst := ((IsPullback.of_prod_fst_with_id f T).map
        (Over.forget S)).isoPullback_hom_fst
      hom_snd := ((IsPullback.of_prod_fst_with_id f T).map
        (Over.forget S)).isoPullback_hom_snd }
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
        ((IsPullback.of_prod_fst_with_id f T).map (Over.forget S)).w).trans
        (heq_of_eq (proEtaleConstantRingCompositeCoefficients_eq
          (prod.map f (𝟙 T)).left (prod.fst : Y ⨯ T ⟶ Y).left A)).symm))

/-- The direct-image compositor, conjugate to the canonical constant-ring pullback
compositor under the specified derived adjunctions. This fixes the usual K-injective
composition identification, including its unit and counit normalization.
Source: blueprint order 3437, endpoint identifications; Stacks Tags 0D6E and 0E46
(blueprint: det-tf-ibc-pasting). -/
def compactificationDirectImageComposition (A : Type u) [CommRing A]
    {X B Y : Scheme.{u}} (j : X ⟶ B) (p : B ⟶ Y) :
    (proEtaleConstantRingPushforward A (j ≫ p)).rightDerivedFunctor ≅
      (proEtaleConstantRingPushforward A j).rightDerivedFunctor ⋙
        (proEtaleConstantRingPushforward A p).rightDerivedFunctor :=
  conjugateIsoEquiv
    (proEtaleRingDerivedAdjunction (j ≫ p) (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison (j ≫ p) A))
    ((proEtaleRingDerivedAdjunction p (proEtaleConstantRing Y A)
      (proEtaleConstantRing B A) (proEtaleConstantRingComparison p A)).comp
      (proEtaleRingDerivedAdjunction j (proEtaleConstantRing B A)
        (proEtaleConstantRing X A) (proEtaleConstantRingComparison j A)))
    (proEtaleConstantRingPullbackComposition j p A)

/-- The same canonical compositor after taking the product with `T`, transported by
`prod.map_comp_id` so its source uses exactly `(p ∘ j) × id_T`.
Source: blueprint order 3437, last endpoint identification; Stacks Tag 0E46
(blueprint: det-tf-ibc-pasting). -/
def compactificationProductDirectImageComposition (A : Type u) [CommRing A]
    {S : Scheme.{u}} {X B Y : Over S} (j : X ⟶ B) (p : B ⟶ Y) (T : Over S) :
    (proEtaleConstantRingPushforward A (prod.map (j ≫ p) (𝟙 T)).left).rightDerivedFunctor ≅
      (proEtaleConstantRingPushforward A (prod.map j (𝟙 T)).left).rightDerivedFunctor ⋙
        (proEtaleConstantRingPushforward A (prod.map p (𝟙 T)).left).rightDerivedFunctor :=
  eqToIso (congrArg
    (fun q : X ⨯ T ⟶ Y ⨯ T ↦ (proEtaleConstantRingPushforward A q.left).rightDerivedFunctor)
    (prod.map_comp_id j p)) ≪≫
      compactificationDirectImageComposition A (prod.map j (𝟙 T)).left
        (prod.map p (𝟙 T)).left

/-- Pasting through the supplied open/proper factorization identifies the specified
exchange map itself with the two factor exchanges, and both factors and the result
are invertible. We substitute `f = j ≫ p`, so no extra property of the intermediate
scheme or of the open immersion is assumed.
Source: blueprint order 3437, det-tf-ibc-pasting; Stacks Tag 0E46
(blueprint: det-tf-ibc-pasting).

Proof:
1. Properness makes p separated and finite type. Composition and the factorization
   of the diagonal make B separated of finite type over k. The qcqs-over-affine and
   qcqs permanence lemmas make j and j_T qcqs. The universal product identifications
   give the two Cartesian squares and their pasted square
   (lem-sfb-finite-type-composition-base-change, lem-weil-pbc-closed-immersion-base-change,
   lem-weil-pbc-closed-immersion-comp, lem-weil-pbc-qcqs-over-affine,
   lem-weil-pbc-qcqs-morphism-permanence, def-pc-fibre-product).
2. Choose a bounded constructible etale origin L of M using
   lem-weil-pbc-finite-ring-constructible-derived-origin. Open-image finiteness and
   qcqs comparison give Rj_*M bounded constructible, for the given finite ring A
   (cor-fin-deligne-open-finite-coefficients, sk-thm-pe-direct-image-comparison).
3. Normalize pullback composition by its sectionwise direct-image adjoint using
   lem-pur-proetale-module-pullback-composition and
   prop-weil-pbc-proetale-constant-ring-map. Ringed module categories are Grothendieck
   abelian (lem-pur-ringed-site-grothendieck-abelian); apply
   lem-sfb-derived-composition-adjunction-normalization to identify the conjugate
   compositors with the usual K-injective direct-image isomorphisms, units and counits.
4. The inverse-image square comparisons paste, by uniqueness of the fibre-product
   isomorphism preserving projections. The K-flat representative normalization of
   lem-weil-pbc-proetale-derived-pullback-composition descends this equality. Apply
   clauses (2) and (3) of lem-weil-pbc-mate-pasting and the definition
   def-weil-pbc-ambient-ringed-exchange; evaluation at M gives the displayed equality.
5. Apply det-geo-open-finiteness-base-change to j and L. Its exchange is the same
   counit transpose (sbc-def-base-change-map, def-weil-pbc-derived-exchange).
   The comparison equation of lem-weil-pbc-transport-identifies-exchange identifies
   this etale exchange with the pro-etale exchange, proving the open factor invertible.
   No smoothness of T is used.
6. Apply det-tf-ibc-proper-step to p and Rj_*M, bounded constructible by Step 2.
   It makes the proper factor invertible with the specified finite coefficients.
7. Functors preserve inverses. The equality in Step 4, the invertible factors in
   Steps 5 and 6, and the endpoint isomorphisms imply the final invertibility.
-/
theorem compactificationProductExchange_pasting
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) (_hl : l.Prime)
    (_hne : l ≠ ringChar D.k) (A : Type u) [CommRing A] [Finite A]
    (_hA : ∃ r : ℕ, 0 < r ∧ ((l ^ r : ℕ) : A) = 0)
    (X Y T : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (B : Over (Spec (.of D.k))) (j : X ⟶ B) [IsOpenImmersion j.left]
    (p : B ⟶ Y) [IsProper p.left] (M : proEtaleDerivedCategory X.left A)
    (_hM : (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} A) X.left) ⋙
      ProEtale.finiteCoefficientIntrinsicDerivedComparison X.left A).essImage M) :
    ((compactificationProductExchange A (j ≫ p) T).app M =
      (proEtaleConstantRingDerivedPullback A (prod.fst : Y ⨯ T ⟶ Y).left).map
        ((compactificationDirectImageComposition A j.left p.left).hom.app M) ≫
      (compactificationProductExchange A p T).app
        ((proEtaleConstantRingPushforward A j.left).rightDerivedFunctor.obj M) ≫
      (proEtaleConstantRingPushforward A (prod.map p (𝟙 T)).left).rightDerivedFunctor.map
        ((compactificationProductExchange A j T).app M) ≫
      (compactificationProductDirectImageComposition A j p T).inv.app
        ((proEtaleConstantRingDerivedPullback A (prod.fst : X ⨯ T ⟶ X).left).obj M)) ∧
    IsIso ((compactificationProductExchange A p T).app
      ((proEtaleConstantRingPushforward A j.left).rightDerivedFunctor.obj M)) ∧
    IsIso ((compactificationProductExchange A j T).app M) ∧
    IsIso ((compactificationProductExchange A (j ≫ p) T).app M) := by
  sorry

end AlgebraicGeometry.Scheme
