/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport

/-!
# The canonical open-square exchange in tensor-pullback coordinates

Source: main-20261015, `lem-trf-open-square-exchange`, construction by normalized mates;
Stacks Project, Tags 03S6 and 04J0 (blueprint: lem-trf-open-square-exchange).

The original exchange uses the transported fixed-scalar inverse image. The Frobenius
comparison uses tensor inverse image over the same intrinsic constant ring. The bridge
below is uniquely fixed by the sectionwise units, and is descended termwise.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The unique identification of the two pullbacks used in the open-square construction.
Its sectionwise equation preserves their specified units and fixes the scalar action.
Source: main-20261015, `lem-trf-open-square-exchange`, normalized-mate construction;
Stacks Tags 03S6, 03D3 and 00YV (blueprint: lem-trf-open-square-exchange).
Proof: both right adjoints evaluate a module on X ×_Y V, with scalar action from the
same constant-section map. The realization comparison is the identity on scalar-unit
sections and extends uniquely to locally constant scalars. Conjugate this sectionwise
comparison under the tensor-normalized and realization-normalized adjunctions. The
resulting mate is invertible and satisfies the displayed unit equation. Conversely that
equation determines its adjoint on every section, hence determines the mate uniquely. -/
theorem openSquarePullbackModel_existsUnique (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! e : proEtaleConstantRingPullback A f ≅ sfIntrinsicPullback A f,
      ∀ (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) (V : Y.ProEt)
        (s : M.val.obj (Opposite.op V)),
        (e.hom.app M).val.app (Opposite.op ((proEtaleBaseChange f).obj V))
            (((proEtaleConstantRingAdjunction A f).unit.app M).val.app (Opposite.op V) s) =
          ((sfIntrinsicConstantModuleAdjunction f A).unit.app M).val.app (Opposite.op V) s := by
  sorry

/-- The unique unit-preserving ordinary change of pullback coordinates.
Source: main-20261015, `lem-trf-open-square-exchange`, construction by mates
(blueprint: lem-trf-open-square-exchange). -/
def openSquarePullbackModel (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantRingPullback A f ≅ sfIntrinsicPullback A f :=
  (openSquarePullbackModel_existsUnique A f).exists.choose

/-- Exact termwise descent of the unit-preserving coordinate identification.
Source: main-20261015, `lem-trf-open-square-exchange`, derived construction
(blueprint: lem-trf-open-square-exchange). -/
def openSquareDerivedPullbackModel (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantRingDerivedPullback A f ≅ sfIntrinsicDerivedPullback A f :=
  Functor.mapDerivedCategoryNatIso (openSquarePullbackModel A f)

/-- The same canonical exchange in tensor-pullback coordinates. The middle comparison is
the existing exchange, whose inverse is the specified open-adjunction mate and whose
restriction, identity and pasting laws are recorded in SfOpenSquareExchangeData.
The two outer factors are the unique unit-preserving changes of coordinates; consequently
these normalizations transport with the exchange, including its identity on the open.
Source: main-20261015, `lem-trf-open-square-exchange`; Stacks Tags 03S6 and 04J0
(blueprint: lem-trf-open-square-exchange). -/
def constantOpenSquareExchange (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n)
    {U' U Y' Y : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ Y')
    (j : U ⟶ Y) (g : Y' ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback gU j' j g) :
    @sfIntrinsicDerivedOpen (Padic.coefficientExtensionRing l E n) _
        (Padic.finite_coefficientExtensionRing l E n hn) _ _ j _ ⋙
        proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n) g ≅
      proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n) gU ⋙
        @sfIntrinsicDerivedOpen (Padic.coefficientExtensionRing l E n) _
          (Padic.finite_coefficientExtensionRing l E n hn) _ _ j' _ := by
  letI := Padic.finite_coefficientExtensionRing l E n hn
  exact Functor.isoWhiskerLeft (sfIntrinsicDerivedOpen _ j)
      (openSquareDerivedPullbackModel _ g) ≪≫
    (Classical.choice (proEtale_openSquareExchange l E n hn)).exchange gU j' j g sq ≪≫
    Functor.isoWhiskerRight (openSquareDerivedPullbackModel _ gU).symm
      (sfIntrinsicDerivedOpen _ j')

end AlgebraicGeometry.Scheme
