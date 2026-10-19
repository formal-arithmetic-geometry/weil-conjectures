/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Paper.ZlOpenDiagramComparisonTransport

import Sheaf.CategoryTheory.FlatRingedDiagramRestriction
import Sheaf.Paper.CompletedCoefficientPushforwardComparison
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
import Sheaf.Paper.AdicPullbackPresentationTransport
import Sheaf.CategoryTheory.RingedCoefficientRestrictionCounit
import Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.CompleteProetaleStrictTowerRealization
import Sheaf.Paper.CompletedCoefficientPresentationTransport
import Sheaf.Paper.CompletedCompactSupportExchange
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.CompletedOpenExchangeTransport
import Sheaf.Paper.CompletedRlimFunctor
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.ExactProductFunctorStrictLimit
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.IntegralCompactSupportUniformRestriction
import Sheaf.Paper.IntegralPullbackComparisonRealization
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.IntegralUniformCoefficient
import Sheaf.Paper.KoszulReconstruction
import Sheaf.Paper.PbcQbarCompletedPullback
import Sheaf.Paper.PbcScalarExtension
import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.Paper.RationalCoefficientCategoryComparison
import Sheaf.Paper.SfWeilSheafComplex

/-! # Framework and PBC open exchange comparison
Source: thm-cbc-qbar.proof.md, common-stage descent
(blueprint: lem-zl-framework-pbc-open-exchange-comparison).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ZlFrameworkPbc
open PurCompactSupport

/-- The integral, raw rational and common-stage ordered exchange squares commute for
one simultaneous coefficient-presentation comparison, on every allowed open diagram.

Source: blueprint main-20261015, thm-cbc-qbar.proof.md, common-stage descent
(blueprint: lem-zl-framework-pbc-open-exchange-comparison).
Proof: identify the full integral constructible categories using the specified completed
coefficient isomorphism, whose projections preserve the actual quotient transitions.
Restriction along it preserves the whole diagram adjunctions. The open tensor comparison
identifies the entire quotient tower of j!K with j! of the quotient tower. Its completed
reconstruction and the canonical proper-direct-image/derived-limit comparison give b.
For a use the same simultaneous flat-term K-flat representative and the identity of
its entire pulled-back quotient diagram. The quotient augmentation and zero shifted
Roos coordinate fix this map and its completion unit. The framework exchange is the
proper diagram mate followed by the open unit-mate on this same diagram. The strict
realization theorem identifies precisely the ordered PBC arrow with its total-limit
image. The source and target comparisons are respectively S and T, so their endpoint
calculation gives the displayed integral equality. All operations restrict to the full
constructible categories by integral uniform restriction. Scalar restriction along a
finite coefficient extension preserves both mates on whole diagrams; the balanced tensor
associators give the mixed beta equation and its identity and successive-field laws.
Localize the integral maps on pure tensors to obtain the finite maps and their equation.
The beta equation descends those actual maps to the pair quotient. Every arrow has a
common-stage representative, so the finite equations yield the common-stage equality.
No faithfulness of separately evaluated reductions and no invertibility of the exchange
is used. Empty opens, zero inputs, repeated stages and identity open restrictions use
the same unit-normalized maps. -/
theorem openExchangeComparison (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] :
    ∃ S : FdCoefficientComparisonSystem.{u} l Ω,
      ∃ N : PullSystem l Ω S,
      FdComparisonSchemeCoherence l Ω S ∧
      ∀ G : OpenDiagram D l,
      (G.u.IsOver (Spec (.of D.k)) ∧ G.v.IsOver (Spec (.of D.k))) ∨
        (IsIso G.u ∧ IsIso G.v) →
      ∃ Q : SquarePacket D l hl Ω G S,
        (∀ E, (Q.data.integral E).pullV = N.comparison G.v E ∧
          (Q.data.integral E).pullU = N.comparison G.u E) ∧
        (∀ E, (Q.data.integral E).comparisons.Commutes
          (Q.data.integral E).sfExchange (Q.data.integral E).pbcExchange) ∧
        (∀ E, (Q.data.finiteComparisons E).Commutes
          (Q.data.sfExchange.τ E) (Q.data.pbcExchange.τ E)) ∧
        Q.data.pairComparisons.Commutes Q.data.sfPairExchange Q.data.pbcPairExchange := by
  sorry

/-- Naturality under an isomorphism of the entire compactification/open diagram,
including semilinear isomorphisms. The four corner actions are the actual scheme
pullbacks; support transport is the same ordered exchange along the corner isomorphisms.
Both integral and coefficient-family naturality are equalities of actual maps.

Source: thm-cbc-qbar.proof.md, common-stage descent and naturality of ordered mates
(blueprint: lem-zl-framework-pbc-open-exchange-comparison).
Proof: move every diagram operation through the corner scheme isomorphisms using
the coefficient-normalized inverse-image compositors. The proper comparison is
its adjunction mate, and the open comparison is the inverse open unit-mate.
The triangle identities identify the two paths on the whole strict diagram.
The diagram isomorphism commutes with the middle arrow, so the resulting proper
and open factors occur in the same order. Apply the canonical derived inverse
limit and its source/target comparisons. This proves the two integral naturality
squares. Scalar restriction preserves these units and counits, and the balanced
associators commute with the same strict maps. Localizing gives the four mixed
families and both finite naturality equalities. Descending their actual compatible
maps with the specified pair-composition isomorphisms gives the two common-stage
naturality equalities. Scheme isomorphisms are not required to be linear over k. -/
theorem diagramNaturality (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] (S : FdCoefficientComparisonSystem.{u} l Ω)
    {G H : OpenDiagram D l} (I : DiagramIso G H)
    (Q : SquarePacket D l hl Ω G S) (R : SquarePacket D l hl Ω H S)
    (T : SquarePacket D l hl Ω I.supportGeometry S)
    (T' : SquarePacket D l hl Ω I.supportGeometry' S) :
    ∃ N : DiagramComparisons D l hl Ω S I Q R T T',
      (∀ E, (N.integralSf E).Commutes
        (Q.data.integral E).sfExchange (R.data.integral E).sfExchange) ∧
      (∀ E, (N.integralPbc E).Commutes
        (Q.data.integral E).pbcExchange (R.data.integral E).pbcExchange) ∧
      (∀ E, (N.finiteSf E).Commutes (Q.data.sfExchange.τ E) (R.data.sfExchange.τ E)) ∧
      (∀ E, (N.finitePbc E).Commutes (Q.data.pbcExchange.τ E) (R.data.pbcExchange.τ E)) ∧
      N.pairSf.Commutes Q.data.sfPairExchange R.data.sfPairExchange ∧
      N.pairPbc.Commutes Q.data.pbcPairExchange R.data.pbcPairExchange := by
  sorry

/-- Identity and successive restriction for the actual framework arrows on the
chosen geometric open diagrams, with the published whole-system unit and compositor.
Source: thm-cbc-qbar.proof.md, identity and iterated restriction
(blueprint: lem-zl-framework-pbc-open-exchange-comparison).
Proof: transpose the proper factors under their composite adjunctions. Their
units and counits give the identity mate and the mate of the pasted square.
Transpose the inverse open factors under openDerivedAdjunction: the identity
transpose is its unit and successive transposes give its composite unit. Hence
the actual proper/open maps agree before localization. The whole quotient-unit
pullback realization and the projection-normalized support realization preserve
these equations on both Roos coordinates. Apply total derived limit and cancel
only those canonical endpoint isomorphisms. IntegralComparisonUnit and
IntegralComparisonComposition are the same whole-system unit and compositor,
so the resulting endpoint equations are exactly those below. Scalar-localization
and the compatible StageSystem descent preserve these equations. -/
theorem frameworkOpenRestrictionCoherence (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (R : IntegralComparisonSystem.{u} l) (G : OpenDiagram D l) :
    (∀ K : sfIntegralConstructibleCategory l E G.X,
      frameworkExchange l E D G.identity hl K ≫
        ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
          G.c E).map (ObjectProperty.homMk
            (integralComparisonUnit l E R G.X K).hom)).hom =
      (integralComparisonUnit l E R G.Y
        ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
          G.c E).obj K)).hom) ∧
    (∀ (H : FurtherOpen G) (K : sfIntegralConstructibleCategory l E G.X),
      (integralComparisonComposition l E R H.v G.v
        ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
          G.c E).obj K)).hom ≫
        (integralDerivedPullback l E H.v).map (frameworkExchange l E D G hl K) ≫
        frameworkExchange l E D H.second hl
          ((constructibleIntegralPullback l E G.u).obj K) =
      frameworkExchange l E D H.outer hl K ≫
        ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
          H.c E).map (ObjectProperty.homMk
            (integralComparisonComposition l E R H.u G.u K).hom)).hom) := by
  sorry

/-- Geometric Frobenius transported through the specified geometric-fibre equality.
Source: Deligne Weil II 1.1.7; thm-cbc-qbar.proof.md, Weil compatibility
(blueprint: lem-zl-framework-pbc-open-exchange-comparison). -/
def descendedFrobenius (D : FiniteFieldDatum.{u})
    (W₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
    {W : Scheme.{u}} (h : W = (D.geometricFiber W₀).left) : W ≅ W :=
  eqToIso h ≪≫ D.geometricFrobenius W₀ ≪≫ (eqToIso h).symm

/-- The actual geometric-Frobenius support comparison lifts to Weil fixed pairs.
The support action is the packet's rebuilt exchange, and the underlying lifted map
is its specified b. Frobenius and every PBC action are fixed in the statement.
Source: thm-cbc-qbar.proof.md, Weil compatibility; Weil II 1.1.7
(blueprint: lem-zl-framework-pbc-open-exchange-comparison).
Proof: the descended Frobenius commutes with the entire compactification diagram.
The proper/open isomorphism exchange is invertible by the adjunction triangle
identities, with no absolute separatedness. Apply the integral comparison to this
actual diagram and localize the normalized maps. Its pullback comparisons agree
with the simultaneous scheme-isomorphism comparisons by PullSystem.isomorphism.
Thus b intertwines the two Frobenius structure maps. The same equation makes b
and its inverse maps of fixed pairs, naturally on all intertwining arrows. The
IsoAlgebra constructor gives the displayed natural isomorphism with underlying b.
For common-stage pairs descend these exact compatible maps, retaining the beta
associators; do not choose new actions after passage to the quotient. -/
theorem frobeniusWeilSupportComparison (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (G : OpenDiagram D l) (X₀ Y₀ T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (hX : G.X = (D.geometricFiber X₀).left)
    (hY : G.Y = (D.geometricFiber Y₀).left)
    (hT : G.c.Z = (D.geometricFiber T₀).left)
    (sp : ChosenCartesianSquare (descendedFrobenius D T₀ hT).hom G.c.g G.c.g
      (descendedFrobenius D Y₀ hY).hom)
    (sj : OpenImmersionSquare (descendedFrobenius D X₀ hX).hom G.c.i G.c.i
      (descendedFrobenius D T₀ hT).hom)
    (S : FdCoefficientComparisonSystem.{u} l Ω) (N : PullSystem l Ω S)
    (Q : SquarePacket D l hl Ω (G.automorphism
      (descendedFrobenius D X₀ hX) (descendedFrobenius D Y₀ hY)
      (descendedFrobenius D T₀ hT) sp sj) S)
    (_pull : ∀ L, (Q.data.integral L).pullU =
      N.comparison (descendedFrobenius D X₀ hX).hom L ∧
      (Q.data.integral L).pullV = N.comparison (descendedFrobenius D Y₀ hY).hom L)
    (E : Padic.FiniteCoefficientFields l Ω) :
    HEq (Q.data.sfP'.system.Φ E) (sfWeilFrobeniusPullback D l hl X₀ (pbcFiniteField.{u} l Ω E)) ∧
    HEq (Q.data.sfP.system.Φ E) (sfWeilFrobeniusPullback D l hl Y₀ (pbcFiniteField.{u} l Ω E)) ∧
    ZlExchange.HasExchangeFixedPairSupportLift
      (Q.data.finiteComparisons E).b (Q.data.finiteComparisons E).a'
      (Q.data.finiteComparisons E).a (Q.data.sfExchange.τ E) (Q.data.pbcExchange.τ E) := by
  sorry

/-- The actual geometric-Frobenius support comparison lifts to Weil fixed pairs.
The support action is the packet's rebuilt exchange, and the underlying lifted map
is its specified b. Frobenius and every PBC action are fixed in the statement.
Source: thm-cbc-qbar.proof.md, Weil compatibility; Weil II 1.1.7
(blueprint: lem-zl-framework-pbc-open-exchange-comparison).
Proof: the descended Frobenius commutes with the entire compactification diagram.
The proper/open isomorphism exchange is invertible by the adjunction triangle
identities, with no absolute separatedness. Apply the integral comparison to this
actual diagram and localize the normalized maps. Its pullback comparisons agree
with the simultaneous scheme-isomorphism comparisons by PullSystem.isomorphism.
Thus b intertwines the two Frobenius structure maps. The same equation makes b
and its inverse maps of fixed pairs, naturally on all intertwining arrows. The
IsoAlgebra constructor gives the displayed natural isomorphism with underlying b.
For common-stage pairs descend these exact compatible maps, retaining the beta
associators; do not choose new actions after passage to the quotient. -/
theorem frobeniusWeilSupportComparisonPair (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (G : OpenDiagram D l) (X₀ Y₀ T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (hX : G.X = (D.geometricFiber X₀).left)
    (hY : G.Y = (D.geometricFiber Y₀).left)
    (hT : G.c.Z = (D.geometricFiber T₀).left)
    (sp : ChosenCartesianSquare (descendedFrobenius D T₀ hT).hom G.c.g G.c.g
      (descendedFrobenius D Y₀ hY).hom)
    (sj : OpenImmersionSquare (descendedFrobenius D X₀ hX).hom G.c.i G.c.i
      (descendedFrobenius D T₀ hT).hom)
    (S : FdCoefficientComparisonSystem.{u} l Ω) (N : PullSystem l Ω S)
    (Q : SquarePacket D l hl Ω (G.automorphism
      (descendedFrobenius D X₀ hX) (descendedFrobenius D Y₀ hY)
      (descendedFrobenius D T₀ hT) sp sj) S)
    (_pull : ∀ L, (Q.data.integral L).pullU =
      N.comparison (descendedFrobenius D X₀ hX).hom L ∧
      (Q.data.integral L).pullV = N.comparison (descendedFrobenius D Y₀ hY).hom L) :
    HEq (Q.data.sfP'.system.functor) (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω) ∧
    HEq (Q.data.sfP.system.functor) (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω) ∧
    ZlExchange.HasExchangeFixedPairSupportLift
      Q.data.pairComparisons.b Q.data.pairComparisons.a' Q.data.pairComparisons.a
      Q.data.sfPairExchange Q.data.pbcPairExchange := by
  sorry

end WeilConjectures.ZlFrameworkPbc

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
namespace WeilConjectures.ZlExchange

/-- The comparison square identifies the induced fixed-pair structures, including
geometric-Frobenius Weil structures. The lifted natural isomorphism has exactly b
as its underlying map, on every input and every intertwining arrow.

For geometric fibres take the actions to be sfWeilFrobeniusPullback and the recorded
PBC completed Frobenius pullback. Their fixed pairs are precisely sfWeilComplex
and its common-stage analogue. The canonical support actions are the isomorphism
specializations of the ordered exchanges, covered by diagramNaturality.
Source: thm-cbc-qbar.proof.md, Weil compatibility; definition of Weil complexes
(blueprint: lem-zl-framework-pbc-open-exchange-comparison).
Proof: map a fixed pair by the canonical inverse pullback comparison followed by
J of its structure isomorphism. For compact support use its ordered-exchange
isomorphism followed by compact support of the original structure map. The given
comparison-square equation says exactly that b intertwines these two structure
maps. IsoAlgebra.isoMk therefore lifts b and its inverse. Naturality is naturality
of b on the underlying category; the forgetful functor is faithful. Thus its
components are the stipulated b maps and the arrow map is unchanged. -/
theorem fixedPairSupportComparison
    {CX : Type u₁} {CY : Type u₂} {PX : Type u₃} {PY : Type u₄}
    [Category.{v₁} CX] [Category.{v₂} CY] [Category.{v₃} PX] [Category.{v₄} PY]
    (JX : CX ⥤ PX) (JY : CY ⥤ PY) (F : CX ⥤ CY) (G : PX ⥤ PY)
    (φX : CX ⥤ CX) (φY : CY ⥤ CY) (ψX : PX ⥤ PX) (ψY : PY ⥤ PY)
    (b : F ⋙ JY ≅ JX ⋙ G)
    (aX : φX ⋙ JX ≅ JX ⋙ ψX) (aY : φY ⋙ JY ≅ JY ⋙ ψY)
    (e : F ⋙ φY ≅ φX ⋙ F) (e' : G ⋙ ψY ≅ ψX ⋙ G)
    (_h : ∀ K : CX,
      aY.hom.app (F.obj K) ≫ ψY.map (b.hom.app K) ≫ e'.hom.app (JX.obj K) =
        JY.map (e.hom.app K) ≫ b.hom.app (φX.obj K) ≫ G.map (aX.hom.app K)) :
    ∃ t : CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso e ⋙
        CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso aY.symm ≅
      CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso aX.symm ⋙
        CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso e',
      ∀ K, (t.hom.app K).hom.f = b.hom.app K.carrier := by
  sorry


/-- Comparison squares paste with the canonical functor associators. Applied to two
successive open restrictions, the middle support comparison is the same normalized
b, and PullSystem.composition identifies the pasted pullback comparison with that
of the composite. Strict-tower mate pasting identifies the displayed pasted arrows
with the ordered arrows for the composite restriction. The identity instance uses
PullSystem.identity and the identity mate normalizations.

Source: thm-cbc-qbar.proof.md, common-stage descent, step 9
(blueprint: lem-zl-framework-pbc-open-exchange-comparison).
Proof: expand the two endpoint comparisons and the two pasted exchanges. Move the
second pullback comparison through the first exchange by naturality. Substitute
the first comparison-square equation, move the middle support comparison through
the second exchange, and substitute the second comparison-square equation. The
two occurrences of the middle b coincide. Functoriality and the pentagon identity
identify the resulting source and target with the displayed associator-normalized
ones. For actual open restrictions the proper mate-pasting identities and the open
unit-mate composition law identify these pasted strict arrows with the composite
arrow. Proper/limit and open/Roos endpoint comparisons compose by their product
projections, so total derived limit preserves that identification. Localization and
common-stage descent preserve this finite equality with the specified associators. -/
theorem pastedExchangeComparison
    {CX CY CU CV CW CZ PX PY PU PV PW PZ : Type u₁}
    [Category.{v₁} CX] [Category.{v₁} CY] [Category.{v₁} CU] [Category.{v₁} CV]
    [Category.{v₁} CW] [Category.{v₁} CZ] [Category.{v₁} PX] [Category.{v₁} PY]
    [Category.{v₁} PU] [Category.{v₁} PV] [Category.{v₁} PW] [Category.{v₁} PZ]
    (JX : CX ⥤ PX) (JY : CY ⥤ PY) (JU : CU ⥤ PU) (JV : CV ⥤ PV)
    (JW : CW ⥤ PW) (JZ : CZ ⥤ PZ)
    (F : CX ⥤ CY) (F' : CU ⥤ CV) (F'' : CW ⥤ CZ)
    (P : CY ⥤ CV) (P' : CX ⥤ CU) (R : CV ⥤ CZ) (R' : CU ⥤ CW)
    (G : PX ⥤ PY) (G' : PU ⥤ PV) (G'' : PW ⥤ PZ)
    (Q : PY ⥤ PV) (Q' : PX ⥤ PU) (T : PV ⥤ PZ) (T' : PU ⥤ PW)
    (C : Comparisons JX JY JU JV F F' P P' G G' Q Q')
    (D : Comparisons JU JV JW JZ F' F'' R R' G' G'' T T')
    (_middle : C.b' = D.b)
    (e : F ⋙ P ⟶ P' ⋙ F') (e' : G ⋙ Q ⟶ Q' ⋙ G')
    (d : F' ⋙ R ⟶ R' ⋙ F'') (d' : G' ⋙ T ⟶ T' ⋙ G'')
    (_first : C.Commutes e e') (_second : D.Commutes d d') :
    ({
      b := C.b
      b' := D.b'
      a := Functor.associator P R JZ ≪≫ Functor.isoWhiskerLeft P D.a ≪≫
        (Functor.associator P JV T).symm ≪≫ Functor.isoWhiskerRight C.a T ≪≫
        Functor.associator JY Q T
      a' := Functor.associator P' R' JW ≪≫ Functor.isoWhiskerLeft P' D.a' ≪≫
        (Functor.associator P' JU T').symm ≪≫ Functor.isoWhiskerRight C.a' T' ≪≫
        Functor.associator JX Q' T' } :
      Comparisons JX JY JW JZ F F'' (P ⋙ R) (P' ⋙ R')
        G G'' (Q ⋙ T) (Q' ⋙ T')).Commutes
      ((Functor.associator F P R).inv ≫ Functor.whiskerRight e R ≫
        (Functor.associator P' F' R).hom ≫ Functor.whiskerLeft P' d ≫
        (Functor.associator P' R' F'').inv)
      ((Functor.associator G Q T).inv ≫ Functor.whiskerRight e' T ≫
        (Functor.associator Q' G' T).hom ≫ Functor.whiskerLeft Q' d' ≫
        (Functor.associator Q' T' G'').inv) := by
  sorry

end WeilConjectures.ZlExchange
