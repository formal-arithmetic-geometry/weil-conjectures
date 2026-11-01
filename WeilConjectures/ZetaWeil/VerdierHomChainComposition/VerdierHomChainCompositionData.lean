/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.PodCtfAdjunctionData.PodCtfAdjunctions
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
public import WeilConjectures.SmoothPurity.Supporting.ConstructibleIntervalsUnordered
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.Algebra.Field.Shrink
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SmoothPurity.Support.SupportScalarProjectionNormalization
public import WeilConjectures.SmoothPurity.Exceptional.ExceptionalSupportProjectionIso
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension
public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients

/-! # Coordinates for composition of the Verdier Hom chain

These are the existing canonical constructions, exposed independently of the composition
proof so that its two transpose calculations can be stated without an import cycle.
Source: fix-prop-coherence.proof.md, adjoint-mate sentence
(blueprint: def-sf-verdier-hom-composition-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

namespace WeilConjectures.VerdierHomChainComposition
open TensorHomCoefficientTransposes

variable {D : FiniteFieldDatum.{u}} {B : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic B.l) E]
  [FiniteDimensional (Padic B.l) E] {n : ℕ} {hn : 1 ≤ n}
  (S : SixFunctorOperationDatum D B E n hn) (s : PodCoefficientStage)

section OneMap
variable {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  (R : Domain S s f c)

end OneMap

section TwoMaps
variable {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
  [IsSeparated (f ≫ g).hom.left] [LocallyOfFiniteType (f ≫ g).hom.left]
  [QuasiCompact (f ≫ g).hom.left]
  (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
  (cx : Compactification (f ≫ g).hom.left)
  (Rf : Domain S s f cf) (Rg : Domain S s g cg) (Rx : Domain S s (f ≫ g) cx)

/-- Restrict the specified compact-support compositor through the full inclusion.
Source: proof steps 3--4 (blueprint: def-sf-verdier-hom-composition-coordinates). -/
def supportComposition : Rx.support ≅ Rf.support ⋙ Rg.support :=
  ((PodCoefficientStage.domain S s Z).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (PodCoefficientStage.domain S s X).ι
      ((PodCoefficientStage.operations S s).composition f g cf cg cx))

/-- Conjugate compact-support composition under the specified exceptional adjunctions.
Source: proof step 4 (blueprint: def-sf-verdier-hom-composition-coordinates). -/
def exceptionalComposition : Rx.exceptional ≅ Rg.exceptional ⋙ Rf.exceptional :=
  Rx.exceptionalAdjunction.rightAdjointUniq
    ((Rf.exceptionalAdjunction.comp Rg.exceptionalAdjunction).ofNatIsoLeft
      (supportComposition S s f g cf cg cx Rf Rg Rx).symm)

/-- The dualizing comparison for a composite in the same composition coordinates.
It is exceptional conjugation followed by f!c_g and c_f, without a new choice.
Source: proof step 5 (blueprint: def-sf-verdier-hom-composition-coordinates). -/
def dualizingComposition
    (OX : (PodCoefficientStage.domain S s X).FullSubcategory)
    (OY : (PodCoefficientStage.domain S s Y).FullSubcategory)
    (OZ : (PodCoefficientStage.domain S s Z).FullSubcategory)
    (df : Rf.exceptional.obj OY ≅ OX) (dg : Rg.exceptional.obj OZ ≅ OY) :
    Rx.exceptional.obj OZ ≅ OX :=
  (exceptionalComposition S s f g cf cg cx Rf Rg Rx).app OZ ≪≫
    Rf.exceptional.mapIso dg ≪≫ df

end TwoMaps

end WeilConjectures.VerdierHomChainComposition
