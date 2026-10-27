/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C7
-/
module

public import Sheaf.Paper.LocallyFiniteAdicCompactSupportData

/-! # Finite-stage native compact-support scalar comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (P : CoefficientConstruction l (ULift.{u} (PadicAlgCl l)) D hl (f := f))
  (c : Compactification f)


/-- Realizations at the three schemes with one compatible family of coefficient maps.
Source: Bhatt--Scholze, Proposition 6.8.14, and normalized completion inclusions.
(blueprint: lem-sf-native-compact-support-finite-comparison). -/
structure CoefficientFamily [G : NativeGeometry.{u} l] where
  source : Realization l X
  target : Realization l Y
  middle : Realization l c.Z
  change : ∀ E : Index l (PadicAlgCl l),
    PurCompactSupport.Change (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l)
  change_source : ∀ E : Index l (PadicAlgCl l),
    (change E).map X = (source.coefficient E).integralMap l X
  change_target : ∀ E : Index l (PadicAlgCl l),
    (change E).map Y = (target.coefficient E).integralMap l Y
  change_middle : ∀ E : Index l (PadicAlgCl l),
    (change E).map c.Z = (middle.coefficient E).integralMap l c.Z

/-- Finite-stage comparisons, natural on rational arrows and compatible with stage changes.
Source: Bhatt--Scholze, Remark 6.8.15, and the proper/open scalar counit mate.
(blueprint: lem-sf-native-compact-support-finite-comparison). -/
structure FiniteComparison [G : NativeGeometry.{u} l]
    (stage : StageAction l D hl P c) (F : CoefficientFamily l c) where
  alpha : ∀ E : Index l (PadicAlgCl l),
    GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙
      stage.system.functor ⋙ F.target.J ≅
    GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ F.source.J ⋙ actual l c
  transition : ∀ (A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X)
      (E : Index l (PadicAlgCl l)) (h : A.stage ≤ E),
    (stage.system.functor ⋙ F.target.J).map
        ((StageSystem.isoToStage
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
          A h).hom) ≫ (alpha E).hom.app (A.toStage h) =
      (alpha A.stage).hom.app A.obj ≫ (F.source.J ⋙ actual l c).map
        ((StageSystem.isoToStage
          (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X) A h).hom)
  integral : ∀ (gamma : stage.system.functor ⋙ F.target.J ≅ F.source.J ⋙ actual l c),
    (∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
      HEq (gamma.hom.app A) ((alpha A.stage).hom.app A.obj)) →
    IntegralNormalization l D hl P c F.source F.target stage F.change gamma


/-- The proper/open scalar mate is invertible on finite rational constructible inputs.
Source: Bhatt--Scholze, Definition 6.7.6, Proposition 6.8.14 and Remark 6.8.15;
steps 1--10 of the native compact-support realization plan.
(blueprint: lem-sf-native-compact-support-finite-comparison).

Proof: choose normalized realizations of X, Y and Z as in the constructible realization
lemma. At every scheme the completed-integral coefficient map sends an integral function
to that same locally finite function, so it commutes with pullback. This gives change,
and its values on X, Y and Z agree with the chosen coefficient presentations.
For integral K first extend by zero. The open reduction comparison and uniform open
interval theorem show that this remains complete constructible. The stratified-perfect
characterization gives boundedness below, and integral residue Tor gives the uniform
finite-level Tor bounds. The integral compactification-system realization and completed
direct-image limit comparison identify the recorded integral operation with actual
proper image of this open extension, with its chosen quotient projections.
Apply localized direct-image comparison to this bounded-below open object, then the
bounded-push comparison from the finite coefficient field to the algebraic closure.
The flat coefficient associator and pasted-mates identity identify their composite with
the single proper scalar counit mate. Open scalar change is the K-flat tensor map
b tensor j_!m mapped to j_!(b restricted tensor m), which is invertible.
Compose these two maps and conjugate by the source and target integral realization
isomorphisms and operationTransport. The resulting component has exactly the original
six-arrow formula of
IntegralNormalization; every factor is invertible. Any comparison
whose components are these finite-stage components has this formula, giving integral.
Integral naturality extends to fractions by inverting the uniformizer scalar, giving
alpha E on the raw rational category. The prescribed P rationalLeft and scalar q identify
these maps with the recorded operation. The common-field normalizations of both
realizations, the P coefficient cocycle, finite-free completed scalar comparison and
pasted counit identities show compatibility with isoToStage: both composites send a
pure tensor b tensor a tensor m to ba tensor m. Thus transition holds on all rational
objects. The construction remains at finite stages; descent on arbitrary common-field
Hom classes and native constructibility preservation are separate arguments. -/
theorem native_compact_support_finite_comparison [G : NativeGeometry.{u} l]
    (stage : StageAction l D hl P c) :
    ∃ F : CoefficientFamily l c, Nonempty (FiniteComparison l D hl P c stage F) := by sorry

end WeilConjectures.LocallyFiniteAdicCompactSupport
