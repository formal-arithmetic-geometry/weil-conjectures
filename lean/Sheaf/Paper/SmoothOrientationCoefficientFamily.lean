/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.FiniteCoefficientSmoothPurity
public import Sheaf.Paper.FiniteReductionComparisons
public import Sheaf.Paper.AdicPurityScalarNaturalityData
public import Sheaf.Paper.RationalSmoothPurityCanonical
public import Sheaf.Paper.SitePerfectComplex
public import Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Sheaf.Paper.PurAdicReconstruction

/-! # Site exchange comparisons under the smooth orientation

Source: latest blueprint, sec-six-functors/sk-thm-sf-package,
thm-pod-global-verdier-duality.proof.md, second paragraph
(blueprint: def-pod-smooth-orientation-coefficient-family).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

attribute [local instance 2000] IntermediateField.algebra'
attribute [local instance 2000] ConstructibleExceptionalCoefficients.category
attribute [local irreducible] CategoryTheory.Functor.mapIso CategoryTheory.Iso.trans

/-- The canonical smooth-purity isomorphism obtained from the recorded map and its
`isIso_smoothPurityMap` theorem.  Source: smooth purity orientation
(blueprint: def-pod-smooth-orientation-coefficient-family). -/
noncomputable def canonicalSmoothPurityIso
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :=
  letI := P.isIso_smoothPurityMap f d K hK
  (asIso (P.smoothPurityMap f d K hK))

/-- Transport an existing finite-Tor object along a specified actual isomorphism.
This is a constructor in the recorded full subcategory: the constructibility proof
is transported by iso closure, and the Tor witness is reindexed by composition
with that isomorphism. No new finiteness predicate is introduced.
Source: the intrinsic finite-Tor domain
(blueprint: def-pod-smooth-orientation-coefficient-family). -/
def smoothOrientationFiniteTorTransport (P : PurityFiniteSetting.{u}) (W : Scheme.{u})
    (V : finiteTorConstructibleCategory P.coefficients.l P.extension P.level P.level_pos W)
    (M : Scheme.proEtaleDerivedCategory W P.Ring) (e : V.obj ≅ M) :
    finiteTorConstructibleCategory P.coefficients.l P.extension P.level P.level_pos W :=
  ⟨M, by
    have : (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l
        P.extension P.level P.level_pos W).IsClosedUnderIsomorphisms :=
      (Scheme.proEtale_bounded_constructible_isTriangulated W P.Ring).1
    refine ⟨ObjectProperty.prop_of_iso _ e V.property.1, ?_⟩
    obtain ⟨a, b, ht⟩ := V.property.2
    refine ⟨a, b, ht.1, ?_⟩
    intro N L hN f hf hL Z j hj
    exact ht.2 N L (hN.map (fun z ↦ z ≪≫ e.symm)) f hf hL Z j hj⟩

/-- Literal coefficient stages inside the fixed closure of the purity conventions.
This indexes only the stipulated coefficients, retaining the actual finite subfield
needed to instantiate the published purity setting.
Source: coefficient list in the smooth-orientation comparison statement
(blueprint: def-pod-smooth-orientation-coefficient-family). -/
inductive SmoothOrientationCoefficient (P : PurityFiniteSetting.{u}) where
  | finite (E : AdicPurityScalarNaturality.Field P.field P.coefficients) (n : ℕ+)
  | integral (E : AdicPurityScalarNaturality.Field P.field P.coefficients)
  | rational (E : AdicPurityScalarNaturality.Field P.field P.coefficients)
  | closed

/-- The existing operation-stage index of a literal purity coefficient.
Source: coefficient stages of the six-functor datum
(blueprint: def-pod-smooth-orientation-coefficient-family). -/
def SmoothOrientationCoefficient.stage (P : PurityFiniteSetting.{u}) :
    SmoothOrientationCoefficient P → ConstructibleExceptionalCoefficients.Stage P.coefficients.l
  | .finite E n => .finite (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E) n
  | .integral E => .integral (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E)
  | .rational E => .rational (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E)
  | .closed => .closed

/-- The finite shifted twisted pullback in its recorded finite-Tor category.
The underlying object is literally `compositionShiftedPullback`; only its
membership proof is transported through the stipulated smooth purity isomorphism.
Source: finite smooth-purity domain
(blueprint: def-pod-smooth-orientation-coefficient-family). -/
def smoothFiniteOrientationSource
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (T : ConstructibleExceptionalCoefficients.System.{u, u} P.coefficients.l
      P.coefficients.Qbar P.field P.coefficients.different (f := f))
    (c : Compactification f)
    (E : AdicPurityScalarNaturality.Field P.field P.coefficients) (n : ℕ+)
    (U : finiteTorConstructibleCategory P.coefficients.l E.val n.val n.pos Y) :
    finiteTorConstructibleCategory P.coefficients.l E.val n.val n.pos X :=
  let PE : PurityFiniteSetting.{u} :=
    { P with
      extension := E.val
      finiteExtension := E.property
      level := n.val
      level_pos := n.pos }
  let e := canonicalSmoothPurityIso PE f d U.obj U.property ≪≫
    ((T.ring.finiteRight c (AdicPurityScalarNaturality.fieldStage
      P.field P.coefficients E) n).app U).symm
  let V := (T.ring.operation c (.finite
    (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E) n)).G.obj U
  smoothOrientationFiniteTorTransport PE X V
    ((PE.compositionShiftedPullback f d).obj U.obj) e.symm

/-- The stipulated purity map in the recorded operation category, at each coefficient
stage. At finite level this is literally `smoothPurityMap`, transported only by
`finiteRight`; the other branches are the normalized integral trace transpose and
its stipulated rational and common-stage realizations. Its source is the actual
shifted Tate-twisted pullback, never a freely chosen object isomorphic to omega.
Source: smooth purity conventions and normalized reconstruction
(blueprint: def-pod-smooth-orientation-coefficient-family). -/
def smoothOrientationAtStage
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (T : ConstructibleExceptionalCoefficients.System.{u, u} P.coefficients.l
      P.coefficients.Qbar P.field P.coefficients.different (f := f))
    (c : Compactification f)
    (s : SmoothOrientationCoefficient P)
    (U : ConstructibleExceptionalCoefficients.C.{u, u} P.coefficients.l
      P.coefficients.Qbar Y (s.stage P)) :
    Σ H : ConstructibleExceptionalCoefficients.C.{u, u} P.coefficients.l
      P.coefficients.Qbar X (s.stage P),
      H ≅ (T.ring.operation c (s.stage P)).G.obj U := by
  letI : ∀ x : X, Invertible (P.coefficients.l : X.residueField x) :=
    fun x ↦ (purAdicResidueUnit P.field P.coefficients X x).invertible
  letI : ∀ y : Y, Invertible (P.coefficients.l : Y.residueField y) :=
    fun y ↦ (purAdicResidueUnit P.field P.coefficients Y y).invertible
  match s, U with
  | .finite E n, U =>
    let PE : PurityFiniteSetting.{u} :=
      { P with
        extension := E.val
        finiteExtension := E.property
        level := n.val
        level_pos := n.pos }
    let e := canonicalSmoothPurityIso PE f d U.obj U.property ≪≫
      ((T.ring.finiteRight c (AdicPurityScalarNaturality.fieldStage
        P.field P.coefficients E) n).app U).symm
    let H := smoothFiniteOrientationSource P f d T c E n U
    exact ⟨H, ObjectProperty.isoMk _ e⟩
  | .integral E, U =>
    let PE : PurityFiniteSetting.{u} :=
      { P with extension := E.val, finiteExtension := E.property }
    exact ⟨RationalSmoothPurityCanonical.integralSource PE f d U,
      RationalSmoothPurityCanonical.integralIso PE f c T d U⟩
  | .rational E, U =>
    let PE : PurityFiniteSetting.{u} :=
      { P with extension := E.val, finiteExtension := E.property }
    exact ⟨_, RationalSmoothPurityCanonical.rationalIso PE f c T d U⟩
  | .closed, U =>
    exact ⟨_, RationalSmoothPurityCanonical.commonIso P f c T d U⟩

/-- The finite quotient scalar and the purity reduction are the same actual
coefficient map, including their positive-exponent casts. The induced functor iso
is transport along this equality, not a choice of scalar comparison.
Source: finite coefficient quotient construction
(blueprint: def-pod-smooth-orientation-coefficient-family). -/
def smoothFiniteScalarBridge (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (W : Scheme.{u}) :
    pbcDerivedExtend ((PurCompactSupport.finiteQuotientChange P.coefficients.l
      P.extension P.level m P.level_pos hm hmn).map W) ≅
      P.finiteReduction m hm hmn W := by
  have h (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ≤ n) :
      (PurCompactSupport.finiteQuotientChange P.coefficients.l P.extension
        n m hn hm hmn).map W =
      Scheme.proEtaleConstantRingMap (T := W)
        (Ideal.Quotient.factor (S := Padic.coefficientExtensionIdeal
          P.coefficients.l P.extension n)
          (T := Padic.coefficientExtensionIdeal P.coefficients.l P.extension m)
          (Ideal.pow_le_pow_right hmn)) := by
    cases n with
    | zero => exact False.elim (Nat.not_succ_le_zero 0 hn)
    | succ n =>
      cases m with
      | zero => exact False.elim (Nat.not_succ_le_zero 0 hm)
      | succ m => rfl
  exact eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ)
    (h P.level m P.level_pos hm hmn))

/-- The actual source comparison for a finite quotient, lifted through the full
finite-Tor inclusion. It is composed from scalar realization, the recorded
pullback/twist/shift comparison, and the coefficient-unit identification. No purity
map or inverse enters this construction.
Source: finite reduction comparisons at the coefficient unit
(blueprint: def-pod-smooth-orientation-coefficient-family). -/
@[irreducible] def smoothFiniteOrientationSourceComparison
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (T : ConstructibleExceptionalCoefficients.System.{u, u} P.coefficients.l
      P.coefficients.Qbar P.field P.coefficients.different (f := f))
    (c : Compactification f)
    (E : AdicPurityScalarNaturality.Field P.field P.coefficients)
    (n m : ℕ+) (hmn : (m : ℕ) ≤ n)
    (SX : ConstructibleExceptionalCoefficients.Scalar.{u, u} P.coefficients.l P.coefficients.Qbar
      (s := .finite (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E) n)
      (t := .finite (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E) m)
      (PurCompactSupport.finiteQuotientChange P.coefficients.l E.val
        n m n.pos m.pos hmn) X)
    (SY : ConstructibleExceptionalCoefficients.Scalar.{u, u} P.coefficients.l P.coefficients.Qbar
      (s := .finite (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E) n)
      (t := .finite (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E) m)
      (PurCompactSupport.finiteQuotientChange P.coefficients.l E.val
        n m n.pos m.pos hmn) Y)
    (Us : ConstructibleExceptionalCoefficients.C.{u, u} P.coefficients.l P.coefficients.Qbar
      Y (.finite (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E) n))
    (Ut : ConstructibleExceptionalCoefficients.C.{u, u} P.coefficients.l P.coefficients.Qbar
      Y (.finite (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E) m))
    (v : SY.functor.obj Us ≅ Ut) :
    SX.functor.obj (smoothFiniteOrientationSource P f d T c E n Us) ≅
      (smoothFiniteOrientationSource P f d T c E m Ut) := by
  let PE : PurityFiniteSetting.{u} :=
    { P with
      extension := E.val
      finiteExtension := E.property
      level := n.val
      level_pos := n.pos }
  let PM : PurityFiniteSetting.{u} :=
    { P with
      extension := E.val
      finiteExtension := E.property
      level := m.val
      level_pos := m.pos }
  let Hs := (smoothFiniteOrientationSource P f d T c E n Us)
  let uv := ((smoothFiniteScalarBridge PE m m.pos hmn Y).app Us.obj).symm ≪≫
    (SY.realization.app Us).symm ≪≫
    (finiteTorConstructible P.coefficients.l E.val m.val m.pos Y).ι.mapIso v
  exact ObjectProperty.isoMk _
    ((SX.realization.app Hs) ≪≫
      (smoothFiniteScalarBridge PE m m.pos hmn X).app Hs.obj ≪≫
      PE.finiteReductionSourceComparison m m.pos hmn f d Us.obj ≪≫
      (PM.compositionShiftedPullback f d).mapIso uv)

/-- The rational h_Q, built from the published tensor/line/shift/pullback
comparison and the scalar identification of the coefficient unit. Its construction
is independent of purity and internal Hom.
Source: rational scalar comparison identification
(blueprint: def-pod-smooth-orientation-coefficient-family). -/
@[irreducible] def smoothRationalOrientationSourceComparison
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (T : ConstructibleExceptionalCoefficients.System.{u, u} P.coefficients.l
      P.coefficients.Qbar P.field P.coefficients.different (f := f))
    (c : Compactification f)
    (E F : AdicPurityScalarNaturality.Field P.field P.coefficients)
    (i : E.val →ₐ[Padic P.coefficients.l] F.val)
    (Us : ConstructibleExceptionalCoefficients.C.{u, u} P.coefficients.l P.coefficients.Qbar
      Y (.rational (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E)))
    (Ut : ConstructibleExceptionalCoefficients.C.{u, u} P.coefficients.l P.coefficients.Qbar
      Y (.rational (AdicPurityScalarNaturality.fieldStage P.field P.coefficients F)))
    (v : (ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
      P.coefficients.Qbar
      (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E)
      (AdicPurityScalarNaturality.fieldStage P.field P.coefficients F) i Y).obj Us ≅ Ut) :
    (ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
      P.coefficients.Qbar
      (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E)
      (AdicPurityScalarNaturality.fieldStage P.field P.coefficients F) i X).obj
        (smoothOrientationAtStage P f d T c (.rational E) Us).1 ≅
      (smoothOrientationAtStage P f d T c (.rational F) Ut).1 := by
  letI : ∀ x : X, Invertible (P.coefficients.l : X.residueField x) :=
    fun x ↦ (purAdicResidueUnit P.field P.coefficients X x).invertible
  letI : ∀ y : Y, Invertible (P.coefficients.l : Y.residueField y) :=
    fun y ↦ (purAdicResidueUnit P.field P.coefficients Y y).invertible
  unfold smoothOrientationAtStage
  exact RationalSmoothPurityCanonical.sourceScalar P.coefficients.l E.val F.val
    i f d Us ≪≫
      (RationalSmoothPurityCanonical.rationalSource P.coefficients.l F.val f d).mapIso v

/-- The rationalization source comparison, with the stipulated localization/shift
comparison and the scalar coefficient-unit identification. This construction uses
no purity arrow.
Source: rational purity source comparison
(blueprint: def-pod-smooth-orientation-coefficient-family). -/
@[irreducible] def smoothRationalizationOrientationSourceComparison
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (T : ConstructibleExceptionalCoefficients.System.{u, u} P.coefficients.l
      P.coefficients.Qbar P.field P.coefficients.different (f := f))
    (c : Compactification f)
    (E : AdicPurityScalarNaturality.Field P.field P.coefficients)
    (Us : ConstructibleExceptionalCoefficients.C.{u, u} P.coefficients.l P.coefficients.Qbar
      Y (.integral (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E)))
    (Ut : ConstructibleExceptionalCoefficients.C.{u, u} P.coefficients.l P.coefficients.Qbar
      Y (.rational (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E)))
    (v : (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l
      P.coefficients.Qbar
      (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E) Y).obj Us ≅ Ut) :
    (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l
      P.coefficients.Qbar
      (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E) X).obj
        (smoothOrientationAtStage P f d T c (.integral E) Us).1 ≅
      (smoothOrientationAtStage P f d T c (.rational E) Ut).1 := by
  letI : ∀ x : X, Invertible (P.coefficients.l : X.residueField x) :=
    fun x ↦ (purAdicResidueUnit P.field P.coefficients X x).invertible
  letI : ∀ y : Y, Invertible (P.coefficients.l : Y.residueField y) :=
    fun y ↦ (purAdicResidueUnit P.field P.coefficients Y y).invertible
  let PE : PurityFiniteSetting.{u} :=
    { P with extension := E.val, finiteExtension := E.property }
  unfold smoothOrientationAtStage
  exact (RationalSmoothPurityCanonical.rationalSourceComparison PE f d
    ((ConstructibleExceptionalCoefficients.rationalization P.coefficients.l
      P.coefficients.Qbar
      (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E) Y).obj Us)).symm ≪≫
      (RationalSmoothPurityCanonical.rationalSource P.coefficients.l E.val f d).mapIso v

/-- Site-perfectness at the four recorded coefficient kinds. Positive finite
levels are matched as successors so this uses exactly the recorded finite predicate,
whose natural-number parameter is the exponent minus one.
Source: site-perfect coefficient conventions
(blueprint: def-pod-smooth-orientation-coefficient-family). -/
@[irreducible] def smoothOrientationSitePerfect
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (X : Scheme.{u}) :
    (s : ConstructibleExceptionalCoefficients.Stage.{u} l) →
      ConstructibleExceptionalCoefficients.C.{u, u} l Ω X s → Prop
  | .finite _ ⟨0, h⟩, _ => (Nat.not_lt_zero 0 h).elim
  | .finite E ⟨n + 1, _⟩, K => IsFiniteCoefficientSitePerfect l E.carrier X n K.obj
  | .integral E, K => IsIntegralCoefficientSitePerfect l E.carrier X K.obj
  | .rational E, K => IsSfRationalCoefficientSitePerfect l E.carrier X K
  | .closed, K => IsGeneralAlgebraicallyClosedCoefficientSitePerfect l Ω X K

/-- The actual positive-quotient scalar functor on the existing finite-Tor domains.
Membership is the reduction component of the uniform finite-Tor predicate.
Source: adic reconstruction, coefficient reductions
(blueprint: def-pod-smooth-orientation-coefficient-family). -/
def smoothIntegralOrientationReduction (P : PurityFiniteSetting.{u})
    (E : AdicPurityScalarNaturality.Field P.field P.coefficients)
    (W : Scheme.{u}) (n : ℕ) :
    finiteTorConstructibleIntegralCategory P.coefficients.l E.val W ⥤
      finiteTorConstructibleCategory P.coefficients.l E.val (n + 1) (Nat.succ_pos n) W :=
  (finiteTorConstructible P.coefficients.l E.val (n + 1) (Nat.succ_pos n) W).lift
    ((finiteTorConstructibleIntegral P.coefficients.l E.val W).ι ⋙
      scalarReductionDerivedExtension P.coefficients.l E.val W n)
    (fun K ↦ purAdicReductionFiniteTor P.field P.coefficients E.val W K.obj K.property n)

/-- The inverse of the finite reduction purity square, using the recorded
inverse of the stipulated smooth-purity map and the actual source and exceptional
comparison arrows. Source: finite reduction of smooth purity, inverse square
(blueprint: def-pod-smooth-orientation-coefficient-family). -/
@[irreducible] def canonicalFiniteInversePuritySquare
    (P : PurityFiniteSetting.{u}) {X : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    (aX : X ⟶ Spec (.of P.field.k))
    [aX.IsOver (Spec (.of P.field.k))]
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (d : ℕ) [SmoothOfRelativeDimension d aX]
    (L : Scheme.proEtaleDerivedCategory (Spec (.of P.field.k)) P.Ring)
    (hL : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (Spec (.of P.field.k)) L)
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) : Prop :=
  let e := P.finiteReductionExceptionalComparison m hm hmn aX d L hL
  let γ := P.smoothPurityMap aX d L hL
  let γ' := (P.finiteReductionSetting m hm).smoothPurityMap aX d
    ((P.finiteReduction m hm hmn (Spec (.of P.field.k))).obj L)
    (P.finiteReduction_preserves_ctf m hm hmn (Spec (.of P.field.k)) L hL)
  let q := P.finiteReductionSourceComparison m hm hmn aX d L
  letI : IsIso γ := P.isIso_smoothPurityMap aX d L hL
  letI : IsIso γ' := by
    exact (P.finiteReductionSetting m hm).isIso_smoothPurityMap aX d
      ((P.finiteReduction m hm hmn (Spec (.of P.field.k))).obj L)
      (P.finiteReduction_preserves_ctf m hm hmn (Spec (.of P.field.k)) L hL)
  (P.finiteReduction m hm hmn X).map (asIso γ).inv ≫ q.hom =
    e ≫ (asIso γ').inv

end WeilConjectures
