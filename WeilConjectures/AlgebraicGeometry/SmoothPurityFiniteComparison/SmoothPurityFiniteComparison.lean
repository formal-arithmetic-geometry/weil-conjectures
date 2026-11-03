/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleProEtaleAdjunctionTransfer
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparisonMap
import all WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleProEtaleAdjunctionTransfer
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingCompactification
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonFaithful
import WeilConjectures.AlgebraicGeometry.FiniteAdmissibleComparison
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactifFiniteTor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude

/-! # Finite coefficients in the smooth-purity comparison

Source: latest blueprint, under literature/blueprint/latest/blueprint/:
part-six-operations/sec-six-functors-basics/sec-ctf-finite-foundations/
sk-prop-ctf-finite-comparison/sk-prop-sp-et-proet/_section.md and the adjacent
sk-prop-sp-et-proet.proof.md (blueprint: sk-prop-sp-et-proet).

The pro-etale categories below use the actual pulled-back condensed ring and finite
constant local models. The normalized encoding only expresses canonical comparison
maps in the ordinary constant-scalar presentation. All compact-support comparisons
use the same compactification on the two sites.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2000
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.SmoothPurityFiniteComparison

variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]

/-- The canonical full inclusion of Dctf in its native localizing closure.
Source: latest blueprint sk-prop-sp-et-proet, Brown compatibility clause
(blueprint: sk-prop-sp-et-proet). -/
def ctfToLocalizing (T : Scheme.{u}) :
    ConstantModelConstructibleFiniteTor (FiniteDiscreteOrdinary.coefficient A) T ⥤
      (localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) T).FullSubcategory :=
  ObjectProperty.ιOfLE (fun K hK _P _hP hgen ↦ hgen K hK)

/-- Restrict a native Brown right adjoint after its preservation of Dctf is known.
Source: latest blueprint sk-prop-sp-et-proet, second paragraph and its adjunction-transfer
proof step (blueprint: sk-prop-sp-et-proet). -/
def brownRestriction {X Y : Scheme.{u}}
    (J : (localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) Y).FullSubcategory ⥤
      (localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) X).FullSubcategory)
    (h : ∀ N : ConstantModelConstructibleFiniteTor (FiniteDiscreteOrdinary.coefficient A) Y,
      constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X
          (J.obj ((ctfToLocalizing A Y).obj N)).obj ∧
        _root_.DerivedCategory.finiteTorAmplitude _
          (J.obj ((ctfToLocalizing A Y).obj N)).obj) :
    ConstantModelConstructibleFiniteTor (FiniteDiscreteOrdinary.coefficient A) Y ⥤
      ConstantModelConstructibleFiniteTor (FiniteDiscreteOrdinary.coefficient A) X :=
  (constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X ⊓
    fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K).lift
      (ctfToLocalizing A Y ⋙ J ⋙
        (localizingClosureProEtale (FiniteDiscreteOrdinary.coefficient A) X).ι) h

omit [Finite A] [DiscreteTopology A] in
set_option maxHeartbeats 1600000 in
-- Elaborating the large record checks all canonical normalization and counit equations.
end AlgebraicGeometry.ProEtale.SmoothPurityFiniteComparison
