/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousModuleEncodingUniverses
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.Normed.Algebra.Basic
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare

/-! # Exact scalar extension under the universe-polymorphic section encodings

Source: Bhatt--Scholze, Lemma 6.8.2(2); Stacks Project, Tags 03EK and 03DA.
(blueprint: lem-weil-pbc-continuous-scalar-encoding-universes)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
attribute [local instance] Profinite.continuousMapRingObjOfUniverseMonObj
attribute [local instance] Profinite.isMonHom_continuousMapRingObjMapOfUniverse
attribute [local instance] Profinite.isCommMonObj_continuousMapRingObjOfUniverse
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The actual integral inclusion, transported through the canonical continuous charts.
Source: Bhatt--Scholze, Lemma 6.8.2(2).
(blueprint: lem-weil-pbc-continuous-scalar-encoding-universes). -/
def continuousInternalScalarMapUniverses (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :
    condensedRingObj (Profinite.continuousCoefficientRingObj
      (Padic.coefficientExtensionIntegers l E)) T ⟶
      condensedRingObj (Profinite.continuousCoefficientRingObj E) T := by
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  let : IsIso (ContinuousRingUniverse.comparison T E) :=
    ContinuousRingUniverse.comparison_isIso T E
  exact ContinuousRingUniverse.comparison T (Padic.coefficientExtensionIntegers l E) ≫
    (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        ((Scheme.adicLisseForget T).map
          (latticeCoefficientSheafMap T
            (Padic.coefficientExtensionIntegers l E).subtype continuous_subtype_val)) ≫
    inv (ContinuousRingUniverse.comparison T E)

set_option maxHeartbeats 800000 in
-- The chart and reconstructed section equivalences require a large definitional comparison.
end AlgebraicGeometry.ProEtale.CondensedRing
