/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized
import Sheaf.RingTheory.WContractibleClosedLocalization
import Sheaf.AlgebraicGeometry.AffineClosedSpecializationLocalization
import Sheaf.AlgebraicGeometry.ProEtaleShriekSpecializationZero
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange

/-! Epimorphism half of the proper/open pro-etale counit support argument.

Source: Stacks, Tags 09AE and 09AG; blueprint
`lem-exc-proetale-proper-open-counit-isiso`.
(blueprint: lem-exc-proetale-proper-open-counit-isiso-epi)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

/-- The proper/open counit is epic; this is the surjectivity part of the
finite-principal-open and specialization-localization argument. -/
theorem sfProperOpenCounit_epi {V W T : Scheme.{u}} (p : V ⟶ T) [IsProper p]
    (i : W ⟶ T) [IsOpenImmersion i] (M :
      proEtaleRingModules (pullback p i)
        (proEtaleConstantRing (pullback p i) A)) :
    Epi ((sfIntrinsicExtensionByZeroAdjunction i A).counit.app
      ((sfIntrinsicExtensionByZero (pullback.fst p i) A ⋙
        proEtaleConstantModuleDirectImage p A).obj M)) := by
  sorry

end AlgebraicGeometry.Scheme
