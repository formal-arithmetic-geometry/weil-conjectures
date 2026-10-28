/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations

/-! Sectionwise injectivity input for the proper/open counit.
(blueprint: lem-exc-proetale-proper-open-counit-mono-section)
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable (A : Type u) [CommRing A] [Finite A]

/-- After forgetting the ring action, the proper/open counit remains monic.
This is the sectionwise injectivity part of the affine proper/open support argument:
for every pro-etale object of the target, the zero-extension map is injective on
sections; exact sheafification and proper base change identify those maps with the
underlying presheaf map of the displayed counit. -/
theorem sfProperOpenCounit_forget_mono {V W T : Scheme.{u}} (p : V ⟶ T) [IsProper p]
    (i : W ⟶ T) [IsOpenImmersion i] (M :
      proEtaleRingModules (pullback p i)
        (proEtaleConstantRing (pullback p i) A)) :
    Mono ((SheafOfModules.forget
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing T A))).map
      ((sfIntrinsicExtensionByZeroAdjunction i A).counit.app
        ((sfIntrinsicExtensionByZero (pullback.fst p i) A ⋙
          proEtaleConstantModuleDirectImage p A).obj M))) := by
  sorry

end AlgebraicGeometry.Scheme
