/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z5
-/
module

public import Sheaf.CategoryTheory.RingedPresentationData

import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal

/-! # Auxiliary ringed presentation comparisons -/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- The module adjunction of a ringed equivalence is an equivalence, with its
underlying inverse image, structural rank-one map and forward internal Hom comparison.

Source: Stacks Project, sites-modules.tex, Tags 03CR and 03D7;
sites-cohomology.tex, Tags 07A4 and 08J9.
(blueprint: lem-weil-pbc-ringed-equivalence-module-hom).

Proof: transport the zero, addition, inverse and scalar-action maps along the
finite-product-preserving equivalence of set sheaves. Its unit and counit
commute with these operations, hence lift to linear isomorphisms. The specified
module direct image agrees with this lift: its generalized-element linearity
identity fixes its action, and the underlying natural comparison fixes its maps.
This gives the module equivalence and the displayed structural equation. Both
functors are additive and preserve all limits and colimits. Localizing their
termwise functors gives the unbounded derived equivalence. Tensor is preserved, since
transport preserves balanced bilinear maps. Apply the closed tensor-Hom
adjunction: maps C → F RHom(L,M) identify successively with maps G C → RHom(L,M),
G C tensor L → M, C tensor F L → F M, and C → RHom(F L,F M).
These identifications are natural in all three objects, so Yoneda produces the
required forward natural isomorphism. The reverse comparison is a formal
consequence of equivalence and is constructed in the parent proof. -/
theorem ringed_equivalence_module_hom
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    [e.inverse.IsEquivalence] [IsIso e.ringMap] :
    ∃ T : RingedPresentationEquivalenceCore S R,
      Nonempty (T.modules.inverse ≅ e.modules) ∧
      ∃ a : T.modules.functor ⋙ presentationForget R ≅
          presentationForget S ⋙ e.inverse,
        (presentationForget R).map T.forwardUnit.hom =
          a.hom.app (SheafOfModules.unit (localCoefficientRings S)) ≫ e.ringMap := by
  sorry

end CategoryTheory
