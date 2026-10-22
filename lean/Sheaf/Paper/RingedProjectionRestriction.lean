/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.Paper.RingedProjectionRestrictionData
import Sheaf.Paper.RingedProjectionGlobalModel
import Sheaf.Paper.RingedProjectionLocalModel
import Sheaf.Paper.RingedRestrictionLocalIso

/-! # Canonical localization comparisons for the projection mate

Source: Stacks Project, Tags 04J0, 08FI, 07A4, 0B56 and 0944.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme
open ProjectionRestriction
/-- Canonical localization comparisons for the projection mate on ringed pro-etale sites.
Source: Stacks 04J0, 08FI, 0FN5, 07A4, 0B56 and 0944
(blueprint: lem-weil-pbc-ringed-projection-restriction).

Proof: construct the normalized global package using globalModel_exists. For every
object V choose the compatible localized package from localModel_exists. These
choices provide the two existential witnesses and the projection equation.
For local detection apply ringedRestrictionLocalIso to the underlying ring sheaf.
The restriction model is exactly overFunctor.mapDerivedCategory: its additivity
and exactness proofs agree with those in the generic construction by proof
irrelevance. The assumed covering sieves therefore give the generic hypotheses.
Exact restriction commutes with all integer cohomology functors, sheaf gluing
makes their global maps invertible, and the unbounded cohomology criterion
concludes. No boundedness or quasi-compactness hypothesis occurs. -/
theorem ringedProjectionRestriction
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X) :
    ∃ g : Global f R_Y R_X c,
      ∃ data : ∀ V : Y.ProEt, Local f R_Y R_X c g V,
        (∀ V : Y.ProEt, (data V).ProjectionCompatible) ∧
        (∀ {A B : Der R_Y} (a : A ⟶ B),
          (∀ V : Y.ProEt, ∃ S : Sieve V, S ∈ ProEt.topology Y V ∧
            ∀ (W : Y.ProEt) (h : W ⟶ V), S.arrows h →
              IsIso (((data W).restrictionY.model).functor.map a)) → IsIso a) := by
  classical
  obtain ⟨g⟩ := ProjectionRestriction.globalModel_exists f R_Y R_X c
  have hl := fun V ↦ ProjectionRestriction.localModel_exists f R_Y R_X c g V
  choose data hd using hl
  refine ⟨g, data, hd, ?_⟩
  intro A B a ha
  apply SheafOfModules.ringedRestrictionLocalIso
    ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y) a
  intro V
  obtain ⟨S, hS, h⟩ := ha V
  refine ⟨S, hS, ?_⟩
  intro W f hf
  let r := (data W).restrictionY
  let := r.additive
  let := r.limits
  let := r.colimits
  exact h W f hf
end AlgebraicGeometry.Scheme
