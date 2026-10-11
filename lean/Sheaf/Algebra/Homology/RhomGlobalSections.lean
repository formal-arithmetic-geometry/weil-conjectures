/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Sheaf.Algebra.Homology.DerivedInternalHom
import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomology

/-!
# Global sections of derived internal Hom

Source: Stacks Project, Lemma 21.35.1, Tag 08JA, global statement
(blueprint: lem-pur-rhom-global-sections).
-/

universe u₁ w₁

open CategoryTheory Opposite

namespace CategoryTheory

set_option synthInstance.maxHeartbeats 100000 in
-- Additive Hom inference traverses the derived and sheaf categories in each repeated binder.
/-- The canonical additive identification `H⁰(C, R𝓗om(L, M)) ≃+ Hom_D(O)(L, M)`,
natural contravariantly in `L` and covariantly in `M`.

Source: Stacks Project, Lemma 21.35.1, Tag 08JA, global statement
(blueprint: lem-pur-rhom-global-sections).

Proof:
1. Choose a K-flat representative of `L` using `lem-pc-kflat-resolution` and a
   K-injective representative `I` of `M` using `prop-pur-kinjective-resolutions-exist`.
   By `def-pur-derived-internal-hom` and `lem-pur-rhom-well-defined`, their sheaf Hom
   complex represents `R𝓗om(L,M)` independently of the choices. It is K-injective
   by `lem-pur-hom-kflat-into-kinjective`, so its global sections compute `H⁰`.
2. By `def-pur-hom-complex`, sections of its degree-n term are families of linear
   maps `Lᵖ → Iᵖ⁺ⁿ` (the tensor-Hom identification at the unit). Its differential is
   `d_I f - (-1)^n f d_L`. Thus degree-zero cocycles are chain maps, and degree-zero
   coboundaries are null-homotopic maps. Its zeroth cohomology is consequently the
   additive group of maps in the homotopy category. Since `I` is K-injective,
   `lem-weil-pbc-kinjective-hom-derived` identifies this group with derived morphisms.
3. The map sends a chain map to its image in the localization. Composition commutes
   with localization and with changes of representatives (`lem-pur-rhom-well-defined`),
   proving independence of all choices and the naturality equation below. -/
theorem rhom_global_sections
    {C : Type u₁} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u₁})
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))] :
    ∃ e : ∀ P : (DerivedCategory (SheafOfModules.{u₁}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))ᵒᵖ ×
        DerivedCategory (SheafOfModules.{u₁}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)),
      ((ringedSiteZerothHypercohomology J R).obj ((derivedInternalHom J R).obj P)) ≃+
        (P.1.unop ⟶ P.2),
      ∀ (P P' : (DerivedCategory (SheafOfModules.{u₁}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))ᵒᵖ ×
          DerivedCategory (SheafOfModules.{u₁}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
        (f : P ⟶ P')
        (x : (ringedSiteZerothHypercohomology J R).obj ((derivedInternalHom J R).obj P)),
        e P' ((ringedSiteZerothHypercohomology J R).map ((derivedInternalHom J R).map f) x) =
          f.1.unop ≫ e P x ≫ f.2 := by
  sorry

end CategoryTheory
