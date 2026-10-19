/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.CategoryTheory.RingedKoszulSystem
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import Sheaf.Algebra.Homology.SplitPerfectTensorKInjective
import Sheaf.Algebra.Homology.TelescopeColimit
import Sheaf.CategoryTheory.RingedCechKoszulColimitIso
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients

/-! # Internal Hom of Cech and a prescribed strict derived limit

Source: Stacks Project, sites-cohomology.tex, Tags 0A0A and 0941.
(blueprint: lem-weil-pbc-ringed-cech-koszul-hom-limit-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]

variable [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]

/-- The telescope/Hom calculation identifies Cech internal Hom with any specified
presentation of the actual strict Koszul tensor tower and its derived inverse limit.

Source: Stacks Project, sites-cohomology.tex, Tags 0A0A and 0941;
more-algebra.tex, Tag 0913; derived.tex, Tag 0949.
(blueprint: lem-weil-pbc-ringed-cech-koszul-hom-limit-comparison).

Proof: compose the augmentation-compatible colimit identification with the canonical
telescope-to-colimit quasi-isomorphism. Apply Hom into a functorial K-injective I.
Hom of each finite positive Koszul complex identifies, by finite evaluation with its
usual total-complex sign, with I tensor its dual. Hom of the telescope is the fibre
of 1-shift on the product of these complexes. Finite split-perfect tensor preserves
K-injectivity, so these products compute derived products. The strict-tower Roos
calculation identifies that fibre with the derived inverse limit of the actual tensor
tower. Its canonical comparison with D.inverseLimit is fixed by the right-derived
universal property and its comparison on K-injective towers; D.tensorFactors fixes
the descent of the actual tensor tower. These identifications are natural before
localization, hence descend to the displayed natural isomorphism. The augmentation
sends x to the fibre coordinate (0,(x)_m), which is the image of the actual degree-zero
Koszul tensor units in the strict derived limit. This proves the unit equation on
complexes, and the representative isomorphisms in D.unit prove it on every derived
object. No restriction comparison or uniqueness of completion-normalized maps is
used. The empty list and zero or invertible generators obey the same calculation. -/
theorem exists_ringed_cech_koszul_hom_limit_comparison
    (D : RingedKoszulLimitPresentation O r b) :
    ∃ theta : ringedCechCompletionFunctor O (ringedExtendedCech O r b).1 ≅ D.completion,
      ∀ E, ringedCechCompletionUnit O (ringedExtendedCech O r b).1
        (ringedExtendedCech O r b).2 E ≫ theta.hom.app E = D.unit E := by
  sorry

end CategoryTheory
