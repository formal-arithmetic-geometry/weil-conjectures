/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.OpenSectionFractionPresentation
public import Sheaf.AlgebraicGeometry.Ample
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.AffineSectionLocalization

/-! # Section fractions on an affine open of an ambient scheme

Source: Stacks Project, Tags 01PW and 09MR, affine-open paragraph.
(blueprint: lem-sc-affine-open-section-fraction-localization).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- Localization of ordinary sections over an ambient affine open.
Source: Stacks Project, Properties, Tag 01PW, equation module-invert-s, and Cohomology
of Schemes, Tag 09MR, affine-open paragraph.
(blueprint: lem-sc-affine-open-section-fraction-localization).

Proof: Put Y = U.toScheme and restrict L and F along U.ι. Restriction agrees with
pullback, so the restricted L is invertible and the restricted F is quasi-coherent.
Restrict s to U and use restrictAppIso to regard it as a global section on Y.
Apply affine_section_localization on Y. The stalk criterion for nonvanishing identifies
its nonvanishing open with the preimage of S, whose image in X is U inf S.
Restriction preserves the tensor unit, tensor products, tensor powers, and the maps
mulTensorPowSection. Thus restrictAppIso in each numerator degree gives an additive
equivalence of direct sums which identifies all fraction relations.
The additive closure of the section relations equals the underlying additive subgroup
of their module span: multiplying the generator indexed by (n,b,t) by r gives the
generator indexed by (n,b,r smul t), by linearity of mulTensorPowSection. Consequently
the direct-sum equivalence descends from OpenSectionFractionPresentation to the
SectionFractionPresentation on Y. Compose with affine_section_localization and the
section comparison on U inf S. The tensor formula there is exactly the displayed
coefficient map: the inverse right unitor sends z to z tensor 1 and tensorPowSection
sends 1 to the section s to the power n. Naturality of restrictAppIso identifies the
other side with restriction from U. Empty U and zero s are included; no nonzero
or inhabited hypothesis occurs in the quotient construction or localization theorem. -/
theorem affineOpen_sectionFraction_localization (X : Scheme.{u})
    (L : X.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    (F : X.Modules) [F.IsQuasicoherent]
    (S : X.Opens) (hS : (S : Set X) = nonvanishingLocus L s)
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ e : OpenSectionFractionPresentation L F s U ≃+ Γ(F, U ⊓ S),
      ∀ (n : ℕ) (t : Γ(F ⊗ L.tensorPow n, U)),
        (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
            F ⟶ (F ⊗ L.tensorPow n : X.Modules)).app (U ⊓ S)
            (e (openSectionFraction L F s U n t)) =
          (F ⊗ L.tensorPow n).presheaf.map
            (homOfLE (inf_le_left : U ⊓ S ≤ U)).op t := by
  sorry

end AlgebraicGeometry.Scheme.Modules
