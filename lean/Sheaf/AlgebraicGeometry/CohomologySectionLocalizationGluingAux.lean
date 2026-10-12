module

public import Sheaf.AlgebraicGeometry.CohomologyFractionPresentation
public import Sheaf.AlgebraicGeometry.Ample
import Sheaf.Paper.LocalizedCohomologyMayerVietoris

universe u_1
@[expose] public section

open CategoryTheory MonoidalCategory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- The five-lemma step for the Mayer--Vietoris localization diagram.  Once the
local comparison maps on `U`, `V`, and `U ⊓ V` are additive equivalences, the
middle comparison map supplied by the Mayer--Vietoris diagram is bijective.
The proof is the standard five-lemma chase on the exact localized and ordinary
Mayer--Vietoris rows (blueprint: lem-sc-invert-s-cohomology-gluing-aux). -/
theorem localized_middle_comparison_bijective
    (X : Scheme.{u_1}) [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    (F : X.Modules) [F.IsQuasicoherent]
    (S : X.Opens) (hS : (S : Set X) = nonvanishingLocus L s)
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (c : ∀ (W : X.Opens) (p : ℕ), CohomologyFractionPresentation L F s p W →+
      (RingedSpace.openModuleCohomology X.toRingedSpace p (W ⊓ S)).obj F)
    (h_locU : ∀ p : ℕ, ∃ e : CohomologyFractionPresentation L F s p U ≃+
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ S)).obj F,
      ∀ (n : ℕ) (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace p U).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (e (cohomologyFraction L F s p U n ξ)) =
          (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_left : U ⊓ S ≤ U))).app
              (F ⊗ L.tensorPow n : X.Modules) ξ)
    (h_locV : ∀ p : ℕ, ∃ e : CohomologyFractionPresentation L F s p V ≃+
        (RingedSpace.openModuleCohomology X.toRingedSpace p (V ⊓ S)).obj F,
      ∀ (n : ℕ) (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace p V).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        (RingedSpace.openModuleCohomology X.toRingedSpace p (V ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (e (cohomologyFraction L F s p V n ξ)) =
          (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_left : V ⊓ S ≤ V))).app
              (F ⊗ L.tensorPow n : X.Modules) ξ)
    (h_locUV : ∀ p : ℕ, ∃ e : CohomologyFractionPresentation L F s p (U ⊓ V) ≃+
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ V ⊓ S)).obj F,
      ∀ (n : ℕ) (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ V)).obj
          (F ⊗ L.tensorPow n : X.Modules)), True) :
    ∀ p : ℕ, Function.Bijective (c (U ⊔ V) p) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
