module

public import Sheaf.AlgebraicGeometry.CohomologyFractionPresentation
public import Sheaf.AlgebraicGeometry.Ample
import Sheaf.Paper.LocalizedCohomologyMayerVietoris

universe u_1
@[expose] public section

open CategoryTheory MonoidalCategory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/- Historical counterexample to the former interface: on Spec k for a nonzero field,
 U = V = S = top, L = F = O, s = 1, and c W p = 0 satisfied the old local
 premises but gave the nonbijective zero map k -> k in degree zero. The old
 STATEMENT-DISPUTED interface omitted hc and replaced the intersection formula
 by True. The corrected hc excludes this example. -/

/-- Bijectivity of the canonical middle comparison in the localization diagram.
The fraction formula `hc` identifies `c` with the canonical comparison; all three
local equivalences satisfy that same formula.

Source: Stacks Project, Cohomology of Schemes, Tag 09MR, Mayer--Vietoris paragraph
(blueprint: lem-sc-invert-s-cohomology-gluing-aux).

Proof: On the nonvanishing open S the section s trivializes L. Consequently the
map on cohomology induced by multiplication by s^n is an isomorphism, for every
open W intersected with S. The formula hc therefore determines c W p on every
fraction [n, xi]. These fractions generate the quotient of the direct sum, so
additive homomorphisms satisfying the formula agree on the entire presentation.
Apply localizedCohomology_mayerVietoris to U and V. Its nonvanishing open equals
S by equality of underlying sets. Uniqueness identifies its comparison family
with c, transferring the exact rows and all commuting squares to c. The same
uniqueness identifies the equivalences in h_locU, h_locV and h_locUV with c on
U, V and their intersection. Thus the product comparisons and intersection
comparisons are bijective in every degree.
In degree zero both rows begin with an injective union-to-product map, followed
by the product-to-intersection map. Injectivity of c on the union follows by
mapping a kernel element to the product, using injectivity of its comparison,
and then injectivity of the upper union-to-product map. For surjectivity, map a
lower union element into the lower product, lift it through the product
comparison, and use the intersection comparison's injectivity and the commuting
square to see that the lift lies in the upper kernel. Upper exactness lifts it
to the upper union; lower injectivity shows its comparison is the given element.
For degree p = q + 1 use the five consecutive terms: product in degree q,
intersection in degree q, union in degree q + 1, product in degree q + 1,
intersection in degree q + 1. Both rows are exact, all squares commute, and all
four outside comparisons are bijective. The additive five lemma gives
bijectivity of the middle comparison c (U union V) (q + 1). Together with the
degree-zero argument this proves the claim in every natural-number degree. -/
theorem localized_middle_comparison_bijective
    (X : Scheme.{u_1}) [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    (F : X.Modules) [F.IsQuasicoherent]
    (S : X.Opens) (hS : (S : Set X) = nonvanishingLocus L s)
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (c : ∀ (W : X.Opens) (p : ℕ), CohomologyFractionPresentation L F s p W →+
      (RingedSpace.openModuleCohomology X.toRingedSpace p (W ⊓ S)).obj F)
    (hc : ∀ (W : X.Opens) (p n : ℕ)
        (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace p W).obj
          (F ⊗ L.tensorPow n : X.Modules)),
      (RingedSpace.openModuleCohomology X.toRingedSpace p (W ⊓ S)).map
          (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
            F ⟶ (F ⊗ L.tensorPow n : X.Modules))
          (c W p (cohomologyFraction L F s p W n ξ)) =
        (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
          (homOfLE (inf_le_left : W ⊓ S ≤ W))).app
            (F ⊗ L.tensorPow n : X.Modules) ξ)
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
          (F ⊗ L.tensorPow n : X.Modules)),
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ V ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (e (cohomologyFraction L F s p (U ⊓ V) n ξ)) =
          (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_left : U ⊓ V ⊓ S ≤ U ⊓ V))).app
              (F ⊗ L.tensorPow n : X.Modules) ξ) :
    ∀ p : ℕ, Function.Bijective (c (U ⊔ V) p) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
