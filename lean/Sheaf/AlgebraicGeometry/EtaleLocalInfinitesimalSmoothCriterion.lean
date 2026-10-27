module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.FormallySmooth
import WeilConjectures.CategoryTheory.Sites.Torsor
import Sheaf.AlgebraicGeometry.EtaleLocalLiftDerivationAction
import WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift

/-! # Étale-local infinitesimal solutions imply smoothness

Source: Stacks Project, Tags 02H0 and 02H6, with the étale lift-torsor argument
of Tag 04AM and quasi-coherent cohomology comparison of Tag 03P2
(blueprint: lem-sfb-etale-local-infinitesimal-lifts-smooth).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A locally finitely presented morphism is smooth when every affine square-zero
lifting problem has compatible solutions on a jointly surjective étale family.
Source: Stacks Project, Tags 02H6, 04AM, 03P2, and 03AJ
(blueprint: lem-sfb-etale-local-infinitesimal-lifts-smooth).

Proof, postponed to stage 3:
1. Fix an affine first-order thickening and a compatible square. Apply
   `lem-sfb-etale-local-lift-torsor-quasi-coherent` to obtain the quasi-coherent
   module `H = i_* Hom(a₀* Ω, I)`, the étale sheaf `L` of lifts, and its simply
   transitive derivation action, conditional on a section.
2. The hypothesized lifts are local sections of `L`. Translation by each section
   trivializes `L` on that member of the cover, making `L` an `H_et`-torsor in
   the general abelian-sheaf sense of `def-sc-gm-torsor`.
3. Affineness and quasi-coherence give `H¹(T_et, H_et) = 0` by
   `lem-sc-etale-affine-qcoherent` with degree one. The module here is on `T`.
4. By `lem-sc-torsor-h1`, zero corresponds to the trivial torsor, so `L` is
   trivial. Its zero section gives a global lift with both required equations.
5. This works for every affine test square, hence gives formal smoothness as
   defined in `def-sbc-formally-smooth` (Tag 02H0).
6. Combine formal smoothness with locally finite presentation using
   `def-sbc-smooth-morphisms` and the criterion of Tag 02H6. -/
theorem smooth_of_etale_local_infinitesimal_lifts
    {V W : Scheme.{u}} (f : V ⟶ W) [LocallyOfFinitePresentation f]
    (h : ∀ (T₀ T : Scheme.{u}) (i : T₀ ⟶ T) [IsAffine T₀] [IsAffine T],
      IsFirstOrderThickening i →
        ∀ (a₀ : T₀ ⟶ V) (b : T ⟶ W), a₀ ≫ f = i ≫ b →
          ∃ (J : Type u) (Tj : J → Scheme.{u}) (v : ∀ j : J, Tj j ⟶ T)
            (a : ∀ j : J, Tj j ⟶ V),
            (∀ j : J, Etale (v j)) ∧
            (∀ t : T, ∃ (j : J) (x : Tj j), v j x = t) ∧
            (∀ j : J, a j ≫ f = v j ≫ b) ∧
            (∀ j : J, pullback.snd i (v j) ≫ a j = pullback.fst i (v j) ≫ a₀)) :
    Smooth f := by
  sorry

end AlgebraicGeometry
