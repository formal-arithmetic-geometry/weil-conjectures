/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.ResolutionOpenRestrictionCore
import WeilConjectures.AlgebraicGeometry.ResolutionOpenScalarCore
import WeilConjectures.AlgebraicGeometry.RestrictedResolutionSectionsExist

/-! # Untwisted comparison of resolution sections

## References

* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 01E4](https://stacks.math.columbia.edu/tag/01E4)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- Raw resolution sections agree with untwisted open cohomology, naturally for
restriction to a pulled-back principal open and for multiplication by a function. -/
theorem resolution_open_scalar_comparison {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) (I : InjectiveResolution F) (q : ℕ)
    (W : T.Opens) (a : Γ(T, W)) :
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let P := sectionCohomologyPresheaf K q
    let Y := (f ⁻¹ᵁ W).toScheme
    let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
    let b := ((f.app W) ≫ (f ⁻¹ᵁ W).topIso.inv).hom a
    let s : Γ(𝟙_ Y.Modules, ⊤) := unitSectionsEquiv ⊤ b
    ∃ c : P.obj (op W) ≃+
        (RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).obj G,
      (∀ (U : Y.Opens), (U : Set Y) = nonvanishingLocus (𝟙_ Y.Modules) s →
        ∃ d : P.obj (op (T.basicOpen a)) ≃+
          (RingedSpace.openModuleCohomology Y.toRingedSpace q U).obj G,
          ∀ x : P.obj (op W),
            (RingedSpace.openModuleCohomologyRestriction Y.toRingedSpace q
              (homOfLE (le_top : U ≤ ⊤))).app G (c x) =
                d ((P.map (homOfLE (T.basicOpen_le a)).op).hom x)) ∧
      (∀ (n : ℕ) (x : P.obj (op W)),
        (RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).map
          (G.smulHom (b ^ n)) (c x) = c (a ^ n • x)) := by
  dsimp
  obtain ⟨R⟩ := restrictedResolutionSections_exists I (f ⁻¹ᵁ W)
  refine ⟨resolutionOpenComparison f F I q W R, ?_, ?_⟩
  · exact resolution_open_restriction_core f F I q W a R
  · exact resolution_open_scalar_core f F I q W a R

end AlgebraicGeometry.Scheme.Modules
