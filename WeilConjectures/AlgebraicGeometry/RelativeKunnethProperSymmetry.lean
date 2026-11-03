/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap
import all WeilConjectures.AlgebraicGeometry.SfSupportedFirstExtraction

/-! # Symmetry of the proper relative Künneth composite

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-p-proper/
sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md, final proper mate calculation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local instance high] SymmetricCategory.toBraidedCategory

private theorem native_route_eq
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {B X Y P : Scheme.{u}} {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B}
    (sq : IsPullback p q f g) (t : P ⟶ B) (w : q ≫ g = t)
    [IsProper f] [IsProper g] [IsProper p] [IsProper q] [IsProper t]
    (K : DerivedCategoryModule Λ X) (L : DerivedCategoryModule Λ Y) :
    relativeKunnethIsoOfIsPullback Λ sq t w K L =
      SupportedTrace.nativeRoute Λ sq t w K L := by
  subst t
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  have hex : asIso ((rightDerivedLowerShriekBaseChangeMap Λ sq).app K) =
      (asIso (rightDerivedLowerShriekBaseChangeMap Λ sq)).app K := by
    apply Iso.ext
    rfl
  apply Iso.ext
  simp only [relativeKunnethIsoOfIsPullback, SupportedTrace.nativeRoute,
    relativeKunnethInnerIso, SupportedTrace.nativeInner, SupportedTrace.nativeProjection,
    rightDerivedLowerShriekCompIsoApp, rightDerivedLowerShriekCompIsoOfEq,
    properRouteCompIso, rightDerivedLowerShriekCongrIso, eqToIso_refl,
    Iso.refl_symm, Iso.refl_trans, projectionIsoApp, SupportedTrace.nativeExchange,
    rightDerivedLowerShriekBaseChangeIso, derivedTensorBraidingIso,
    SupportedTrace.push, CoordinateTrace.swap, CoordinateTrace.pull, CoordinateTrace.tensor,
    derivedTensorBraiding, derivedTensorSymmetry,
    DerivedCategory.canonicalTensorSymmetry]
  rw [hex]

/-- For proper factors the canonical relative comparison commutes with tensor symmetry.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-p-proper/
sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md, the proper two-counit mate calculation
(blueprint: lem-sf-relative-kunneth-proper-symmetry).

Proof: the proper-support route is the same six-factor comparison. Its comparison with
ordinary direct image is the ordinary counit-defined Künneth map. The latter commutes with
tensor symmetry, since the pulled-back counits do. Cancel the proper comparison to obtain
the supported square, then identify the native route with the published relative map. -/
theorem relativeKunnethIsoOfIsPullback_proper_symmetry
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {B X Y P : Scheme.{u}} {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B}
    (sq : IsPullback p q f g) (t : P ⟶ B) (w : q ≫ g = t)
    [IsProper f] [IsProper g] [IsProper p] [IsProper q] [IsProper t]
    (K : DerivedCategoryModule Λ X) (L : DerivedCategoryModule Λ Y) :
    (R(t)_![ModuleCat.{u + 1} Λ]).map
        (derivedTensorBraidingIso (ModuleCat.{u + 1} Λ) P
          ((L((p)^*[ModuleCat.{u + 1} Λ])).obj K)
          ((L((q)^*[ModuleCat.{u + 1} Λ])).obj L)).hom ≫
      (relativeKunnethIsoOfIsPullback Λ sq.flip t (sq.w.trans w) L K).hom =
        (relativeKunnethIsoOfIsPullback Λ sq t w K L).hom ≫
          (derivedTensorBraidingIso (ModuleCat.{u + 1} Λ) B
            ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)
            ((R(g)_![ModuleCat.{u + 1} Λ]).obj L)).hom := by
  rw [native_route_eq, native_route_eq]
  exact (SupportedTrace.native_relative_symmetry Λ sq t w K L).symm

end AlgebraicGeometry.Etale
