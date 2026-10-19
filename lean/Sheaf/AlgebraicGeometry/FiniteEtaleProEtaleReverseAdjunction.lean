/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import Sheaf.AlgebraicGeometry.FiniteEtaleProEtaleLocalizationComparison

/-!
# Underived ambidexterity for finite etale morphisms

Source: Weil blueprint, order 2062, proof paragraphs 1--2
(blueprint: lem-sf-finite-etale-proetale-reverse-adjunction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale

/-- On module sheaves, finite etale direct image is left adjoint to inverse image.
There is no finiteness requirement on the coefficient ring.

Source: blueprint `prop-exc-finite-etale-adjoint`, proof paragraphs 1--2, before
passage to complexes (blueprint: lem-sf-finite-etale-proetale-reverse-adjunction).

Proof: an etale map is weakly etale, so inverse image is restriction to the slice
site. Its left adjoint J is the sheafification of the direct-sum extension presheaf.
Cover the base by etale neighbourhoods splitting the finite etale map into finitely
many sheets; these neighbourhoods are pro-etale covers. On such a neighbourhood,
sheaves are tuples of module sheaves, restriction is the diagonal, J is the finite
sum and direct image is the finite product. The canonical biproduct isomorphism
has identity diagonal entries and zero off-diagonal entries. Its inverse is the
sum of the inclusions composed with projections. Both maps commute with relabeling
of sheets. On overlaps refine by the clopen intersections of the two systems of
sheets, where relabeling is a permutation. Hence uniqueness of sheaf morphism gluing
produces a natural isomorphism J to direct image. Transport J's adjunction along
this isomorphism. The unit includes each sheet and the counit sums the sheets;
the triangles follow from projection-inclusion identities. The empty sheet set
gives the zero functor and the same identities, so surjectivity is unnecessary. -/
theorem finiteEtale_reverseModuleAdjunction {V X : Scheme.{u}} (e : V ⟶ X)
    [IsFinite e] [Etale e] (R : Type (u + 1)) [CommRing R] :
    Nonempty (lowerStar (ModuleCat.{u + 1} R) e ⊣ upperStar (ModuleCat.{u + 1} R) e) := by
  obtain ⟨comparison⟩ := finiteEtale_localizationExtensionIso e R
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e))
    (ModuleCat.{u + 1} R) (Scheme.ProEt.topology V) (Scheme.ProEt.topology X)
  exact ⟨(a.ofNatIsoLeft comparison).ofNatIsoRight
    (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} R) e inferInstance).symm⟩

end AlgebraicGeometry.ProEtale
