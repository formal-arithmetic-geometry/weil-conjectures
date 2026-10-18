/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.BaseChange.Pasting
import Sheaf.AlgebraicGeometry.EtaleSetDegreeZeroFlatBaseChange

/-!
# Degree-zero flat base change for abelian étale sheaves

Source: Stacks Project, Étale Cohomology, Tag 0EYS, and blueprint
sec-smooth-purity/sk-prop-sf-kunneth-ordinary (blueprint: lem-kun-0eys).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Flat, locally finitely presented inverse image with geometrically reduced fibres
commutes with direct image for every abelian étale sheaf, under arbitrary base change.
The arrow is the recorded underived exchange for the transposed square: its transpose
under `upperStar h ⊣ lowerStar h` is the square inverse-image comparison followed by
`upperStar e` applied to the counit for `g`.
Source: Stacks Project, Tag 0EYS; blueprint sec-smooth-purity/sk-prop-sf-kunneth-ordinary
(blueprint: lem-kun-0eys).

Proof:
1. Forget abelian sheaves to sets. The comparison and adjunction bijections of
   lem-weil-pbc-etale-inverse-image-algebraic-structures preserve units and counits
   (a counit is the transpose of an identity). By the unit characterization in
   lem-weil-pbc-inverse-image-composition and uniqueness in
   lem-weil-pbc-sets-etale-inverse-image-composition-units, they preserve composition
   comparisons. The formula in lem-weil-pbc-square-iso-pasting then identifies the
   forgotten square comparison with the set square comparison. Consequently the
   forgotten exchange has transpose h⁻¹f⁻¹g_*F → e⁻¹g⁻¹g_*F → e⁻¹F, as required.
2. Write L and R for set inverse and direct images, A = R_g F, B = L_e F, and
   α : L_h L_f ≅ L_e L_g. Exchange is m = R_h(L_e ε_g ∘ α_A) ∘ η_h.
   The composite-unit equation of
   lem-weil-pbc-sets-etale-inverse-image-composition-units says
   R_f R_h(α_A) ∘ R_f(η_h) ∘ η_f = R_g(η_e) ∘ η_g.
   Thus R_f(m) ∘ η_f = R_g R_e(L_e ε_g) ∘ R_g(η_e) ∘ η_g
   = R_g(η_e) ∘ R_g(ε_g) ∘ η_g = R_g(η_e), by naturality and the triangle
   identity. This is the defining transpose of the set exchange in
   sbc-lem-degree-zero-flat-base-change. That theorem makes the forgotten arrow
   invertible, with exactly the given flatness, presentation and fibre hypotheses.
3. Each component of exchange is therefore a bijective group homomorphism. Its
   inverse preserves zero and addition by injectivity of that homomorphism.
   Naturality of the inverses follows by composing the desired equation with the
   bijective component and using naturality of exchange. The inverses give a
   morphism of abelian sheaves (def-weil-pbc-abelian-etale-sheaves), with both
   composites equal to identities. Hence the specified abelian exchange is an
   isomorphism. No restriction on g and no torsion assumption is used. -/
theorem isIso_abelianBaseChangeMap_of_flat
    {X Y S T : Scheme.{u}} {h : Y ⟶ X} {e : Y ⟶ T}
    {f : X ⟶ S} {g : T ⟶ S} (sq : ChosenCartesianSquare h e f g)
    [Flat f] [LocallyOfFinitePresentation f]
    (hf : ∀ s : S, GeometricallyReduced (f.fiberToSpecResidueField s))
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq.flip).app F) := by
  sorry

end AlgebraicGeometry.Etale
