/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAffineContinuity
public import Mathlib.CategoryTheory.Category.Basic

/-!
# Cohomology of a pro-étale affine

Source: `literature/blueprint/latest/blueprint/part-six-operations/sec-proetale-coefficients/`
`sec-pe-derived-comparison/sk-cor-pe-affine-continuity/_section.md`,
node `sk-cor-pe-affine-continuity`, order 1050; Stacks Project, Tag 03Q6.

For an arbitrary unital coefficient ring, the canonical map from the filtered derived
colimit of section complexes on an affine étale presentation to derived pro-étale
sections is an isomorphism.  The map is the canonical section map constructed in
`det-sf-comparison-affine-continuity`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/--
The derived-sections continuity isomorphism for a pro-étale affine presentation.

The source is the filtered derived colimit of the section complexes on the affine
étale stages, and the target is derived sections after the geometric inverse image
on the pro-étale site.  The displayed map is induced by the actual restriction maps
and the comparison inverse-image unit.  The theorem is the statement of the
corollary; its proof applies the arbitrary-ring affine-continuity comparison.

Source: `literature/blueprint/latest/blueprint/part-six-operations/sec-proetale-coefficients/`
`sec-pe-derived-comparison/sk-cor-pe-affine-continuity/_section.md`,
node `sk-cor-pe-affine-continuity` (blueprint: `sk-cor-pe-affine-continuity`);
Stacks Project, Tag 03Q6.

Proof: The presentation is small, nonempty and cofiltered, with affine étale stages
and affine transition morphisms.  The canonical map from the filtered derived
colimit of stage sections to pro-étale derived sections is
`affineContinuityProEtaleMap`; the comparison theorem for arbitrary unital rings
makes this map invertible.  The bounded-below hypothesis is represented by
`K : DerivedCategory.Plus` and the chosen bounded-below injective representative
`L`; the coefficient action is the left action of the constant ring sheaf.
-/
theorem proEtaleAffineContinuityCorollary {I : Type u} [SmallCategory I]
    [IsCofiltered I] (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
    (D : I ⥤ X.Etale) (c : Cone (D ⋙ Scheme.toProEt X))
    (hc : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c))
    [∀ i : I, IsAffine (D.obj i).left]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (a : ℤ) [L.IsStrictlyGE a] [∀ n : ℤ, Injective (L.X n)]
    (e : DerivedCategory.Q.obj L ≅ K.obj) :
    IsIso (affineContinuityProEtaleMap D c K.obj L e) := by
  exact (proEtaleAffineContinuity X Λ D c hc K L a e).2.1

end AlgebraicGeometry.ProEtale
