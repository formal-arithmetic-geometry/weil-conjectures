/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import WeilConjectures.AlgebraicGeometry.RelativePseudoCoherentComplex

/-! # Relative pseudo-coherence on algebraic spaces

Source: Stacks Project, spaces-more-morphisms.tex, definition-relative-pseudo-coherence
and lemma-qcoh-relative-pseudo-coherence-characterize, condition (1)
(blueprint: def-sfb-space-relative-pseudo-coherent-complex).

The scheme object is the existing right-derived restriction to Zariski opens of a chart.
On quasi-coherent cohomology this is the inverse of the etale/Zariski equivalence.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w wZ

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Relative m-pseudo-coherence is tested on every compatible pair of etale scheme charts.
The finite-type witness is recorded together with the scheme predicate, so this definition
also encodes its locally finite type domain without an additional typeclass on space maps.
On a locally finite type map those witnesses are already implied by the chart definition.
Source: Stacks Project, spaces-more-morphisms.tex, definition-relative-pseudo-coherence (1)
and lemma-qcoh-relative-pseudo-coherence-characterize (1)
(blueprint: def-sfb-space-relative-pseudo-coherent-complex). -/
def IsMPseudoCoherentRelativeTo
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [HasDerivedCategory.{w} X.SmallModules]
    [∀ T : Scheme.{u},
      HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (g : X ⟶ Y) (m : ℤ) (K : X.DerivedQCoh) : Prop :=
  ∀ (U : X.EtaleSite) (V : Y.EtaleSite) (h : U.obj.left ⟶ V.obj.left),
    U.obj.hom ≫ g.hom.hom = yoneda.map h ≫ V.obj.hom →
      ∃ hf : LocallyOfFiniteType h.left,
        @Scheme.IsMPseudoCoherentRelativeTo.{u, wZ} _ _ _ h.left hf m
          (derivedSchemeRestriction X U K.obj)

/-- Relative pseudo-coherence means relative m-pseudo-coherence for every integer m.
The affine covers, factorizations and perfect approximations in the scheme predicate can
vary with m and with the pair of charts; there is no global cohomological bound.
Source: Stacks Project, spaces-more-morphisms.tex, definition-relative-pseudo-coherence (2)
(blueprint: def-sfb-space-relative-pseudo-coherent-complex). -/
def IsPseudoCoherentRelativeTo
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [HasDerivedCategory.{w} X.SmallModules]
    [∀ T : Scheme.{u},
      HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (g : X ⟶ Y) (K : X.DerivedQCoh) : Prop :=
  ∀ m : ℤ, IsMPseudoCoherentRelativeTo g m K

end AlgebraicGeometry.AlgebraicSpace
