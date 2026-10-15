/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.EtaleSheaves

/-!
# Geometric stalks detect isomorphisms in the bounded below derived category

Source: literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-cd/
lem-weil-pbc-derived-stalk-conservative.md
(blueprint: lem-weil-pbc-derived-stalk-conservative).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A morphism in `D⁺(T_et)` is invertible exactly when every geometric stalk of every
cohomology-sheaf map is invertible.

Source: blueprint sec-curve-estimates/sk-prop-cd/lem-weil-pbc-derived-stalk-conservative.md
(blueprint: lem-weil-pbc-derived-stalk-conservative).

Proof: The bounded below category is a full subcategory of the derived category. A derived
morphism is invertible if and only if all its cohomology maps are invertible: localization
inverts quasi-isomorphisms, and the calculus of fractions represents any derived morphism
as a roof with a quasi-isomorphism on the left. If its cohomology maps are invertible, the
right arrow is also a quasi-isomorphism and the roof has an inverse
(def-weil-abstract-derived-category, lem-pc-quasi-isomorphisms-multiplicative-system).
If all displayed stalk maps are invertible, apply geometric-stalk conservativity to each
cohomology-sheaf map (lemma-weil-pbc-geometric-stalk-conservative), then the preceding
criterion. Conversely cohomology and stalk functors carry an inverse to an inverse.
There is no need to commute stalks with cohomology, since these are already stalks of
cohomology sheaves. -/
theorem isIso_iff_isIso_geometricStalk_homologyMap
    {T : Scheme.{u}}
    {K L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (f : K ⟶ L) :
    IsIso f ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (CommRingCat.of Ω) ⟶ T) (i : ℤ),
      IsIso ((pointSmallEtale t).sheafFiber.map
        ((DerivedCategory.Plus.homologyFunctor _ i).map f)) := by
  sorry

end AlgebraicGeometry.Scheme
