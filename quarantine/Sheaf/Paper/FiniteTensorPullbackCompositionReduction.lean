/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.Paper.FiniteTensorFixedComparisons

/-! # Finite coefficient pullback coherence in fixed-scalar coordinates

Source: the finite-reduction proof Step 2, expanded presentation-reduction Step 7;
Stacks Project, sites-cohomology.tex, Tag 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

/-- The recorded coefficient pullback mate respects the exact pullback compositor.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 2; expanded parent proof Step 7;
Stacks 07A4 (blueprint: lem-pur-finite-tensor-pullback-composition-reduction).
Proof: take a flat-term K-flat representative of K. Pullback along g and then f,
and pullback along f composed with g, preserve the representatives. The canonical
cochain compositor identifies their iterated inverse images and scalar association.
The coefficient comparison in either order sends a section tensor b to its
iterated inverse image tensor b. Thus the two cochain maps agree, by the composition
and coefficient equations of cochainPullbackTensorCoherence. These maps are the
recorded scalar-adjunction mates: their transposes use the same unit x to x tensor 1.
The canonical pullback compositor is the adjunction conjugate of the restriction
compositor, and mates commute with composition, so this identification preserves
the compositor used in compositionFixedPullbackComp. Localize the cochain equality
and transport it through the fixed realization, scalar presentation and pullback
model isomorphisms. Naturality and the adjunction triangle identities cancel the
intermediate units and counits. Faithfulness of realization then gives the stated
fixed-scalar equality. No flatness of the quotient ring is used. Identity maps,
empty schemes and equal coefficient levels obey the same equations. -/
theorem finiteTensorPullbackCompositionReduction (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∀ K,
      (P.finiteTensorReduction m hm hmn X).map
          ((compositionFixedPullbackComp P.Ring f g).hom.app K) ≫
        (P.finiteTensorPullbackComparison m hm hmn f ((P.smoothPurityPullback g).obj K)).hom ≫
        ((P.finiteReductionSetting m hm).smoothPurityPullback f).map
          (P.finiteTensorPullbackComparison m hm hmn g K).hom =
      (P.finiteTensorPullbackComparison m hm hmn (f ≫ g) K).hom ≫
        (compositionFixedPullbackComp (P.finiteReductionSetting m hm).Ring f g).hom.app
          ((P.finiteTensorReduction m hm hmn Z).obj K) := by sorry

end WeilConjectures.PurityFiniteSetting
