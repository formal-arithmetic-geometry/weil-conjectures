/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.SmoothPresentationClosedSubsets
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Rational points of quasi-separated algebraic spaces

Source: Stacks Project, decent-spaces.tex, Tags 03JX, 0H1T, 0H1R and 07U5
(blueprint: lem-sfb-qs-space-rational-point-topology).

We use the existing field-object quotient and smooth-atlas topology on the discrete
fibred groupoid of an algebraic space. Rational points are actual natural transformations
from the representable presheaf of the identity scheme over the base field.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Send a rational point to its field-object class, using the given morphism itself.
The spectrum of the base field is the identity object over that spectrum; the witness
that its source is a field spectrum is the identity isomorphism.
Source: Stacks Project, Tags 03BU and 04XG; the point convention of
lem-sfb-smooth-presentation-closed-subsets
(blueprint: lem-sfb-qs-space-rational-point-topology). -/
def rationalPointClass (K : Type u) [Field K] (Z : AlgebraicSpace (Spec (.of K)))
    (a : yoneda.obj (Over.mk (𝟙 (Spec (.of K)))) ⟶ Z.obj.obj) :
    ModuliPoints (discreteModuli Z.obj.obj) :=
  Quot.mk _ ⟨CostructuredArrow.mk a, ⟨K, inferInstance, ⟨Iso.refl _⟩⟩⟩

/-- Rational points of a quasi-separated algebraic space are determined by their point
classes, and every such class is closed in the smooth-atlas topology.
Source: Stacks Project, Tags 03JX, 0H1T, 0H1R and 07U5
(blueprint: lem-sfb-qs-space-rational-point-topology).

Proof:
1. Apply lem-sfb-qs-space-field-monomorphism over Spec K to the class of a rational
point a. The quasi-compact relative diagonal supplies a quasi-compact monomorphism
j : Spec F → Z representing that class. Its structural map is a field homomorphism
 i : K → F by def-weil-affine-spectrum. The field-extension equivalence conventions
of def-a1-space-point-topology and lem-sfb-smooth-presentation-closed-subsets agree.
2. Spec K is reduced. By lem-sfb-reduced-singleton-field-factorization, a factors
through j, giving h : F → K with h ∘ i = id. Any other rational point b with this
class similarly gives h' : F → K with h' ∘ i = id.
3. A unital homomorphism from a field is injective. Since h(i(h(u))) = h(u),
injectivity gives i(h(u)) = u, so i is surjective. Consequently h and h' are both its
inverse. The affine-spectrum morphism/ring-map correspondence gives a = b.
4. Every point has a quasi-compact field monomorphism representative by step 1.
Apply lem-sfb-decent-algebraic-field-image-closed to a over Spec K: the base has one
closed point and the residue-field extension K → K is algebraic. Thus its image
is a closed singleton in the algebraic-space atlas topology. An étale atlas is smooth
by def-sbc-smooth-morphisms, so lem-sfb-smooth-presentation-closed-subsets identifies
this topology with the one used here. Empty rational-point sets give vacuous claims.
No finite-type, reducedness or separatedness assumption on Z is used. -/
theorem qsSpace_rationalPoint_topology (K : Type u) [Field K]
    (Z : AlgebraicSpace (Spec (.of K)))
    (hdiag : IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left)
      (prod.lift (𝟙 Z.obj.obj) (𝟙 Z.obj.obj))) :
    Function.Injective (rationalPointClass K Z) ∧
      ∀ a : yoneda.obj (Over.mk (𝟙 (Spec (.of K)))) ⟶ Z.obj.obj,
        @IsClosed _ (moduliSmoothPointTopology (discreteModuli Z.obj.obj))
          {rationalPointClass K Z a} := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
