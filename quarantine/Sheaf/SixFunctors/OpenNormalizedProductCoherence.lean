/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q132
-/
module

public import Sheaf.Paper.FiniteOpenProductSwap
public import Sheaf.SixFunctors.OpenExternalTensorNormalization
import Sheaf.SixFunctors.OpenTensorNormalization
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Algebra.Homology.RingedTensorComplexConstraints
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients

/-!
# Triple pasting of supplied normalized open product comparisons

Source: blueprint latest, sec-six-functors/sk-thm-sf-kunneth-relative,
lem-sf-kunneth-coherence.proof.md, clause (ii); Stacks 0GL1 and 03DI.
(blueprint: lem-sf-open-normalized-product-coherence-criterion).

The four isomorphisms are independent inputs. Only their four restriction equations
are assumed. The geometric diagrams permit any choices of the product cones; `Triple`
expresses transport of both bracketings to the same triple product.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open SheafOfModules.OpenTensorNormalization WeilConjectures
open AlgebraicGeometry.ProEtale.OpenExternalTensor

namespace AlgebraicGeometry.ProEtale.OpenExternalTensor.NormalizedProduct

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable {X Y W Xb Yb Wb T Tb T₁₂ T₂₃ Tb₁₂ Tb₂₃ : Scheme.{u}}
variable {j : X ⟶ Xb} {k : Y ⟶ Yb} {l : W ⟶ Wb}
variable [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion l]

/-- The supplied binary comparison is normalized by precisely the section open units.
The existing `restriction` is the inverse of r in the node's notation, so this is
r⁻¹ followed by u*e equals the open unit, equivalently u*e equals r followed by the unit.
Source: node statement, normalization equation; Stacks 03DI and 0GL1
(blueprint: lem-sf-open-normalized-product-coherence-criterion). -/
def IsNormalized (d : Diagram j k T Tb) (K : FiniteD A X) (L : FiniteD A Y)
    (e : ambient A d K L ≅ (finiteShriek A d.u).obj (inside A d K L)) : Prop :=
  restriction A d K L ≫ (FiniteOpenProduct.pull A d.u).map e.hom =
    (FiniteOpenProduct.adj A d.u).unit.app (inside A d K L)

/-- The left pasting uses e₁₂ then eL, with the canonical tensor/pullback comparisons.
Source: F in the node statement and proof step 3; blueprint clause (ii)
(blueprint: lem-sf-open-normalized-product-coherence-criterion). -/
def leftPaste (d₁₂ : Diagram j k T₁₂ Tb₁₂) (dL : Diagram d₁₂.u l T Tb)
    (K : FiniteD A X) (L : FiniteD A Y) (M : FiniteD A W)
    (e₁₂ : ambient A d₁₂ K L ≅ (finiteShriek A d₁₂.u).obj (inside A d₁₂ K L))
    (eL : ambient A dL (inside A d₁₂ K L) M ≅
      (finiteShriek A dL.u).obj (inside A dL (inside A d₁₂ K L) M)) :
    tripleAmbient A d₁₂ dL K L M ⟶
      (finiteShriek A dL.u).obj (tripleInside A d₁₂ dL K L M) :=
  (FiniteOpenProduct.tensorIsoMap A _
    (FiniteOpenProduct.tensorPullIso A dL.pb _ _).symm (Iso.refl _)).hom ≫
    FiniteOpenProduct.tensorMap A Tb
      ((FiniteOpenProduct.pull A dL.pb).map e₁₂.hom) (𝟙 _) ≫ eL.hom ≫
    (finiteShriek A dL.u).map
      (FiniteOpenProduct.tensorIsoMap A _
        (FiniteOpenProduct.tensorPullIso A dL.p _ _) (Iso.refl _)).hom

/-- The right pasting uses e₂₃ then eR; the two existing associators and the equality
of product opens identify its source and target with those of `leftPaste`.
Source: G in the node statement and proof step 3; blueprint clause (ii)
(blueprint: lem-sf-open-normalized-product-coherence-criterion). -/
def rightPaste
    {d₁₂ : Diagram j k T₁₂ Tb₁₂} {d₂₃ : Diagram k l T₂₃ Tb₂₃}
    {dL : Diagram d₁₂.u l T Tb} {dR : Diagram j d₂₃.u T Tb}
    (t : Triple d₁₂ d₂₃ dL dR)
    (K : FiniteD A X) (L : FiniteD A Y) (M : FiniteD A W)
    (e₂₃ : ambient A d₂₃ L M ≅ (finiteShriek A d₂₃.u).obj (inside A d₂₃ L M))
    (eR : ambient A dR K (inside A d₂₃ L M) ≅
      (finiteShriek A dR.u).obj (inside A dR K (inside A d₂₃ L M))) :
    tripleAmbient A d₁₂ dL K L M ⟶
      (finiteShriek A dL.u).obj (tripleInside A d₁₂ dL K L M) :=
  (outerAssociator A t K L M).hom ≫
    FiniteOpenProduct.tensorMap A Tb (𝟙 _)
      ((FiniteOpenProduct.pull A dR.qb).map e₂₃.hom) ≫ eR.hom ≫
    (finiteShriek A dR.u).map (innerAssociator A t K L M).hom ≫
    (shriekCongr A t.sameOpen).hom.app (tripleInside A d₁₂ dL K L M)

/-- Four independently supplied normalized binary isomorphisms have equal triple
pastings, both invertible, both restricting to identity under the specified units.
Restriction is injective on maps from this triple source to any extension v!D'.

Source: blueprint latest, lem-sf-kunneth-coherence.proof.md, clause (ii), and
Stacks 0GL1, 03DI (blueprint: lem-sf-open-normalized-product-coherence-criterion).

Proof plan (the five steps of the node):
1. The open units are invertible by lem-sf-open-tensor-normalization. The composite
adjunction unit (def-weil-pbc-composite-adjunction) and the conjugate unit equation
(lem-weil-pbc-conjugate-iso-unit-equation) show that the unique-left-adjoint
compositor preserves the specified restriction identifications.
2. On flat-term K-flat tensor models the native associator takes ((x tensor y)
tensor z) to x tensor (y tensor z), and restriction keeps these sections. Apply
lem-sf-ringed-tensor-complex-constraints, then preservation and comparison in
lem-weil-pbc-ringed-topoi-derived-tensor-pullback, and descend with
lem-weil-pbc-site-derived-tensor-descent. Projection composition identifies the
same pulled-back section. Thus both bracketings give the same tripleRestriction.
3. Each pasted factor is an isomorphism. Restrict the first supplied comparison
using its normalization equation. In the next normalization its open unit meets
its inverse and cancels. Do this for e₁₂,eL and separately for e₂₃,eR. Step 2 and
the compositor unit equation give the two displayed triple unit equations.
No formula or naturality for the four supplied isomorphisms is needed.
4. For h,h' from H₃ to v!D', precompose with the inverse left pasting. The resulting
maps v!D₃ to v!D' come from unique maps D₃ to D' by full faithfulness of v!.
Equal restrictions and naturality of its invertible unit make those maps equal;
hence h=h'. This uses the proved isomorphism of this specific source with v!D₃.
5. Apply this injectivity with D'=D₃ to the two unit equations from step 3.
-/
theorem coherence (B : Scheme.{u}) (a : Xb ⟶ B) (b : Yb ⟶ B) (c : Wb ⟶ B)
    (d₁₂ : Diagram j k T₁₂ Tb₁₂) (d₂₃ : Diagram k l T₂₃ Tb₂₃)
    (dL : Diagram d₁₂.u l T Tb) (dR : Diagram j d₂₃.u T Tb)
    (t : Triple d₁₂ d₂₃ dL dR)
    (_bar₁₂ : IsPullback d₁₂.pb d₁₂.qb a b)
    (_inner₁₂ : IsPullback d₁₂.p d₁₂.q (j ≫ a) (k ≫ b))
    (_bar₂₃ : IsPullback d₂₃.pb d₂₃.qb b c)
    (_inner₂₃ : IsPullback d₂₃.p d₂₃.q (k ≫ b) (l ≫ c))
    (_barL : IsPullback dL.pb dL.qb (d₁₂.pb ≫ a) c)
    (_innerL : IsPullback dL.p dL.q (d₁₂.p ≫ j ≫ a) (l ≫ c))
    (_barR : IsPullback dR.pb dR.qb a (d₂₃.pb ≫ b))
    (_innerR : IsPullback dR.p dR.q (j ≫ a) (d₂₃.p ≫ k ≫ b))
    (K : FiniteD A X) (L : FiniteD A Y) (M : FiniteD A W)
    (e₁₂ : ambient A d₁₂ K L ≅ (finiteShriek A d₁₂.u).obj (inside A d₁₂ K L))
    (e₂₃ : ambient A d₂₃ L M ≅ (finiteShriek A d₂₃.u).obj (inside A d₂₃ L M))
    (eL : ambient A dL (inside A d₁₂ K L) M ≅
      (finiteShriek A dL.u).obj (inside A dL (inside A d₁₂ K L) M))
    (eR : ambient A dR K (inside A d₂₃ L M) ≅
      (finiteShriek A dR.u).obj (inside A dR K (inside A d₂₃ L M)))
    (_h₁₂ : IsNormalized A d₁₂ K L e₁₂)
    (_h₂₃ : IsNormalized A d₂₃ L M e₂₃)
    (_hL : IsNormalized A dL (inside A d₁₂ K L) M eL)
    (_hR : IsNormalized A dR K (inside A d₂₃ L M) eR) :
    IsIso (leftPaste A d₁₂ dL K L M e₁₂ eL) ∧
    IsIso (rightPaste A t K L M e₂₃ eR) ∧
    (tripleRestriction A d₁₂ dL K L M ≫
      (FiniteOpenProduct.pull A dL.u).map (leftPaste A d₁₂ dL K L M e₁₂ eL) =
        (FiniteOpenProduct.adj A dL.u).unit.app (tripleInside A d₁₂ dL K L M)) ∧
    (tripleRestriction A d₁₂ dL K L M ≫
      (FiniteOpenProduct.pull A dL.u).map (rightPaste A t K L M e₂₃ eR) =
        (FiniteOpenProduct.adj A dL.u).unit.app (tripleInside A d₁₂ dL K L M)) ∧
    (∀ D' : FiniteD A T, Function.Injective
      (fun h : tripleAmbient A d₁₂ dL K L M ⟶ (finiteShriek A dL.u).obj D' =>
        (FiniteOpenProduct.pull A dL.u).map h)) ∧
    leftPaste A d₁₂ dL K L M e₁₂ eL = rightPaste A t K L M e₂₃ eR := by
  sorry

end AlgebraicGeometry.ProEtale.OpenExternalTensor.NormalizedProduct
