/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # Components of the bounded ordinary sheaf dual

Source: Stacks Project, sites-cohomology.tex, Tags 08JJ and 0A8X
(blueprint: lem-sfb-ringed-site-bounded-dual-components).

The abbreviations below only expand the recorded Hom constructions and the
coefficient sheaf in degree zero. The component is the actual product projection.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe c v r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RingedSiteBoundedDual

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  (R : Sheaf J CommRingCat.{max c v r})

/-- Module sheaves in the chosen ambient universe.
Source: Stacks 08JJ, 0A8X (blueprint: lem-sfb-ringed-site-bounded-dual-components). -/
abbrev Modules := SheafOfModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)

/-- The standard zero-object structure obtained from the terminal module sheaf.
Source: Stacks 0A8X (blueprint: lem-sfb-ringed-site-bounded-dual-components). -/
instance modulesHasZeroObject : HasZeroObject (Modules.{c, v, r} R) :=
  hasZeroObject_of_hasTerminal_object

/-- The coefficient sheaf as a module over itself.
Source: Stacks 08JJ (blueprint: lem-sfb-ringed-site-bounded-dual-components). -/
abbrev coefficient : Modules.{c, v, r} R := SheafOfModules.unit _

/-- The standard complex R[0], with the standard single-complex construction.
Source: Stacks 08JJ (blueprint: lem-sfb-ringed-site-bounded-dual-components). -/
abbrev zeroComplex : CochainComplex (Modules.{c, v, r} R) ℤ :=
  (CochainComplex.singleFunctor (Modules.{c, v, r} R) 0).obj (coefficient.{c, v, r} R)

/-- The recorded internal sheaf Hom into the coefficient sheaf.
Source: Stacks 04TT, 08JJ (blueprint: lem-sfb-ringed-site-bounded-dual-components). -/
abbrev dual (T : Modules.{c, v, r} R) : Modules.{c, v, r} R :=
  SheafOfModules.homObj T (coefficient.{c, v, r} R)

/-- The recorded sheaf Hom complex into R[0].
Source: Stacks 0A8X, 08JJ (blueprint: lem-sfb-ringed-site-bounded-dual-components). -/
abbrev complexDual (E : CochainComplex (Modules.{c, v, r} R) ℤ) :
    CochainComplex (Modules.{c, v, r} R) ℤ :=
  homComplex (R := R) E (zeroComplex.{c, v, r} R)

/-- Projection to the sole possibly nonzero Hom factor, followed by O^0 = R.
Source: Stacks 0A8X, 08JJ (blueprint: lem-sfb-ringed-site-bounded-dual-components). -/
def component (E : CochainComplex (Modules.{c, v, r} R) ℤ) (p q : ℤ) (h : p + q = 0) :
    (complexDual.{c, v, r} R E).X q ⟶ dual.{c, v, r} R (E.X p) :=
  homComplexπ E (zeroComplex.{c, v, r} R) q p 0 h ≫
    SheafOfModules.homObjMap (𝟙 (E.X p))
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (coefficient.{c, v, r} R)).hom

/-- The ordinary bounded dual has reversed terms and support, the double-dual
has the negative double-transposed differential, and signed evaluation is a chain map.
The first two equations pin the isomorphisms to the actual product projections.
The last two equations specify ordinary evaluation delta and beta^i = (-1)^i delta.
Thus, for homogeneous phi of degree -i, beta(x)(phi) = (-1)^(i*(-i)) phi(x);
all remaining Hom factors have zero coefficient target.

Source: Stacks Project, sites-cohomology.tex, Tag 08JJ, second proof paragraph,
and Section 0A8X (blueprint: lem-sfb-ringed-site-bounded-dual-components).

Proof:
1. By def-pur-hom-complex and def-pur-sheaf-hom, project the degree-q
   Hom product to p=-q. Insert a local map into this factor and zero into all
   other factors, whose coefficient targets vanish. These operations are linear,
   restriction compatible and inverse, giving alpha.
2. Outside [-b,-a], E^(-q) is zero by the bound. Its sheaf dual is zero,
   so alpha gives the claimed support, also when a>b.
3. The coefficient complex has zero differential. The Hom differential of
   def-pur-hom-complex therefore becomes (-1)^(q+1) precomposition by d_E.
4. Repeat the projection for D, and dualize alpha in degree -i, to obtain gamma.
   The two consecutive Hom signs multiply to -1. Linearity then gives the
   negative double transpose of d_E, with no exactness assumption.
5. By def-pur-sheaf-hom, evaluate every local functional on the restriction
   of x to each slice object. This is linear in both arguments and commutes
   with restriction, hence defines delta. The homogeneous Koszul sign is
   (-1)^(i*(-i)) = (-1)^i, since i*i and i have the same parity.
6. Define beta degreewise using gamma inverse and (-1)^i delta. Evaluate the
   chain-map equation on every slice functional: the negative bidual differential
   changes (-1)^i to (-1)^(i+1), while naturality of evaluation moves d_E to x.
   Extensionality gives the chain-map equation. No finite-free retract,
   reflexivity, or exactness of the terms was used. -/
theorem boundedDualComponents
    (E : CochainComplex (Modules.{c, v, r} R) ℤ) (a b : ℤ)
    (hE : ∀ i : ℤ, i < a ∨ b < i → IsZero (E.X i)) :
    ∃ (α : ∀ (p q : ℤ), p + q = 0 →
        ((complexDual.{c, v, r} R E).X q ≅ dual.{c, v, r} R (E.X p)))
      (γ : ∀ i : ℤ, (complexDual.{c, v, r} R (complexDual.{c, v, r} R E)).X i ≅
        dual.{c, v, r} R (dual.{c, v, r} R (E.X i)))
      (δ : ∀ i : ℤ, E.X i ⟶ dual.{c, v, r} R (dual.{c, v, r} R (E.X i)))
      (β : E ⟶ complexDual.{c, v, r} R (complexDual.{c, v, r} R E)),
      (∀ (p q : ℤ) (h : p + q = 0), (α p q h).hom = component.{c, v, r} R E p q h) ∧
      (∀ i : ℤ, (γ i).hom ≫
          SheafOfModules.homObjMap (α i (-i) (add_neg_cancel i)).hom
            (𝟙 (coefficient.{c, v, r} R)) =
        component.{c, v, r} R (complexDual.{c, v, r} R E) (-i) i (neg_add_cancel i)) ∧
      (∀ q : ℤ, (complexDual.{c, v, r} R E).d q (q + 1) ≫
          (α (-(q + 1)) (q + 1) (neg_add_cancel (q + 1))).hom =
        (q + 1).negOnePow • ((α (-q) q (neg_add_cancel q)).hom ≫
          SheafOfModules.homObjMap (E.d (-(q + 1)) (-q)) (𝟙 (coefficient.{c, v, r} R)))) ∧
      (∀ i : ℤ,
        (complexDual.{c, v, r} R (complexDual.{c, v, r} R E)).d i (i + 1) ≫ (γ (i + 1)).hom =
        -((γ i).hom ≫ SheafOfModules.homObjMap
          (SheafOfModules.homObjMap (E.d i (i + 1)) (𝟙 (coefficient.{c, v, r} R)))
          (𝟙 (coefficient.{c, v, r} R)))) ∧
      (∀ q : ℤ, q < -b ∨ -a < q → IsZero ((complexDual.{c, v, r} R E).X q)) ∧
      (∀ (i : ℤ) (U : Cᵒᵖ) (x : (E.X i).val.obj U) (W : (Over U.unop)ᵒᵖ)
        (φ : (dual.{c, v, r} R (E.X i)).val.obj (op W.unop.left)),
        ((((δ i).val.app U).hom x).app W).hom φ =
          (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom
            ((E.X i).val.map W.unop.hom.op x)) ∧
      (∀ (i q t : ℤ) (h : i + q = t) (h' : q + i = t)
        (U : Cᵒᵖ) (x : (E.X i).val.obj U) (W : (Over U.unop)ᵒᵖ)
        (φ : ((complexDual.{c, v, r} R E).X q).val.obj (op W.unop.left)),
        ((((homComplexπ (complexDual.{c, v, r} R E) (zeroComplex.{c, v, r} R)
          i q t h').val.app U).hom (((β.f i).val.app U).hom x)).app W).hom φ =
        (i * q).negOnePow •
          ((((homComplexπ E (zeroComplex.{c, v, r} R) q i t h).val.app
            (op W.unop.left)).hom φ).app (op (Over.mk (𝟙 W.unop.left)))).hom
              ((E.X i).val.map W.unop.hom.op x)) ∧
      (∀ i : ℤ, β.f i ≫ (γ i).hom = i.negOnePow • δ i) := by
  sorry

end CategoryTheory.RingedSiteBoundedDual
