/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityFrameClass
import WeilConjectures.AlgebraicGeometry.SupportLongExact
import WeilConjectures.AlgebraicGeometry.SupportedCupFunctoriality
import WeilConjectures.AlgebraicGeometry.PurTwistSheafLocallyFree
import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted

/-!
# Unit and permutation invariance of concrete supported Kummer products

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
lem-pur-frame-independence.proof.md, "Unit multiples" and "Permutations"
(blueprint: lem-pur-kummer-product-unit-permutation).

The existing frameBoundaryProduct is defined for arbitrary functions. Equality of
its defining ideal sheaves supplies the canonical identification of closed supports;
frameClosedCoefficientIso transports the supported-Hom representative along it.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

/-- Multiplying the functions by global units and permuting them preserves their
scheme-theoretic zero subscheme and concrete supported Kummer product. The witness
hs is equality of the actual defining ideal sheaves, not just their radicals or
underlying closed sets. Its induced isomorphism over X identifies the coefficient
sources. Both products have the same canonical positive Tate twist and degree 2c.
There is no smoothness, regularity, finiteness or separatedness assumption.

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
lem-pur-frame-independence.proof.md, "Unit multiples" and "Permutations"
(blueprint: lem-pur-kummer-product-unit-permutation).

Proof (the six steps of the DAG node):
1. A unit multiple generates the same principal ideal, and a permutation preserves
   the sum of these ideals. Thus the ideal sheaves agree. For c=0 both products
   are frameEmptyClass, the supported unit on X.
2. For a global unit v, Kummer pullback identifies its class on X minus V(f) with
   the restriction of its class on X (lem-pur-supported-cup-functoriality).
   Exactness of thm-pur-with-support-exactness kills its support boundary.
3. Kummer additivity and the additive boundary give boundary(kappa(v*f)) =
   boundary(kappa(v)) + boundary(kappa(f)) = boundary(kappa(f)). This works for
   arbitrary f, including zero divisors and nilpotents.
4. The first Tate line is locally free of rank one
   (lem-pur-twist-sheaf-locally-free). Locally writing its sections as a*e and b*e
   shows that its tensor flip is the identity since ab=ba. Equality of these
   sheaf morphisms descends, independently of the temporary basis. Tensoring
   with identities proves the same assertion inside every positive twist power
   of def-coefficient-twists-detailed.
5. Associativity of lem-pur-supported-cup-functoriality isolates any adjacent pair
   of boundary factors. Its graded symmetry has sign (-1)^(2*2)=1; step 4 removes
   the coefficient flip. Reassociation preserves the left-associated product.
6. Express a permutation as adjacent swaps, using step 5 successively. Replace
   each unit-scaled factor by step 3. The support transports are those induced
   by step 1. For an etale frame, frameClass is this very boundary product, so
   the assertion specializes after identifying its zero scheme with the pullback. -/
theorem frameBoundaryProduct_unit_permutation (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k)) (c : ℕ)
    (h : Fin c → Γ(X, ⊤)) (σ : Equiv.Perm (Fin c)) (v : Fin c → Γ(X, ⊤)ˣ) :
    ∃ hs :
      Scheme.IdealSheafData.ofIdealTop
          (Ideal.span (Set.range (fun j : Fin c ↦ (v j : Γ(X, ⊤)) * h (σ j)))) =
        (Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range h)) : X.IdealSheafData),
      P.frameBoundaryProduct X a c (fun j ↦ (v j : Γ(X, ⊤)) * h (σ j)) =
        (cupSingle P X).map
          (P.frameClosedCoefficientIso
            (X.zeroLocusSubschemeι
              (Set.range (fun j : Fin c ↦ (v j : Γ(X, ⊤)) * h (σ j))))
            (X.zeroLocusSubschemeι (Set.range h))
            (eqToIso (congrArg Scheme.IdealSheafData.subscheme hs))
            (Scheme.IdealSheafData.eqToHom_comp_subschemeι hs)).hom ≫
          P.frameBoundaryProduct X a c h := by
  sorry

end WeilConjectures.PurityFiniteSetting
