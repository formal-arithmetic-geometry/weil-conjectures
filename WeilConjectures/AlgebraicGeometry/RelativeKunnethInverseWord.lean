/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap

/-! # The inverse relative Künneth word

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-p-proper/
sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md, opening sentence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local instance high] SymmetricCategory.toBraidedCategory

/-- The inverse product is the forward projection/exchange word with compositor last.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-p-proper/
sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md, opening sentence
(blueprint: lem-sf-relative-kunneth-inverse-word).

Proof: reverse the four outer isomorphisms. Reverse the three inner isomorphisms,
using functoriality of mapIso and the fact that the hom of the exchange is precisely
the specified base-change map. Associate the resulting composite to the right. -/
theorem relativeKunnethIsoOfIsPullback_inverse_word
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {B X Y P : Scheme.{u}} {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ B} {g : Y ⟶ B}
    (sq : IsPullback p q f g) (t : P ⟶ B) (w : q ≫ g = t)
    [HasCompactification f] [HasCompactification g] [HasCompactification q]
    [HasCompactification t] [QuasiCompact q] [QuasiCompact t]
    (K : DerivedCategoryModule Λ X) (L : DerivedCategoryModule Λ Y) :
    (relativeKunnethIsoOfIsPullback Λ sq t w K L).inv =
      (derivedTensorBraidingIso (ModuleCat.{u + 1} Λ) B
        ((R(g)_![ModuleCat.{u + 1} Λ]).obj L)
        ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).inv ≫
      (projectionIsoApp Λ g L ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).hom ≫
      (R(g)_![ModuleCat.{u + 1} Λ]).map
        ((derivedTensorBraidingIso (ModuleCat.{u + 1} Λ) Y
          ((L((g)^*[ModuleCat.{u + 1} Λ])).obj
            ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)) L).inv ≫
          ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).map
            ((rightDerivedLowerShriekBaseChangeMap Λ sq).app K)).app L ≫
          (projectionIsoApp Λ q ((L((p)^*[ModuleCat.{u + 1} Λ])).obj K) L).hom) ≫
      (rightDerivedLowerShriekCompIsoApp Λ q g t w _).inv := by
  -- Avoid inserting large definitional-equality proofs for the derived-functor types.
  simp -implicitDefEqProofs only [relativeKunnethIsoOfIsPullback, relativeKunnethInnerIso,
    Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv,
    rightDerivedLowerShriekBaseChangeIso_hom,
    Category.assoc]

end AlgebraicGeometry.Etale
