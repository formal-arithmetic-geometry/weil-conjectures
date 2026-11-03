/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.NativeShriek.NativeShriekDefs

/-! # Composition on native strict Weil pairs

Source: latest blueprint, lem-zl-composition-weight-bound.proof.md, paragraph 1,
Frobenius-compatible composition (blueprint: lem-zl-native-shriek-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.DeligneLaumon.NativeShriek

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The iterated actual compact-support image and the composite's actual image
are isomorphic as strict Weil pairs, for every compactification presentation.
There is no weight hypothesis in this comparison.

Source: latest blueprint, lem-zl-composition-weight-bound.proof.md, paragraph 1,
first sentence and the Frobenius-compatibility explanation
(blueprint: lem-zl-native-shriek-composition).

Proof: base change the models and compactifications to D.k. Separated finite-type
models have the ordinary bounded constructible category and its constructible
heart, as in prop-constructible-truncations and the finite-field scope bridge.
Apply lem-zl-shriek-composition to h and g. Its normalized
proper/open compositor alpha gives an isomorphism from the iterated image
to the composite image on bounded constructible carriers. Identify its three
exchanges with RelativeCurve.exchange: expand properExchange as the right
mate of the pullback square and openExchange as the inverse open-adjunction
mate. The derived/exact pullback comparison and the compactification
refinement comparison are normalized by these same units and counits.
Mate pasting and the refinement cocycle therefore identify the exchanges,
including for the semilinear geometric Frobenius on separated models.
The normalized composition/exchange coherence equation is exactly the equivariance
equation for alpha at K. Package alpha and its inverse as morphisms of IsoAlgebra; inverse
compatibility follows by cancelling alpha. Their inverse identities follow
from faithful forgetting. This uses only bounded constructibility of K,
not a chosen realization as a derived Weil module, and works for zero K
and nondense compactifications as well. -/
theorem composition
    (hl : l ≠ D.p)
    (Z₀ : Over (Spec (.of D.k₀)))
    [QuasiSeparated X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [QuasiSeparated Z₀.hom]
    [IsSeparated Z₀.hom]
    [QuasiSeparated Y₀.hom] [IsSeparated Y₀.hom]
    (h₀ : X₀ ⟶ Z₀) (g₀ : Z₀ ⟶ Y₀)
    [IsSeparated h₀.left] [LocallyOfFiniteType h₀.left] [QuasiCompact h₀.left]
    [IsSeparated g₀.left] [LocallyOfFiniteType g₀.left] [QuasiCompact g₀.left]
    (ch : Compactification h₀.left) (cg : Compactification g₀.left)
    (cgh : Compactification (h₀.left ≫ g₀.left))
    (K : Pair D l X₀)
    (hK : constantModelBoundedConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left K.carrier) :
    Nonempty ((image D l g₀ cg).obj ((image D l h₀ ch).obj K) ≅
      (image D l (h₀ ≫ g₀) cgh).obj K) := by
  sorry

end WeilConjectures.DeligneLaumon.NativeShriek
