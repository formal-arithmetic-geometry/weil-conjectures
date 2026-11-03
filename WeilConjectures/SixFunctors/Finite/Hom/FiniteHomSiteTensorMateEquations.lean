/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescentData
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomSiteTensorNaturalEquality
public import WeilConjectures.SixFunctors.FiniteHomSiteTensorNaturalEqualityLegacy

/-! # Tensor equation of the finite site mate

Source: blueprint finite Hom proof, normalized scalar and site tensor comparisons.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem beta_square_inverse
    {C D : Type*} [Category C] [Category D]
    (T : C × C ⥤ D) {A B E F : D} {K K' M M' : C}
    (s : A ≅ B) (k : K ≅ K') (m : M ≅ M')
    (f₁ : B ⟶ E) (f₂ : E ⟶ T.obj (K', M'))
    (g₁ : A ⟶ F) (g₂ : F ⟶ T.obj (K, M))
    (h : f₁ ≫ f₂ ≫ T.map (Prod.mkHom k.inv m.inv) = s.inv ≫ g₁ ≫ g₂) :
    s.hom ≫ f₁ ≫ f₂ = g₁ ≫ g₂ ≫ T.map (Prod.mkHom k.hom m.hom) := by
  have ht : T.map (Prod.mkHom k.hom m.hom) ≫
      T.map (Prod.mkHom k.inv m.inv) = 𝟙 _ := by
    rw [← T.map_comp]
    change T.map (Prod.mkHom (k.hom ≫ k.inv) (m.hom ≫ m.inv)) = _
    rw [k.hom_inv_id, m.hom_inv_id]
    exact T.map_id _
  have : IsIso (Prod.mkHom k.inv m.inv) :=
    (k.symm.prod m.symm).isIso_hom
  apply (cancel_epi s.inv).mp
  apply (cancel_mono (T.map (Prod.mkHom k.inv m.inv))).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, ht, Category.comp_id] using h

set_option maxHeartbeats 0 in
-- Specializing the abstract inverse square compares the recorded tensor functors.
/-- The fixed restriction mate preserves the normalized tensor map.
This assertion chooses no strong or symmetric structures or tower equation.
Source: blueprint thm-coef-finite-hom proof, final scalar/site comparison paragraph
(blueprint: lem-coef-finite-hom-site-tensor-mate-equations).

Proof: form the two natural transformations in the direction of finiteHomSiteBeta.
Fully faithful restriction detects equality on pairs of K-flat representatives.
The route-normalization lemma gives common source and target isomorphisms and
identifies each route with the localization of its ordinary chain map. The chain
equation identifies those maps; canceling the comparison isomorphisms gives
equality on representatives and hence equality of the natural transformations.
Evaluate at K,M and invert the beta components to obtain the displayed square.
The unit equation is a separate categorical consequence of this tensor equation
once strong structures are supplied.
Identity quotients use the identity ring map and its adjunction triangles.
No assertion about Hom or quotient flatness is used. -/
theorem finiteHomSiteTensorMateEquations
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    {n m : ℕ} (h : m ≤ n) :
    ∀ K M : finiteHomEtale l E X n,
      (coefFiniteHomSiteIso l E X h).hom.app
          ((finiteHomEtaleClosed l E X n).tensor.obj (K, M)) ≫
        (coefficientFiniteQuotientDerived l E X h).map
          ((finiteHomNuTensor l E X n).hom.app (K, M)) ≫
        (coefFiniteHomProTensor l E X h).hom.app
          ((finiteHomNu l E X n).obj K, (finiteHomNu l E X n).obj M) =
      (finiteHomNu l E X m).map ((finiteHomEtaleTensor l E X h).hom.app (K, M)) ≫
        (finiteHomNuTensor l E X m).hom.app
          ((finiteHomEtaleReduction l E X h).obj K,
            (finiteHomEtaleReduction l E X h).obj M) ≫
        (finiteIntrinsicClosed l E X m).tensor.map
          (Prod.mkHom ((coefFiniteHomSiteIso l E X h).hom.app K)
            ((coefFiniteHomSiteIso l E X h).hom.app M)) := by
  intro K M
  have hKM := congrArg (fun z ↦ z.app (K, M))
    (finiteHomSiteTensorNaturalEquality_legacy l E X h)
  exact beta_square_inverse ((finiteIntrinsicClosed l E X m).tensor)
    ((coefFiniteHomSiteIso l E X h).app
      ((finiteHomEtaleClosed l E X n).tensor.obj (K, M)))
    ((coefFiniteHomSiteIso l E X h).app K) ((coefFiniteHomSiteIso l E X h).app M)
    ((coefficientFiniteQuotientDerived l E X h).map
      ((finiteHomNuTensor l E X n).hom.app (K, M)))
    ((coefFiniteHomProTensor l E X h).hom.app
      ((finiteHomNu l E X n).obj K, (finiteHomNu l E X n).obj M))
    ((finiteHomNu l E X m).map ((finiteHomEtaleTensor l E X h).hom.app (K, M)))
    ((finiteHomNuTensor l E X m).hom.app
      ((finiteHomEtaleReduction l E X h).obj K,
        (finiteHomEtaleReduction l E X h).obj M)) hKM

end WeilConjectures
