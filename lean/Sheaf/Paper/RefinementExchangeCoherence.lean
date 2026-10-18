/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting
public import Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport
import WeilConjectures.Compactification.CategoryBaseChange
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
import Sheaf.AlgebraicGeometry.StrictTowerOpenExtension
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import Sheaf.Paper.ProjectionCompactification

/-!
# Refinement exchange coherence for strict pro-etale towers

Source: Stacks Project, Tags 0F7B, 0F7C and 0F7F; the final independence and naturality
argument of the blueprint proof of `thm-cbc-complete-proetale`
(blueprint: lem-cbc-complete-proetale-refinement-exchange-coherence).

`compositionF`, `compositionC` and `compositionE` are the already published canonical
compactification candidate, refinement comparison and proper/open exchange. The wrappers
below only supply quasi-compactness and invertibility, not a new choice of any operation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- The existing normalized refinement map, with open quasi-compactness obtained from f.
The explicit proof argument allows the same construction on a pulled-back f without
adding a quasi-compactness hypothesis on the base change.
Source: Stacks, Tags 0F7B and 0F7C, identity-left proper/open square
(blueprint: lem-cbc-complete-proetale-refinement-exchange-coherence). -/
noncomputable def refinementComparison {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂)
    (hf : QuasiCompact f := by infer_instance) :
    compositionF B c₂ ⟶ compositionF B c₁ := by
  letI : QuasiCompact c₁.i := c₁.quasiCompact_openImmersion hf
  letI : QuasiCompact c₂.i := c₂.quasiCompact_openImmersion hf
  exact compositionC B r

/-- Invertibility of the comparison on the finite scalar etale-origin domain.
Source: Stacks, Tag 0F7B; item proof steps 1 and 2
(blueprint: lem-cbc-complete-proetale-refinement-exchange-coherence).
Proof: the refinement gives the proper/open square with top c₁.i, bottom c₂.i,
left identity and right r.hom. Apply gamma_isIso at M with its given origin at each
level, then apply the functor R of c₂.g. The identity and direct-image compositors
in compositionC are isomorphisms, so the resulting refinement comparison is invertible. -/
theorem refinementComparison_isIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂)
    (M : Derived B X)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M)))
    (hf : QuasiCompact f := by infer_instance) :
    IsIso ((refinementComparison B r hf).app M) := by
  sorry

/-- Pullback preserves the exact finite scalar etale-origin domain used in this item.
Source: blueprint, thm-cbc-complete-proetale, final naturality argument; Stacks, Tag 04JC
and Section 0735; item proof step 2
(blueprint: lem-cbc-complete-proetale-refinement-exchange-coherence).
Proof: evaluation commutes with G. At level n keep the same finite ring Λ_n and
B-algebra map. Constant-coefficient scalar restriction commutes with inverse image,
and the site-comparison pullback isomorphism identifies pullback of ν*L_n with
ν* of etale inverse image of L_n. Exactness of etale inverse image preserves the
lower bound of this L_n. This supplies a ScalarEtaleOrigin at each n, without a
common coefficient ring or a uniform lower bound. -/
theorem refinementFiniteOrigin_pullback {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (M : Derived B X)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M))) :
    ∀ n : ℕ,
      Nonempty (ScalarEtaleOrigin B X' ((ev B X' n).obj ((G B g').obj M))) := by
  sorry

/-- The actual common-refinement isomorphism C_{u₂}⁻¹ C_{u₁}, with no arbitrary choice.
Source: blueprint, thm-cbc-complete-proetale, final independence argument; item step 5
(blueprint: lem-cbc-complete-proetale-refinement-exchange-coherence). -/
noncomputable def refinementCommonComparison {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ d : Compactification f} (u₁ : d.Refinement c₁) (u₂ : d.Refinement c₂)
    (M : Derived B X)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M)))
    (hf : QuasiCompact f := by infer_instance) :
    (compositionF B c₁).obj M ≅ (compositionF B c₂).obj M := by
  letI := refinementComparison_isIso B u₁ M hM hf
  letI := refinementComparison_isIso B u₂ M hM hf
  exact asIso ((refinementComparison B u₁ hf).app M) ≪≫
    (asIso ((refinementComparison B u₂ hf).app M)).symm

/-- All refinement and common-refinement coherences, in the derived strict-tower categories.
The first three equations and the refinement/base-change square are equalities of
natural transformations on the whole derived categories. Invertibility and the
common-refinement isomorphisms are on the stated finite scalar etale-origin domain.
Source: Stacks, Tags 0F7B, 0F7C and 0F7F; blueprint, thm-cbc-complete-proetale,
final independence and naturality argument
(blueprint: lem-cbc-complete-proetale-refinement-exchange-coherence).

Proof, following the six node steps:
1. The refinement equations identify its identity-left proper/open square. Whiskering
   its normalized gamma by R of c₂.g, with canonical compositors, is compositionC.
2. gamma_isIso on the finite scalar etale origins makes this map invertible, as in
   refinementComparison_isIso. The origins are preserved by arbitrary pullback, as in
   refinementFiniteOrigin_pullback: exact etale inverse image retains each lower bound.
3. Pull back the refinement square. The calculus cube gives the equality for gamma
   and beta. Whisker by the outer proper direct image. Naturality moves gamma past
   the outer proper mate, and mate pasting identifies the composite proper mates
   with the mate for c₁.g. These are exactly the two displayed exchange paths.
   This is an equality of transformations, not a deduction from evaluation.
4. Identity normalization gives C_id = 1. Vertical pasting gives the refinement
   composition equation, including the canonical R compositors.
5. For any two common-refinement diagrams choose a common domination. Equalize the
   two arrows to c₁, then equalize the two arrows to c₂ after that refinement.
   The two legs now agree simultaneously. The composition equation and cancellation
   of the invertible comparisons give equality of refinementCommonComparison, also
   for different arrows from the same common refinement.
6. Dominate three compactifications at once. Independence permits computing all
   comparisons there; cancellation gives the cocycle. After base change the common
   refinement and its arrows pull back, and step 2 supplies invertible primed maps.
   Apply step 3 to both legs and cancel C_{u₂}' to get the final intertwining equation.
   There is no qcqs or Noetherian assumption on Y, no properness assumption on g,
   and no common bound or coefficient ring for the different levels.
-/
theorem refinementExchangeCoherence {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (M : Derived B X)
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin B X ((ev B X n).obj M))) :
    (∀ {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂),
      IsIso ((refinementComparison B r).app M)) ∧
    (∀ c : Compactification f,
      refinementComparison B (Compactification.Refinement.id c) = 𝟙 _) ∧
    (∀ {c₁ c₂ c₃ : Compactification f}
      (r : c₁.Refinement c₂) (s : c₂.Refinement c₃),
      refinementComparison B (r.comp s) =
        refinementComparison B s ≫ refinementComparison B r) ∧
    (∀ {X' Y' : Scheme.{u}} {f' : X' ⟶ Y'}
      (g' : X' ⟶ X) (g : Y' ⟶ Y) (sf : IsPullback g' f' f g)
      (c₁ c₂ : Compactification f) (c₁' c₂' : Compactification f')
      (s₁ : c₁'.Z ⟶ c₁.Z) (s₂ : c₂'.Z ⟶ c₂.Z)
      (si₁ : IsPullback g' c₁'.i c₁.i s₁) (sp₁ : IsPullback s₁ c₁'.g c₁.g g)
      (si₂ : IsPullback g' c₂'.i c₂.i s₂) (sp₂ : IsPullback s₂ c₂'.g c₂.g g)
      (r : c₁.Refinement c₂) (r' : c₁'.Refinement c₂')
      (hr : r'.hom ≫ s₂ = s₁ ≫ r.hom),
      compositionE B c₂ c₂' g' g s₂ si₂.w sp₂.w si₂ ≫
          Functor.whiskerLeft (G B g')
            (refinementComparison B r'
              (MorphismProperty.IsStableUnderBaseChange.of_isPullback sf inferInstance)) =
        Functor.whiskerRight (refinementComparison B r) (G B g) ≫
          compositionE B c₁ c₁' g' g s₁ si₁.w sp₁.w si₁) ∧
    (∀ {c₁ c₂ d e : Compactification f}
      (u₁ : d.Refinement c₁) (u₂ : d.Refinement c₂)
      (v₁ : e.Refinement c₁) (v₂ : e.Refinement c₂),
      refinementCommonComparison B u₁ u₂ M hM =
        refinementCommonComparison B v₁ v₂ M hM) ∧
    (∀ {c₁ c₂ c₃ d₁₂ d₂₃ d₁₃ : Compactification f}
      (u₁ : d₁₂.Refinement c₁) (u₂ : d₁₂.Refinement c₂)
      (v₂ : d₂₃.Refinement c₂) (v₃ : d₂₃.Refinement c₃)
      (w₁ : d₁₃.Refinement c₁) (w₃ : d₁₃.Refinement c₃),
      refinementCommonComparison B u₁ u₂ M hM ≪≫
          refinementCommonComparison B v₂ v₃ M hM =
        refinementCommonComparison B w₁ w₃ M hM) ∧
    (∀ {X' Y' : Scheme.{u}} {f' : X' ⟶ Y'}
      (g' : X' ⟶ X) (g : Y' ⟶ Y) (sf : IsPullback g' f' f g)
      (c₁ c₂ d : Compactification f) (c₁' c₂' d' : Compactification f')
      (s₁ : c₁'.Z ⟶ c₁.Z) (s₂ : c₂'.Z ⟶ c₂.Z) (sd : d'.Z ⟶ d.Z)
      (si₁ : IsPullback g' c₁'.i c₁.i s₁) (sp₁ : IsPullback s₁ c₁'.g c₁.g g)
      (si₂ : IsPullback g' c₂'.i c₂.i s₂) (sp₂ : IsPullback s₂ c₂'.g c₂.g g)
      (sid : IsPullback g' d'.i d.i sd) (spd : IsPullback sd d'.g d.g g)
      (u₁ : d.Refinement c₁) (u₂ : d.Refinement c₂)
      (u₁' : d'.Refinement c₁') (u₂' : d'.Refinement c₂')
      (hu₁ : u₁'.hom ≫ s₁ = sd ≫ u₁.hom)
      (hu₂ : u₂'.hom ≫ s₂ = sd ≫ u₂.hom),
      (G B g).map (refinementCommonComparison B u₁ u₂ M hM).hom ≫
          (compositionE B c₂ c₂' g' g s₂ si₂.w sp₂.w si₂).app M =
        (compositionE B c₁ c₁' g' g s₁ si₁.w sp₁.w si₁).app M ≫
          (refinementCommonComparison B u₁' u₂' ((G B g').obj M)
            (refinementFiniteOrigin_pullback B g' M hM)
            (MorphismProperty.IsStableUnderBaseChange.of_isPullback sf inferInstance)).hom) := by
  sorry

end AlgebraicGeometry.ProEtale.StrictTower
