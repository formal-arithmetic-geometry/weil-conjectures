/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.TraceFormula.ComparisonInductionStep

/-!
# Vanishing for the comparison of two site topologies

Source: Stacks Project, Tags 0EZ3, 0EZE and 0EZF
(blueprint: lem-trf-refined-topology-comparison-vanishing).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace CategoryTheory.RefinedTopologyComparison

/-- The first assertion of Stacks Project, Tag 0EZF, lemma-V-C-all-n-general,
under the situation of Tag 0EZ3 (blueprint: lem-trf-refined-topology-comparison-vanishing).

The site structures are actual covering precoverages satisfying the site axioms.
The comparison geometric morphism is constructed from the sheafification
adjunction: its direct image retains the underlying presheaf and its inverse
image is finer sheafification. The weak Serre conditions are written separately
to avoid imposing closure under arbitrary subobjects or quotients. Relocalization is the canonical
slice-site adjunction, and every higher direct image uses injective resolutions.

Proof: For n = 0 the interval 1 ≤ i ≤ n is empty, giving (V_0). Tag 0EZE,
lemma-induction-step-V-C-general, proves (V_r) implies (V_{r+1}) under exactly
these five hypotheses. Induction on r therefore gives (V_n) for all n. By the
definition of (V_n), its instance at X and H in the essential image is precisely
the asserted vanishing of R^i ε_{X,*}H for 1 ≤ i ≤ n. -/
theorem refinedTopologyComparisonVanishing
    {C : Type u} [SmallCategory C]
    (τ τ' : Precoverage C)
    (hτsite : τ.IsSiteForCoverings) (hτ'site : τ'.IsSiteForCoverings)
    (hτ : τ' ≤ τ)
    (P : ∀ ⦃X Y : C⦄, (X ⟶ Y) → Prop)
    (A' : ∀ X : C, Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u} → Prop)
    (hzero : ∀ X : C, A' X 0)
    (hiso : ∀ (X : C) (H K : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u}),
      Nonempty (H ≅ K) → A' X H → A' X K)
    (hkernel : ∀ (X : C) (H K : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u})
      (f : H ⟶ K), A' X H → A' X K → A' X (kernel f))
    (hcokernel : ∀ (X : C) (H K : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u})
      (f : H ⟶ K), A' X H → A' X K → A' X (cokernel f))
    (hextension : ∀ (X : C)
      (S : ShortComplex (Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u})),
      S.ShortExact → A' X S.X₁ → A' X S.X₃ → A' X S.X₂)
    (hbaseChange : ∀ (X Y Y' : C) (f : X ⟶ Y), P f → ∀ g : Y' ⟶ Y,
      ∃ h : HasPullback f g, letI := h; P (pullback.snd f g))
    (hrelocalization : ∀ (X Y : C) (f : X ⟶ Y)
      (H : Sheaf (τ'.toGrothendieck.over Y) AddCommGrpCat.{u}),
      A' Y H → A' X ((relocalization τ'.toGrothendieck f).inverse.obj H))
    (htauSheaf : ∀ (X : C) (H : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u}),
      A' X H → Presheaf.IsSheaf (τ.toGrothendieck.over X) H.obj)
    (hderivedImage : ∀ (X Y : C) (f : X ⟶ Y), P f →
      ∀ (H : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u}), A' X H →
        ∀ i : ℕ, A' Y (((relocalization τ'.toGrothendieck f).direct.rightDerived i).obj H))
    (hrefinement : ∀ (U : C) (I : Type u) (U₀ : I → C) (a : ∀ i : I, U₀ i ⟶ U),
      Presieve.ofArrows U₀ a ∈ τ U →
      ∃ (J : Type u) (V W : J → C) (v : ∀ j : J, V j ⟶ U) (w : ∀ j : J, W j ⟶ V j)
        (K : J → Type u) (Z : ∀ j : J, K j → C) (z : ∀ (j : J) (k : K j), Z j k ⟶ W j),
        Presieve.ofArrows V v ∈ τ' U ∧
        (∀ j : J, Presieve.singleton (w j) ∈ τ (V j) ∧ P (w j)) ∧
        (∀ j : J, Presieve.ofArrows (Z j) (z j) ∈ τ' (W j)) ∧
        ∀ (j : J) (k : K j), ∃ (i : I) (b : Z j k ⟶ U₀ i),
          z j k ≫ w j ≫ v j = b ≫ a i)
    (n : ℕ) (X : C) (H : Sheaf (τ.toGrothendieck.over X) AddCommGrpCat.{u})
    (hH : ∃ H' : Sheaf (τ'.toGrothendieck.over X) AddCommGrpCat.{u},
      A' X H' ∧ Nonempty (H ≅ (sliceComparison τ τ' hτ X).inverse.obj H')) :
    ∀ i : ℕ, 1 ≤ i → i ≤ n →
      IsZero (((sliceComparison τ τ' hτ X).direct.rightDerived i).obj H) := by
  sorry

end CategoryTheory.RefinedTopologyComparison
