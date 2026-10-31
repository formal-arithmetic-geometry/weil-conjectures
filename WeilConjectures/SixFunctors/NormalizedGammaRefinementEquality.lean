/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedCompactificationReindexing
public import WeilConjectures.AlgebraicGeometry.CondensedOpenProperPasting
import WeilConjectures.SixFunctors.CondensedDirectCompositorNormalization

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing
open AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper
open WeilConjectures

namespace WeilConjectures

/-- The middle natural transformation `Γ_u` of the normalized proper/open refinement word:
the normalized `CondensedOpenProper.gamma` of the square `(j₁, 1_X, u, j₂)`, preceded by the
inverse identity direct-image comparison.

Source: `literature/blueprint/latest/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/`
`prop-sf-pf-coherence.proof.md`, independence paragraph
(blueprint: def-sf-normalized-gamma-adjunct). -/
def normalizedGammaAdjunct
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (r : c₁.Refinement c₂) (P : Pasting Λ) :
    CompactificationReindexing.J Λ c₂.i ⟶
      CompactificationReindexing.J Λ c₁.i ⋙ CompactificationReindexing.R Λ r.hom := by
  let sq : CommSq c₁.i (𝟙 X) r.hom c₂.i := CommSq.mk r.i_hom
  let γ := CondensedOpenProper.gamma Λ P.units sq
  exact (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (CondensedOpenProper.rId Λ X).inv
      (CompactificationReindexing.J Λ c₂.i) ≫ γ

/-- The normalized proper/open refinement transformation on the full ordinary derived
categories.  Its middle map is `CondensedOpenProper.gamma`; the two direct-image
compositors and the identity comparison are retained explicitly.  The body is the one
it had in `WeilConjectures.SixFunctors.CondensedRefinementCounitIdentification`; its middle map
is definitionally `normalizedGammaAdjunct`.

Source: the proper/open mate normalization in `lem-zl-condensed-open-proper-pasting`
and the refinement comparison in `lem-sf-projection-refinement-descent`.
(blueprint: `lem-sf-condensed-refinement-counit-identification`).
-/
def normalizedGammaRefinement
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (r : c₁.Refinement c₂) (P : Pasting Λ) :
    CompactificationReindexing.F Λ c₂ ⟶ CompactificationReindexing.F Λ c₁ := by
  let sq : CommSq c₁.i (𝟙 X) r.hom c₂.i := CommSq.mk r.i_hom
  let γ := CondensedOpenProper.gamma Λ P.units sq
  let m : CompactificationReindexing.J Λ c₂.i ⟶
      CompactificationReindexing.J Λ c₁.i ⋙ CompactificationReindexing.R Λ r.hom :=
    (Functor.leftUnitor _).inv ≫
      Functor.whiskerRight (CondensedOpenProper.rId Λ X).inv
        (CompactificationReindexing.J Λ c₂.i) ≫ γ
  exact Functor.whiskerRight m (CompactificationReindexing.R Λ c₂.g) ≫
    Functor.whiskerLeft (CompactificationReindexing.J Λ c₁.i)
      ((CondensedOpenProper.rComp Λ r.hom c₂.g).hom ≫
        (eqToIso (congrArg (CompactificationReindexing.R Λ) r.hom_g)).hom)

/-- The native middle map `m_u`: the `P_u ⊣ R_u` transpose of the clopen refinement
adjunct `CompactificationReindexing.refinementAdjunct`, exactly the middle map in the
definition of `CompactificationReindexing.refinement`.

Source: `literature/blueprint/latest/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/`
`prop-sf-pf-coherence.proof.md`, independence paragraph
(blueprint: def-sf-native-refinement-middle). -/
def nativeRefinementMiddle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (r : c₁.Refinement c₂) :
    CompactificationReindexing.J Λ c₂.i ⟶
      CompactificationReindexing.J Λ c₁.i ⋙ CompactificationReindexing.R Λ r.hom := by
  exact ((derivedUpperStarLowerStarAdjunction Λ r.hom).whiskerRight _).homEquiv _ _
    (CompactificationReindexing.refinementAdjunct Λ r)

/-- The normalized Gamma middle map equals the native clopen adjunct: `Γ_u = m_u` on the
whole ordinary unbounded category.

Source: `literature/blueprint/latest/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/`
`prop-sf-pf-coherence.proof.md`, independence paragraph; step 2 of
`lem-sf-condensed-refinement-counit-identification`.
Proof: the refinement is the commutative square `(j₁, 1_X, u, j₂)` of
`lem-zl-condensed-open-proper-pasting`(b); its fibre product `W₁ ×_{W₂} X` is the open
`V = u⁻¹(j₂ X)` with `i : V → W₁`, `t : V → X` and the clopen section `s` with `t s = 1`,
`i s = j₁`. `Γ_u` is the `J_{j₂} ⊣ P_{j₂}` adjunct of `λ⁻¹`, `λ` the open restriction
followed by the inverse open unit, so it suffices that `λ ∘ P_{j₂}(m_u) ∘ η_{j₂} = 1`.
(i) The mate-transpose lemma `lem-pur-adjunction-mate-transpose` for `P_u ⊣ R_u`,
`P_t ⊣ R_t` and the open restriction `P_{j₂} R_u → R_t P_i` moves the transpose through
`P_{j₂}`. (ii) By the normalization of the open base change (`B_normalized`) the resulting
map, after the inverse open units of `i`, is the clopen projector `P_t K → J_s K`.
(iii) By `lem-pur-clopen-unbounded-derived-localization` on `V = s(X) ⊔ C` this projector is
the unit of `P_s ⊣ R_s`, and `J_s ≅ R_s` is the zero insertion. Hence the composite is the
unit of the composite adjunction for `t s = 1_X`, carried by the compositors, which is the
identity by `lem-fix-condensed-pullback-coherence`. Uniqueness of transposes gives the
equality. Empty `X` and `u = 1` are covered (zero objects; `V = X`, `s = 1`).
(blueprint: lem-sf-normalized-gamma-adjunct-equality). -/
theorem normalizedGammaAdjunct_eq_refinementAdjunct
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (r : c₁.Refinement c₂) (P : Pasting Λ) :
    normalizedGammaAdjunct Λ r P = nativeRefinementMiddle Λ r := by
  sorry

/-- Equality of the middle refinement maps gives equality of the full normalized and
native refinement transformations.

Source: `literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-pf-done/`
`fix-prop-projection-formula.proof.md`; step 3 of
`lem-sf-condensed-refinement-counit-identification`.
Proof: unfolding, `normalizedGammaRefinement` is `R_{p₂}(normalizedGammaAdjunct)` followed by
`CondensedOpenProper.rComp u p₂` and the index equality, while
`CompactificationReindexing.refinement` is `R_{p₂}(nativeRefinementMiddle)` followed by
`rightDerivedLowerStarComp u p₂` and the same index equality. By `h` the middle maps agree,
so it remains to identify the two direct-image compositors. `rComp` is the conjugate of the
pullback compositor `pComp` (the derived image of the module pullback compositor) under the
adjunctions `mapDerivedCategoryRightDerivedAdjunction`; `rightDerivedLowerStarComp` is the
conjugate of `leftDerivedUpperStarComp` under `derivedUpperStarLowerStarAdjunction`. Module
pullback is exact (`det-prop-sfb-module-pullback-exact-main`), so its left derived functor is
its derived image and the two left adjoints agree; under this identification
`leftDerivedUpperStarComp` is the derived image of the module pullback compositor
(`prop-sfb-module-left-derived-upper-star-comp`,
`lem-sfb-derived-composition-adjunction-normalization`). Conjugates are unique, so the two
direct-image compositors agree, and whiskering gives the equality.
(blueprint: lem-sf-normalized-gamma-transport). -/
theorem normalizedGammaRefinement_transport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c₁ c₂ : Compactification f}
    (r : c₁.Refinement c₂) (P : Pasting Λ)
    (h : normalizedGammaAdjunct Λ r P = nativeRefinementMiddle Λ r) :
    normalizedGammaRefinement Λ r P = CompactificationReindexing.refinement Λ r := by
  change Functor.whiskerRight (normalizedGammaAdjunct Λ r P)
      (CompactificationReindexing.R Λ c₂.g) ≫ _ = _
  rw [h]
  unfold CompactificationReindexing.refinement
  rw [← normalizedDirectCompositor_eq Λ r.hom c₂.g]
  rfl

end WeilConjectures
