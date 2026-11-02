/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperExchangeComparison
public import WeilConjectures.Compactification.BoundaryRefinement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingCompactificationCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompCompositionBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
import WeilConjectures.AlgebraicGeometry.ClassicalProEtaleProperBaseChange
import WeilConjectures.Compactification.DenseCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperRefinementSquareExchangeCompatibility

/-! # Proper coincidence and its canonical exchange

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sf-comp-proper/_section.md and sk-prop-sf-comp-proper.proof.md
(blueprint: sk-prop-sf-comp-proper).

The normalization uses the actual refinement from the identity compactification.
Compatibility is an equation of the ordinary ambient condensed-module exchanges.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CompactificationReindexing

/-- The identity compactification, as an object of the dense boundary-refinement category.
Its open immersion is the identity, hence quasi-compact and scheme-theoretically dense.
Source: proper-coincidence proof, first sentence (blueprint: sk-prop-sf-comp-proper). -/
def properDenseIdentityCompactification {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    Compactification.DenseBoundaryCompactification f :=
  ⟨⟨⟨Compactification.ofIsProper f, inferInstanceAs (QuasiCompact (𝟙 X))⟩⟩,
    inferInstanceAs (IsSchemeTheoreticallyDominant (𝟙 X))⟩

/-- The canonical refinement from the identity compactification to any compactification
of a proper map. Its ambient arrow is the supplied open immersion; properness follows
from properness of f and separatedness of the compactification's proper factor.
Source: proper-coincidence proof, identity model and comparison paragraph
(blueprint: sk-prop-sf-comp-proper). -/
def properIdentityRefinement {X Y : Scheme.{u}} {f : X ⟶ Y} [IsProper f]
    (c : Compactification f) : (Compactification.ofIsProper f).Refinement c where
  hom := c.i
  i_hom := Category.id_comp _
  hom_g := c.comm.symm

private noncomputable def properComparisonFamily
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
      (c : Compactification f), F Λ c ≅ R Λ f :=
  fun {X Y} f [IsProper f] c =>
    properRefinementComparisonForSquare Λ f c

private theorem properComparisonFamily_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (c : Compactification f) :
    (properComparisonFamily Λ f c).hom =
      refinement Λ (properIdentityRefinement c) ≫
        (properIdentityComparison Λ f).hom := by
  simp only [properComparisonFamily, properRefinementComparisonForSquare,
    properRefinementComparison, properIdentityRefinement,
    properIdentityRefinementForSquare, Iso.trans_hom, asIso_hom]

/-- The canonical proper comparison is independent of compactification and identifies
compact-support exchange with the ordinary proper exchange. The family is normalized
by the actual identity-open comparison and actual refinement maps; it is not an
arbitrary family of isomorphisms. The last equivalence expresses specialization of
compact-support base change to proper base change on its specified coefficient domains.

Source: latest blueprint proper-coincidence proposition and its three proof paragraphs
(blueprint: sk-prop-sf-comp-proper).

Proof:
1. The identity open is quasi-compact and dense, so properDenseIdentityCompactification
is an object of Comp(f) (sk-def-nagata-sketch-data and
sk-prop-nagata-sketch-comp-category). On this model the functor is Rf_* after exact
identity extension. The open-adjunction normalization of
lem-sf-identity-open-exchange-normalization is the published properIdentityComparison.
2. For any other compactification its open is clopen, since f is proper. The normalized
refinement from the identity model is therefore invertible. Compose it with the
identity comparison to obtain the displayed family. The identity and cocycle laws of
sk-prop-sf-comp-coherence, equivalently the normalized refinement identities, give its
compatibility with every refinement and independence of any common refinement.
3. By det-def-sf-exchanges the compact exchange is the proper mate followed by the
proper image of beta. On the identity model, identity-open normalization makes beta
identity. Naturality of the proper mate gives the displayed exchange equation.
Compatibility with compactification comparisons (det-sf-comp-composition-base-change)
transports it to any supplied pair of compactifications. Cancel the two comparison
isomorphisms to obtain the final equivalence. Thus the invertibility assertion of
det-prop-sf-cbc becomes invertibility of the very same proper mate, the exchange of
sk-thm-properbasechange, wherever that assertion is applied.
-/
theorem properCompactificationCoincidence
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    ∃ κ : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
        (c : Compactification f), F Λ c ≅ R Λ f,
      (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (c : Compactification f),
        (κ f c).hom = refinement Λ (properIdentityRefinement c) ≫
          (properIdentityComparison Λ f).hom) ∧
      (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
          (c d : Compactification f) (r : c.Refinement d),
        refinement Λ r ≫ (κ f c).hom = (κ f d).hom) ∧
      (∀ {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
          [IsProper f] [IsProper f'] {w : X' ⟶ X} {v : Y' ⟶ Y}
          (sq : IsPullback w f' f v) (c : Compactification f) (c' : Compactification f')
          (s : Square c c' w v) (K : D Λ X),
        (squareExchange Λ s).app K ≫ (κ f' c').hom.app ((P Λ w).obj K) =
          (P Λ v).map ((κ f c).hom.app K) ≫
            (baseChangeMap Λ sq.toCommSq).app K) ∧
      (∀ {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
          [IsProper f] [IsProper f'] {w : X' ⟶ X} {v : Y' ⟶ Y}
          (sq : IsPullback w f' f v) (c : Compactification f) (c' : Compactification f')
          (s : Square c c' w v) (K : D Λ X),
        IsIso ((squareExchange Λ s).app K) ↔
          IsIso ((baseChangeMap Λ sq.toCommSq).app K)) := by
  classical
  refine ⟨properComparisonFamily Λ, ?_, ?_, ?_, ?_⟩
  · intro X Y f _hf c
    exact properComparisonFamily_hom Λ f c
  · intro X Y f _hf c d r
    have hcomp : (properIdentityRefinement c).comp r =
        properIdentityRefinement d := by
      ext
      dsimp [properIdentityRefinement, properIdentityRefinementForSquare]
      change c.i ≫ r.hom = d.i
      exact r.i_hom
    have href := (refinement_id_comp Λ c (properIdentityRefinement c) r).2
    rw [hcomp] at href
    rw [properComparisonFamily_hom Λ f c, properComparisonFamily_hom Λ f d]
    simpa only [Category.assoc] using
      congrArg (fun q => q ≫ (properIdentityComparison Λ f).hom) href.symm
  · intro X Y X' Y' f f' _hf _hf' w v sq c c' s K
    exact properRefinement_squareExchange_compatibility Λ sq c c' s K
  · intro X Y X' Y' f f' _hf _hf' w v sq c c' s K
    have h := properRefinement_squareExchange_compatibility Λ sq c c' s K
    rw [← isIso_comp_right_iff ((squareExchange Λ s).app K)
      ((properComparisonFamily Λ f' c').hom.app ((P Λ w).obj K))]
    change IsIso ((squareExchange Λ s).app K ≫
      (properRefinementComparisonForSquare Λ f' c').hom.app ((P Λ w).obj K)) ↔ _
    rw [h]
    rw [isIso_comp_left_iff]

end AlgebraicGeometry.ProEtale.CondensedRing
