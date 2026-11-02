/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CondensedExceptionalReconstruction.Datum.ExceptionalReconstructionComparison
import WeilConjectures.SmoothPurity.PurIntegralSupportComparison.PurIntegralSupportComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.GoodTruncationNormalization
import WeilConjectures.AlgebraicGeometry.BrownTowerComparison.BrownTowerRealization
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Recognition steps for supplied strict coefficient systems

Source: current blueprint integral-adjunction reconstruction and unit/counit paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
attribute [local instance high] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
  WeilConjectures.PurityFiniteSetting.clopenProEtaleSystemDerived
  WeilConjectures.PurityFiniteSetting.clopenProEtaleLevelDerived
attribute [local semireducible] AlgebraicGeometry.exceptionalProSystemDerived
  AlgebraicGeometry.exceptionalProLevelDerived
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedExceptionalReconstruction
open CondensedERealization CompactSupportCondensedRealization PurityFiniteSetting
variable (l : ℕ) [Fact l.Prime] (k : Type u) [_root_.Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [local irreducible] WeilConjectures.purCoefficientModel
variable {X Y : Base k} {f : X.scheme ⟶ Y.scheme}
  [f.IsOver (Spec (.of k))] {c : Compactification f}
  (P : Context l k X Y f c)

/-- Compatible finite identifications lift for systems concentrated in one common degree.
No constructibility, normalization, reconstruction, or geometric unit assertion is included.
Source: blueprint sk-prop-sp-integral-adjunction, tower reconstruction; parent recognition
proof Step 2 (blueprint: lem-pur-condensed-exceptional-concentrated-lift).

Proof: evaluation is exact and commutes with cohomology. Joint conservativity of the
ordinary evaluations detects zero cohomology, so the degree hypothesis and the supplied
finite isomorphisms put both the supplied and Brown systems in degree r. Conjugate the
H^r maps of toBrown by the exact-evaluation cohomology comparisons. The transition
squares, and the representative normalization of the derived transitions, identify these
maps with a morphism between the strict H^r coefficient systems. Each component is an
isomorphism, so its inverses also commute with transitions and give the inverse strict
system map. Identify each derived system with its strict H^r system placed in degree r
by good truncation normalized by identity on H^r. Conjugate the strict-system isomorphism
by these identifications. Exact-functor compatibility of good truncation and full
faithfulness of the shifted-heart embedding show that its evaluations are precisely
toBrown. In particular this isomorphism is unique with those evaluations: apply H^r,
ordinary componentwise extensionality, and shifted-heart faithfulness. This constructs
no lift of maps between arbitrary derived systems. -/
theorem condensed_exceptional_concentrated_lift
    (d : Datum l k P) (ht : d.Transitions l k) (r : ℤ)
    (hdeg : ∀ n : ℕ,
      ((P.source.proEtaleEvaluation.evaluation n).obj d.tower).IsGE r ∧
      ((P.source.proEtaleEvaluation.evaluation n).obj d.tower).IsLE r) :
    ∃ theta : d.tower ≅ brownTower l k P d.L,
      ∀ n : ℕ, (P.source.proEtaleEvaluation.evaluation n).map theta.hom =
        (d.toBrown l k n).hom := by
  classical
  let E := P.source.proEtaleEvaluation
  let N := brownTower l k P d.L
  have hN (n : ℕ) : ((E.evaluation n).obj N).IsGE r ∧
      ((E.evaluation n).obj N).IsLE r := by
    let := (hdeg n).1
    let := (hdeg n).2
    exact ⟨DerivedCategory.TStructure.t.isGE_of_iso (d.toBrown l k n) r,
      DerivedCategory.TStructure.t.isLE_of_iso (d.toBrown l k n) r⟩
  obtain ⟨hVge, hVle⟩ := concentrated_of_evaluations
    (W := X.scheme) (O := clopenSystemRing l (Field.{u} l))
    (t := clopenSystemUniformizer l (Field.{u} l)) E d.tower r hdeg
  obtain ⟨hNge, hNle⟩ := concentrated_of_evaluations
    (W := X.scheme) (O := clopenSystemRing l (Field.{u} l))
    (t := clopenSystemUniformizer l (Field.{u} l)) E N r hN
  let := hVge
  let := hVle
  let := hNge
  let := hNle
  obtain ⟨deltaV, _⟩ := normalized_single_iso d.tower r
  obtain ⟨deltaN, _⟩ := normalized_single_iso N r
  let p (n : ℕ) := (E.evaluation n).map deltaV.inv ≫ (d.toBrown l k n).hom ≫
    (E.evaluation n).map deltaN.hom
  have hp (m n : ℕ) (h : n ≤ m) :
      (E.transition h).app _ ≫ (E.scalar h).restriction.map (p n) =
        p m ≫ (E.transition h).app _ := by
    dsimp only [p]
    simp only [Functor.map_comp, Category.assoc]
    have hv := (E.transition h).naturality deltaV.inv
    have hn := (E.transition h).naturality deltaN.hom
    dsimp only [Functor.comp_map] at hv hn
    rw [← reassoc_of% hv]
    change _ ≫ ((E.transition h).app d.tower ≫ _ ≫ _) = _
    rw [reassoc_of% (ht h)]
    rw [hn]
  obtain ⟨a, ha⟩ := lift_single_family
    (W := X.scheme) (O := clopenSystemRing l (Field.{u} l))
    (t := clopenSystemUniformizer l (Field.{u} l)) E r
    ((DerivedCategory.homologyFunctor _ r).obj d.tower)
    ((DerivedCategory.homologyFunctor _ r).obj N) p hp
  let b := deltaV.hom ≫ (DerivedCategory.singleFunctor _ r).map a ≫ deltaN.inv
  have hb (n : ℕ) : (E.evaluation n).map b = (d.toBrown l k n).hom := by
    dsimp only [b]
    rw [Functor.map_comp, Functor.map_comp, ha]
    simp only [p, Category.assoc]
    rw [← Functor.map_comp, deltaN.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
    rw [← Functor.map_comp_assoc, deltaV.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have : IsIso b := by
    apply (P.source.derived.detectsIso b).2
    intro n
    rw [hb n]
    infer_instance
  exact ⟨asIso b, hb⟩

end WeilConjectures.CondensedExceptionalReconstruction
