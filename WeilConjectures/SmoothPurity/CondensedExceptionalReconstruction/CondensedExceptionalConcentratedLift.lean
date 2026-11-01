/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CondensedExceptionalReconstruction.Datum.ExceptionalReconstructionComparison

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
        (d.toBrown l k n).hom := by sorry

end WeilConjectures.CondensedExceptionalReconstruction
