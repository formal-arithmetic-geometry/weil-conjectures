/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurIntegralRepresentingPairData
import WeilConjectures.AlgebraicGeometry.PurPointwiseCoordinatePair
import WeilConjectures.AlgebraicGeometry.CoefficientSingleDegreeEvaluationFaithfulness

/-! # Coordinate representing families

Source: blueprint integral adjunction, coordinate Hom chain and actual counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [-instance] WeilConjectures.integralExceptionalSystemDerived
attribute [-instance] WeilConjectures.integralExceptionalLevelDerived
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModules
open WeilConjectures AlgebraicGeometry.Scheme
attribute [local instance 5000] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
namespace WeilConjectures.PurIntegralRepresentingPair
open PurIntegralSupportComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  (S : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) c)
  (G : EtaleTowerBrownAdjunction S) (H : BrownTowerComparison.FiniteEvaluation S G)
  (D : BrownTowerComparison.TransportData S G H)

private theorem transportCounit_naturality
    (hD : BrownTowerComparison.Transport S G H D (finite := D.finite))
    (C C' : DerivedCategory (BrownTowerComparison.ProSystem Y
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)))
    (hC : D.siteY.Origin C) (hC' : D.siteY.Origin C')
    (hn : IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology Y)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)
      D.siteY.proEvaluation C)
    (hn' : IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology Y)
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)
      D.siteY.proEvaluation C')
    (hc : ∀ n, FiniteCoefficientAdjoints.ctf
      (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
        (integralExceptionalUniformizer l E) n) Y
      ((D.siteY.realization n).derived.obj ((D.siteY.proEvaluation.evaluation n).obj C)))
    (hc' : ∀ n, FiniteCoefficientAdjoints.ctf
      (BrownTowerComparison.Ring (integralExceptionalIntegers l E)
        (integralExceptionalUniformizer l E) n) Y
      ((D.siteY.realization n).derived.obj ((D.siteY.proEvaluation.evaluation n).obj C')))
    (hb : ∃ a : ℤ, ∀ n,
      ((BrownTowerComparison.finiteExceptional S G H D.siteX D.siteY n).obj
        ((D.siteY.proEvaluation.evaluation n).obj C)).IsGE a)
    (hb' : ∃ a : ℤ, ∀ n,
      ((BrownTowerComparison.finiteExceptional S G H D.siteX D.siteY n).obj
        ((D.siteY.proEvaluation.evaluation n).obj C')).IsGE a)
    (b : C ⟶ C') :
    D.compact.functor.map ((brown l E S G H D).map b) ≫ D.counit C' hC' hn' hc' hb' =
      D.counit C hC hn hc hb ≫ b := by
  let := D.finite
  obtain ⟨a, ha⟩ := hb
  have hi := hD.compact_iso (G.right.obj (D.siteY.direct.obj C))
    ⟨a, (hD.bound C hC hn hc a ha).1⟩
  apply (cancel_epi (D.compactComparison.app (G.right.obj (D.siteY.direct.obj C)))).mp
  rw [← Category.assoc]
  have ht := D.compactComparison.naturality (G.right.map (D.siteY.direct.map b))
  dsimp only [Functor.comp_map, brown] at ht ⊢
  rw [← ht, Category.assoc, hD.counit_formula]
  rw [← Category.assoc (D.compactComparison.app _) (D.counit C hC hn hc _) b,
    hD.counit_formula]
  simp only [Category.assoc]
  have hg := G.adjunction.counit.naturality (D.siteY.direct.map b)
  dsimp only [Functor.comp_map, Functor.id_map] at hg
  rw [← Functor.map_comp_assoc, hg, Functor.map_comp, Category.assoc]
  have hy := D.siteY.adjunction.counit.naturality b
  dsimp only [Functor.comp_map, Functor.id_map] at hy
  rw [hy]

private theorem pairHom_natural_right
    (RX : CoefficientDerivedSystemCalculus l E X)
    (RY : CoefficientDerivedSystemCalculus l E Y)
    (hD : BrownTowerComparison.Transport S G H D (finite := D.finite))
    (L L' : CondensedERealization.Integral l E Y)
    (A : Supplied l E RX RY S G H D L) (A' : Supplied l E RX RY S G H D L')
    (P : Pair l E RX RY S G H D L A hD) (P' : Pair l E RX RY S G H D L' A' hD)
    (b : L ⟶ L') (a : A.system ⟶ A'.system)
    (ha : a ≫ P'.theta.hom = P.theta.hom ≫
      (brown l E S G H D).map ((reduction l E Y RY).map b.hom))
    (K : CondensedERealization.Integral l E X) (h : K ⟶ A.object) :
    P'.hom K (ObjectProperty.homMk (h.hom ≫ (totalLimit l E X).map a)) =
      P.hom K h ≫ b.hom := by
  let := D.finite
  let := P.unit_iso
  let := P'.unit_iso
  have hε := transportCounit_naturality l E S G H D hD _ _
    P.origin P'.origin P.normalized P'.normalized P.finiteTor P'.finiteTor
    P.lowerBound P'.lowerBound ((reduction l E Y RY).map b.hom)
  have hc := (adjunction l E X RX).counit.naturality a
  dsimp only [Functor.comp_map, Functor.id_map] at hc
  have hu := (adjunction l E Y RY).unit.naturality b.hom
  dsimp only [Functor.comp_map, Functor.id_map] at hu
  have hui : (totalLimit l E Y).map ((reduction l E Y RY).map b.hom) ≫
      inv ((adjunction l E Y RY).unit.app L'.obj) =
    inv ((adjunction l E Y RY).unit.app L.obj) ≫ b.hom := by
    apply (cancel_epi ((adjunction l E Y RY).unit.app L.obj)).1
    rw [← Category.assoc, ← hu]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id,
      IsIso.hom_inv_id_assoc]
  rw [P'.hom_formula, P.hom_formula]
  dsimp only [transpose, ObjectProperty.homMk_hom]
  have ht : (reduction l E X RX).map (h.hom ≫ (totalLimit l E X).map a) ≫
      (adjunction l E X RX).counit.app A'.system ≫ P'.theta.hom =
    ((reduction l E X RX).map h.hom ≫
      (adjunction l E X RX).counit.app A.system ≫ P.theta.hom) ≫
        (brown l E S G H D).map ((reduction l E Y RY).map b.hom) := by
    rw [Functor.map_comp, Category.assoc, ← Category.assoc _ _ P'.theta.hom,
      hc, Category.assoc, ha]
    simp only [Category.assoc]
  have he : alpha l E RX RY S G H D K.obj ≫
      D.compact.functor.map
        ((reduction l E X RX).map (h.hom ≫ (totalLimit l E X).map a) ≫
          (adjunction l E X RX).counit.app A'.system ≫ P'.theta.hom) ≫
        D.counit _ P'.origin P'.normalized P'.finiteTor P'.lowerBound =
      (alpha l E RX RY S G H D K.obj ≫
        D.compact.functor.map ((reduction l E X RX).map h.hom ≫
          (adjunction l E X RX).counit.app A.system ≫ P.theta.hom) ≫
        D.counit _ P.origin P.normalized P.finiteTor P.lowerBound) ≫
          (reduction l E Y RY).map b.hom := by
    rw [ht, Functor.map_comp]
    simp only [Category.assoc]
    rw [hε]
  rw [he, Functor.map_comp]
  simp only [Category.assoc]
  rw [hui]

/-- The representing Hom chain in quotient coordinates, including normalized theta,
its finite counit equation and naturality on actual supplied system maps.
Source: current blueprint sk-prop-sp-integral-adjunction, Hom display and final
unit/counit paragraph (blueprint: lem-route-coordinate-representing-family).

Proof: apply uniform integral reduction to the input and test objects to obtain the
finite Tor bounds and etale-origin witnesses. Transfer the supplied finite interval
through phi to bound the exceptional outputs. Apply Brown transport to these inputs.
In recognition mode (a) retain theta. In mode (b), exact conservative evaluations
detect concentration of both systems; the transition squares on H^r give an actual
strict-system isomorphism. Conjugate it by the H^r-normalized good truncations to
obtain theta and use full faithfulness of the shifted heart for common-degree squares.
Intrinsic completeness and normalized reconstruction invert the actual units and
counits. The support object is integral because supportPresentation identifies it
with rawSupport, which the integral model preserves. Compose reduction/limit Hom,
theta, Brown Hom, and the inverse reduction Hom map. These maps are linear and natural
and their composite is precisely transpose. Apply this formula to the identity and
use the adjunction triangles to obtain trace_reduction. Evaluate that equality and
paste the Brown finite counit normalization to obtain trace_evaluation. Naturality
of all four Hom maps gives the two family naturality equations. -/
theorem coordinateRepresentingFamily
    (p : ℕ) [Fact p.Prime] (_hpl : p ≠ l)
    (k : Type u) [Field k] [CharP k p]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [f.IsOver (Spec (.of k))]
    (R : ∀ W : Scheme.{u}, CoefficientDerivedSystemCalculus l E W)
    (M : CompactSupportCondensedRealization.IntegralModel l E c R)
    (hD : BrownTowerComparison.Transport S G H D (finite := D.finite)) :
    Nonempty (Family l E (R X) (R Y) S G H D hD) := by
  classical
  let P (L : CondensedERealization.Integral l E Y)
      (A : Supplied l E (R X) (R Y) S G H D L) :=
    Classical.choice (pointwiseCoordinatePair l E S G H D p _hpl k R M hD L A)
  refine ⟨{
    pair := P
    hom_natural := ?_
    trace_natural := ?_
    single_degree_square := ?_ }⟩
  · intro L L' A A' b a ha K h
    exact pairHom_natural_right l E S G H D (R X) (R Y) hD
      L L' A A' (P L A) (P L' A') b a ha K h
  · intro L L' A A' b a ha
    let aI : A.object ⟶ A'.object :=
      ObjectProperty.homMk ((totalLimit l E X).map a)
    have hleft := (P L' A').hom_natural A'.object A.object aI (𝟙 A'.object)
    have hright := pairHom_natural_right l E S G H D (R X) (R Y) hD
      L L' A A' (P L A) (P L' A') b a ha A.object (𝟙 A.object)
    simp only [Category.comp_id] at hleft
    simp only [ObjectProperty.FullSubcategory.id_hom, Category.id_comp] at hright
    exact hleft.symm.trans hright
  · intro L L' A A' r b a hA hA' hs
    have he : a = (P L A).theta.hom ≫
        (brown l E S G H D).map ((reduction l E Y (R Y)).map b.hom) ≫
          (P L' A').theta.inv := by
      apply singleDegreeEvaluation_hom_ext X
        (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)
        D.siteX.proEvaluation A.system A'.system r hA hA'
      intro n
      apply (cancel_mono ((D.siteX.proEvaluation.evaluation n).map
        (P L' A').theta.hom)).1
      rw [← Functor.map_comp, ← Functor.map_comp]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.map_comp]
      rw [(P L A).theta_evaluation, (P L' A').theta_evaluation]
      exact hs n
    rw [he]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end WeilConjectures.PurIntegralRepresentingPair
