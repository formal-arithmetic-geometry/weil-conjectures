/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Refinement.IntegralRefinementPastingData
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralNormalizedRefinementPasting
import WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.IntegralFiniteTorRefinementDiagram
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Refinement.IntegralRefinementTransposeRealization

/-! # The composition component of normalized integral refinement pasting -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
section OverProjection
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (o : Operations l E) (S : Realizations l E D o)
  {X Y : Over (Spec (CommRingCat.of D.k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
  (P : IntegralRefinementPastingData l E D hl f)

include S in

/-- Actual integral identity, composition, total-limit realization and outer-factor laws.
Source: blueprint exceptional inverse image, extracted normalized coefficient argument,
old step 10; Stacks 0F7B, 0F7C, 0F7D
(blueprint: lem-sf-integral-normalized-refinement-pasting).

Proof:
1. For a refinement u use the square (j_c,j_d,1_X,u). The intrinsic proper/open
mate transpose gives lambda P(g_u)=1. Semilinear mate pasting and ambient proper/open
pasting give g_vu=c_vu (S_v g_u) g_v and g_1=1 before evaluation.
2. The integral compactification system realization and generator reduction coherence
identify the realized g_u with the supplied e_u: both have the specified open-unit
transpose after the canonical restriction/clopen identification. Injectivity of the
open-adjunction Hom equivalence gives equality of actual arrows. Proper compositors
are identified by the same realization. All intermediate systems satisfy the assumed
normalized, witnessed common cohomology and Tor bounds.
3. The actual reconstruction counits on normalized systems are invertible by
lem-pur-normalized-actual-reconstruction-maps. Naturality expresses g_u as the
conjugate of reduction of its invertible realized map; hence g_u is invertible.
The forward system refinement is proper image of its inverse, after the inverse
proper compositor, precisely the inverse of completedShriekRefinement.
4. Invert step 1's equation. Naturality and associativity of the proper compositors
give t_v t_u=t_vu and t_1=1, with every intermediate compositor evaluated on J inputs.
5. The supplied normalization of rho gives I(rho_u)=a_d L(t_u) a_c inverse, where
a_c is c_Bc followed by r_c inverse. The recursive realization identifies the same
square after proper/open whiskering. Applying total limit to step 4 and cancelling
adjacent realization isomorphisms gives the asserted laws after inclusion. Its
faithfulness gives the actual integral identity and composition laws. Zero inputs
and empty opens give unique zero-object arrows; identity refinements use unitors.
No equality is detected by finite evaluation.
-/
private theorem integralNormalizedRefinementPasting_legacy
    (_compatible : ∀ c : Compactification f.left,
      ∃ η : F c ⋙ PurCompactSupport.finiteTorIntegralInclusion l E Y.left ≅
          PurCompactSupport.finiteTorIntegralInclusion l E X.left ⋙
            sfCompactSupportFiniteIntegralFunctor l D.k
              (PurCompactSupport.coefficientPrimeUnit l D hl) c E,
        ∀ K : finiteTorConstructibleIntegralCategory l E X.left,
          (r c).hom.app K = (sfIntegralConstructible l E Y.left).ι.map (η.hom.app K) ≫
            (sfQcqsCompactSupportRealization l E D.k
              (PurCompactSupport.coefficientPrimeUnit l D hl) c).inv.app
                ((PurCompactSupport.finiteTorIntegralInclusion l E X.left).obj K))
    (_transpose : ∀ (c d : Compactification f.left) (v : c.Refinement d)
      (K : finiteTorConstructibleIntegralCategory l E X.left),
      (ringedOpenAdj l E d.i).homEquiv _ _ ((e v).hom.app K) ≫
          PurCompactSupport.refinementRestriction (PurCompactSupport.completed l E) v
            (PurCompactSupport.completedPull_comp l E c.i v.hom) K.obj =
        (ringedOpenAdj l E c.i).unit.app K.obj)
    (_normalization : ∀ (c d : Compactification f.left) (v : c.Refinement d)
      (K : finiteTorConstructibleIntegralCategory l E X.left),
      (finiteTorConstructibleIntegral l E Y.left).ι.map ((ρ v).hom.app K) ≫
          (r d).hom.app K =
        (r c).hom.app K ≫
          ((ringedPushComp l E v.hom d.g ≪≫
            eqToIso (congrArg (ringedPush l E) v.hom_g)).inv.app
              ((ringedOpen l E c.i).obj K.obj)) ≫
          (ringedPush l E d.g).map ((e v).inv.app K))
    (hDiagram : ∀ (c : Fin 3 → Compactification f.left)
      (v : (c 0).Refinement (c 1)) (w : (c 1).Refinement (c 2))
      (K : finiteTorConstructibleIntegralCategory l E X.left) (q : Fin 18),
      (refinementDiagramWords f c v w (fun i ↦ inferInstance) q).2.domain l E o
        (fun _ ↦ K.obj)) :
    (∀ c : Compactification f.left, ρ (.id c) = Iso.refl (F c)) ∧
    (∀ (c d b : Compactification f.left) (v : c.Refinement d) (w : d.Refinement b),
      ρ (v.comp w) = ρ v ≪≫ ρ w) ∧
    (∀ (c d : Compactification f.left) (v : c.Refinement d)
      (K : finiteTorConstructibleIntegralCategory l E X.left),
      IsIso ((completedShriekRefinement l E R v).app
        ((calculus l E X.left).reduction.obj K.obj)) ∧
      (finiteTorConstructibleIntegral l E Y.left).ι.map ((ρ v).hom.app K) ≫
          (r d).hom.app K =
        (r c).hom.app K ≫
          (R.comparison (normalizedRefinementWord f c)
            (normalizedRefinementGeometric f c)).inv.app
              ⟨(fun _ ↦ K.obj), hDiagram (fun _ ↦ c) (.id c) (.id c) K 15⟩ ≫
          (coefficientSequenceLimit l E Y.left).map
            (normalizedRefinementSystemMap l E R v
              ((calculus l E X.left).reduction.obj K.obj)) ≫
          (R.comparison (normalizedRefinementWord f d)
            (normalizedRefinementGeometric f d)).hom.app
              ⟨(fun _ ↦ K.obj), hDiagram (fun _ ↦ d) (.id d) (.id d) K 15⟩) ∧
    (∀ (c d : Compactification f.left) (v : c.Refinement d)
      (K : finiteTorConstructibleIntegralCategory l E X.left)
      {W : Over (Spec (CommRingCat.of D.k))}
      (q : NormalizedRefinementContext _ Y W)
      (gc : (q.plug (normalizedRefinementWord f c)).geometric)
      (gd : (q.plug (normalizedRefinementWord f d)).geometric)
      (hc : (q.plug (normalizedRefinementWord f c)).domain l E o (fun _ ↦ K.obj))
      (hd : (q.plug (normalizedRefinementWord f d)).domain l E o (fun _ ↦ K.obj)),
      (q.evaluate (integralInterpretation l E)).map
          ((r c).inv.app K ≫
            (finiteTorConstructibleIntegral l E Y.left).ι.map ((ρ v).hom.app K) ≫
            (r d).hom.app K) =
        (q.realization l E R (normalizedRefinementWord f c) gc (fun _ ↦ K.obj) hc).inv ≫
          (coefficientSequenceLimit l E W.left).map
            ((q.evaluate (systemInterpretation l E o)).map
              (normalizedRefinementSystemMap l E R v
                ((calculus l E X.left).reduction.obj K.obj))) ≫
          (q.realization l E R (normalizedRefinementWord f d) gd (fun _ ↦ K.obj) hd).hom) := by
  classical
  let L := coefficientSequenceLimit l E Y.left
  let I := (finiteTorConstructibleIntegral l E Y.left).ι
  let M (K : finiteTorConstructibleIntegralCategory l E X.left) :=
    (calculus l E X.left).reduction.obj K.obj
  let a (c : Compactification f.left)
      (K : finiteTorConstructibleIntegralCategory l E X.left) :=
    (R.comparison (normalizedRefinementWord f c) (normalizedRefinementGeometric f c)).app
      ⟨(fun _ ↦ K.obj), hDiagram (fun _ ↦ c) (.id c) (.id c) K 15⟩
  have hDom (c : Compactification f.left)
      (K : finiteTorConstructibleIntegralCategory l E X.left) :
      completedShriekDomain l E o c (M K) := by
    have h := hDiagram (fun _ ↦ c) (.id c) (.id c) K 15
    exact ⟨h.2.2.1.1, h.2.2.2, h.2.1⟩
  have laws := completedShriekRefinementLaws l E D hl o R (f := f.left)
  have hIso (c d : Compactification f.left) (v : c.Refinement d)
      (K : finiteTorConstructibleIntegralCategory l E X.left) :
      IsIso ((completedShriekRefinement l E R v).app (M K)) :=
    laws.2.2.1 c d v (M K) (hDom c K) (hDom d K)
  have hId (c : Compactification f.left)
      (K : finiteTorConstructibleIntegralCategory l E X.left) :
      normalizedRefinementSystemMap l E R (.id c) (M K) = 𝟙 _ := by
    have := hIso c c (.id c) K
    simp only [normalizedRefinementSystemMap_eq_inv, laws.1 c (M K), IsIso.inv_id]
  have hComp (c d b : Compactification f.left) (v : c.Refinement d)
      (w : d.Refinement b) (K : finiteTorConstructibleIntegralCategory l E X.left) :
      normalizedRefinementSystemMap l E R (v.comp w) (M K) =
        normalizedRefinementSystemMap l E R v (M K) ≫
          normalizedRefinementSystemMap l E R w (M K) := by
    have := hIso c d v K
    have := hIso d b w K
    have := hIso c b (v.comp w) K
    simp only [normalizedRefinementSystemMap_eq_inv,
      laws.2.1 c d b v w, NatTrans.comp_app, IsIso.inv_comp]
  let t (c d : Compactification f.left) (v : c.Refinement d)
      (K : finiteTorConstructibleIntegralCategory l E X.left) :=
    ((ringedPushComp l E v.hom d.g ≪≫
      eqToIso (congrArg (ringedPush l E) v.hom_g)).app
        ((ringedOpen l E c.i).obj K.obj)).symm ≪≫
      (ringedPush l E d.g).mapIso ((e v).app K).symm
  have hOuter (c d : Compactification f.left) (v : c.Refinement d)
      (K : finiteTorConstructibleIntegralCategory l E X.left)
      {W : Over (Spec (CommRingCat.of D.k))}
      (q : NormalizedRefinementContext _ Y W)
      (gc : (q.plug (normalizedRefinementWord f c)).geometric)
      (gd : (q.plug (normalizedRefinementWord f d)).geometric)
      (hc : (q.plug (normalizedRefinementWord f c)).domain l E o (fun _ ↦ K.obj))
      (hd : (q.plug (normalizedRefinementWord f d)).domain l E o (fun _ ↦ K.obj)) :
      (q.evaluate (integralInterpretation l E)).map (t c d v K).hom =
        (q.realization l E R (normalizedRefinementWord f c) gc (fun _ ↦ K.obj) hc).inv ≫
          (coefficientSequenceLimit l E W.left).map
            ((q.evaluate (systemInterpretation l E o)).map
              (normalizedRefinementSystemMap l E R v (M K))) ≫
          (q.realization l E R (normalizedRefinementWord f d) gd (fun _ ↦ K.obj) hd).hom := by
    have := hIso c d v K
    have h := integralRefinementTransposeRealization l E D hl o R f K
      (fun cs v w i ↦ hDiagram cs v w K i) c d v ((e v).app K)
      (_transpose c d v K) q gc gd hc hd
    have h' := forward_of_reverse_square (coefficientSequenceLimit l E W.left)
      ((q.evaluate (systemInterpretation l E o)).map
        ((completedShriekRefinement l E R v).app (M K)))
      (q.realization l E R (normalizedRefinementWord f c) gc (fun _ ↦ K.obj) hc)
      (q.realization l E R (normalizedRefinementWord f d) gd (fun _ ↦ K.obj) hd)
      ((q.evaluate (integralInterpretation l E)).mapIso (t c d v K)) h
    simpa only [Functor.mapIso_hom, ← Functor.map_inv,
      normalizedRefinementSystemMap_eq_inv] using h'
  have hBase (c d : Compactification f.left) (v : c.Refinement d)
      (K : finiteTorConstructibleIntegralCategory l E X.left) :
      (t c d v K).hom =
        (a c K).inv ≫ L.map (normalizedRefinementSystemMap l E R v (M K)) ≫
          (a d K).hom := by
    have h := hOuter c d v K .hole (normalizedRefinementGeometric f c)
      (normalizedRefinementGeometric f d)
      (hDiagram (fun _ ↦ c) (.id c) (.id c) K 15)
      (hDiagram (fun _ ↦ d) (.id d) (.id d) K 15)
    dsimp [NormalizedRefinementContext.realization,
      NormalizedRefinementContext.evaluationIso, NormalizedRefinementContext.evaluate,
      NormalizedRefinementContext.plug] at h
    erw [L.map_id, L.map_id] at h
    erw [Category.id_comp, Category.comp_id, Category.id_comp, Category.comp_id] at h
    exact h
  have hMap (c d : Compactification f.left) (v : c.Refinement d)
      (K : finiteTorConstructibleIntegralCategory l E X.left) :
      I.map ((ρ v).hom.app K) ≫ (r d).hom.app K =
        (r c).hom.app K ≫ (a c K).inv ≫
          L.map (normalizedRefinementSystemMap l E R v (M K)) ≫ (a d K).hom := by
    rw [_normalization c d v K]
    change (r c).hom.app K ≫ (t c d v K).hom = _
    rw [hBase]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    apply Iso.ext
    apply NatTrans.ext
    funext K
    apply I.map_injective
    apply (cancel_mono ((r c).hom.app K)).mp
    have h := hMap c c (.id c) K
    rw [hId] at h
    erw [L.map_id] at h
    erw [Category.id_comp, (a c K).inv_hom_id, Category.comp_id] at h
    simpa only [Iso.refl_hom, NatTrans.id_app, I.map_id, Category.id_comp] using h
  · intro c d b v w
    apply Iso.ext
    apply NatTrans.ext
    funext K
    apply I.map_injective
    apply (cancel_mono ((r b).hom.app K)).mp
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
    rw [hMap c b (v.comp w) K, hMap d b w K]
    simp only [← Category.assoc]
    rw [hMap c d v K]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, hComp, Functor.map_comp]
  · intro c d v K
    exact ⟨hIso c d v K, hMap c d v K⟩
  · intro c d v K W q gc gd hc hd
    have h := _normalization c d v K
    have h' : (r c).inv.app K ≫ I.map ((ρ v).hom.app K) ≫ (r d).hom.app K =
        (t c d v K).hom := by
      rw [h]
      simp only [Iso.inv_hom_id_app_assoc]
      rfl
    rw [h']
    exact hOuter c d v K q gc gd hc hd

/-- The composition component of normalized integral refinement pasting.
Source: `integralNormalizedRefinementPasting` and finite-Tor diagram admissibility.
(blueprint: lem-sf-integral-refinement-composition-pasting-projection).
Proof: extract all eighteen domain witnesses from the common Tor interval, apply
normalized pasting to the fields of the data and normalization records, and take
its composition conjunct. -/
theorem integralRefinementCompositionPastingProjection
    (hnormalization : IntegralRefinementPastingData.Normalized l E D hl f P) :
    ∀ (c d b : Compactification f.left) (v : c.Refinement d) (w : d.Refinement b),
      P.ρ (v.comp w) = P.ρ v ≪≫ P.ρ w := by
  have hDiagram (c : Fin 3 → Compactification f.left)
      (v : (c 0).Refinement (c 1)) (w : (c 1).Refinement (c 2))
      (K : finiteTorConstructibleIntegralCategory l E X.left) (q : Fin 18) :
      (refinementDiagramWords f c v w (fun _ ↦ inferInstance) q).2.domain l E o
        (fun _ ↦ K.obj) :=
    integralFiniteTorRefinementDiagram l E D hl o S f c v w (fun _ ↦ inferInstance) K q
  exact (integralNormalizedRefinementPasting_legacy l E D hl o S f P.F P.r P.ρ P.e
    P.compatible P.transpose hnormalization.equation hDiagram).2.1

/-- Composition of prescribed identity-on-open maps, with the canonical derived compositor.
Source: current blueprint `det-sf-comp-coherence-refinement`, clause (3).
(blueprint: lem-sfb-prescribed-refinement-composition).
Proof: apply prescribed refinement pasting to the normalized family and take its
composition conjunct. The input is any unbounded complex; no finite evaluation
or localizing-domain hypothesis is needed for this equality. -/
theorem prescribedRefinementCompositionPastingProjection
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (b : ∀ (c d : Compactification.DenseBoundaryCompactification f) (r : d ⟶ c)
      (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      (openImmersionLowerShriek Λ c.obj.obj.obj.i).mapDerivedCategory.obj K ⟶
        (lowerStar Λ r.hom.hom.hom.hom).rightDerivedFunctor.obj
          ((openImmersionLowerShriek Λ d.obj.obj.obj.i).mapDerivedCategory.obj K))
    (hnormalized : ∀ (c d : Compactification.DenseBoundaryCompactification f)
      (r : d ⟶ c) (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.obj.i).unit.app K ≫
          (upperStar Λ c.obj.obj.obj.i).mapDerivedCategory.map (b c d r K) ≫
            (refinementTheta Λ r.hom K).hom = 𝟙 K) :
    (∀ (c d e : Compactification.DenseBoundaryCompactification f)
      (r : d ⟶ c) (s : e ⟶ d) K,
      b c e (s ≫ r) K ≫
          (refinementDerivedLowerStarComp Λ s.hom.hom.hom.hom r.hom.hom.hom.hom).hom.app
            ((openImmersionLowerShriek Λ e.obj.obj.obj.i).mapDerivedCategory.obj K) =
        b c d r K ≫ (lowerStar Λ r.hom.hom.hom.hom).rightDerivedFunctor.map
          (b d e s K)) := by
  exact (integralNormalizedRefinementPasting Λ ℓ k p hp hpℓ hΛ f b hnormalized).2.2.2

end OverProjection
end WeilConjectures.IntegralSystemRealization
