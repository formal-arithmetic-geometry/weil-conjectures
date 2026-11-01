/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefDualFormulaScalarData
import all WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefRelativeTraceReduction
import WeilConjectures.SixFunctors.Integral.IntegralConstructibleAdjacentReductionHom
import WeilConjectures.SixFunctors.Compact.CompactSupportReductionCoherence
import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefDualFormulaPairingPerfect
import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefDualFormulaPairingScalar

/-!
# Scalar transpose of the canonical integral exceptional formula

Source: blueprint main-20261015, lem-coef-rational-operations, proof paragraph 8,
Step 15 (blueprint: lem-coef-dual-formula-scalar-transpose).

The trace and evaluation normalizations below specify the formula comparison.
They exclude rescaling an otherwise unspecified exceptional-formula isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CoefDualFormulaScalarTranspose

private theorem iso_of_pairings {C : Type*} [Category C] (H G : C)
    (P : C → Type*) (A : ∀ K, (K ⟶ H) → P K) (B : ∀ K, (K ⟶ G) → P K)
    (ha : ∀ K, Function.Bijective (A K)) (hb : ∀ K, Function.Bijective (B K))
    (pre : ∀ {K K'}, (K ⟶ K') → P K' → P K)
    (an : ∀ {K K'} (v : K ⟶ K') (h : K' ⟶ H),
      A K (v ≫ h) = pre v (A K' h))
    (bn : ∀ {K K'} (v : K ⟶ K') (g : K' ⟶ G),
      B K (v ≫ g) = pre v (B K' g)) :
    ∃! k : G ≅ H, A G k.hom = B G (𝟙 G) := by
  let e (K : C) : (K ⟶ H) ≃ (K ⟶ G) :=
    (Equiv.ofBijective (A K) (ha K)).trans (Equiv.ofBijective (B K) (hb K)).symm
  have he (K : C) (h : K ⟶ H) : B K (e K h) = A K h := by
    exact (Equiv.ofBijective (B K) (hb K)).apply_symm_apply _
  have hn {K K' : C} (v : K ⟶ K') (h : K' ⟶ H) :
      e K (v ≫ h) = v ≫ e K' h := by
    apply (hb K).injective
    rw [he, bn, he, an]
  let k := (e G).symm (𝟙 G)
  let j := e H (𝟙 H)
  have hk : e G k = 𝟙 G := (e G).apply_symm_apply _
  have hkj : k ≫ j = 𝟙 G := by
    simpa only [Category.comp_id, j, hk] using (hn k (𝟙 H)).symm
  have hjk : j ≫ k = 𝟙 H := by
    apply (e H).injective
    rw [hn, hk, Category.comp_id]
  refine ⟨⟨k, j, hkj, hjk⟩, ?_, ?_⟩
  · change A G k = B G (𝟙 G)
    rw [← he, hk]
  · intro k' hk'
    apply Iso.ext
    apply (ha G).injective
    change A G k'.hom = A G k
    rw [hk', ← he, hk]

private theorem coherent_trace_family
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (Fm : A ⥤ B) (Fn : C ⥤ D) (SX : C ⥤ A) (SY : D ⥤ B)
    (e : SX ⋙ Fm ≅ Fn ⋙ SY)
    {a1 w1 : A} {a0 w0 : C} {b1 z1 p1 : B} {b0 z0 p0 : D}
    (ex1 : a1 ≅ w1) (ex0 : a0 ≅ w0) (ey1 : b1 ≅ z1) (ey0 : b0 ≅ z0)
    (r1 : p1 ≅ Fm.obj a1) (r0 : p0 ≅ Fn.obj a0)
    (tx : a1 ⟶ SX.obj a0) (ty : b1 ⟶ SY.obj b0)
    (ux : w1 ⟶ SX.obj w0) (uy : z1 ⟶ SY.obj z0) (tp : p1 ⟶ SY.obj p0)
    (t1 : Fm.obj w1 ⟶ z1) (t0 : Fn.obj w0 ⟶ z0)
    (hx : tx ≫ SX.map ex0.hom = ex1.hom ≫ ux)
    (hy : ty ≫ SY.map ey0.hom = ey1.hom ≫ uy)
    (hr : r1.hom ≫ Fm.map tx ≫ e.hom.app a0 = tp ≫ SY.map r0.hom)
    (ht : t1 ≫ uy = Fm.map ux ≫ e.hom.app w0 ≫ SY.map t0) :
    (r1.hom ≫ Fm.map ex1.hom ≫ t1 ≫ ey1.inv) ≫ ty =
      tp ≫ SY.map (r0.hom ≫ Fn.map ex0.hom ≫ t0 ≫ ey0.inv) := by
  have hy' : ey1.inv ≫ ty = uy ≫ SY.map ey0.inv := by
    apply (Iso.cancel_iso_hom_left ey1 _ _).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← hy]
    simp only [Category.assoc, ← SY.map_comp, Iso.hom_inv_id, SY.map_id,
      Category.comp_id]
  have hn := e.hom.naturality ex0.hom
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [hy', reassoc_of% ht]
  simp only [← Fm.map_comp_assoc]
  rw [← hx]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hr]

private theorem cancel_trace_tail
    {C : Type*} [Category C] {x y z w v : C}
    (a : x ⟶ y) (b : y ⟶ z) (c : z ⟶ w) (e : v ≅ w) :
    (a ≫ b ≫ c ≫ e.inv) ≫ e.hom = a ≫ b ≫ c := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem eq_trace_tail
    {C : Type*} [Category C] {x y z w v : C}
    (g : x ⟶ v) (a : x ⟶ y) (b : y ⟶ z) (c : z ⟶ w) (e : v ≅ w)
    (h : g ≫ e.hom = a ≫ b ≫ c) : g = a ≫ b ≫ c ≫ e.inv := by
  have h' := (Iso.eq_comp_inv e).mpr h
  simpa only [Category.assoc] using h'

private theorem tensor_precomp
    {C D : Type*} [Category C] [Category D] (T : C × C ⥤ D)
    {x y z n : C} {w : D} (v : x ⟶ y) (g : y ⟶ z)
    (e : T.obj (z, n) ⟶ w) :
    T.map (Prod.mkHom (v ≫ g) (𝟙 n)) ≫ e =
      T.map (Prod.mkHom v (𝟙 n)) ≫ T.map (Prod.mkHom g (𝟙 n)) ≫ e := by
  rw [← Category.assoc, ← T.map_comp]
  congr 2
  exact Prod.hom_ext rfl (Category.id_comp _).symm

private theorem adjunction_comparison_natural
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (U : C ⥤ A) (V : D ⥤ B) (S : A ⥤ B) (eta : U ⋙ S ≅ F ⋙ V)
    {K K' : C} {M : D} (v : K ⟶ K') (g : K' ⟶ G.obj M) :
    eta.hom.app K ≫ V.map ((adj.homEquiv K M).symm (v ≫ g)) =
      S.map (U.map v) ≫ eta.hom.app K' ≫ V.map ((adj.homEquiv K' M).symm g) := by
  rw [adj.homEquiv_naturality_left_symm, V.map_comp]
  have he := eta.hom.naturality v
  dsimp only [Functor.comp_map] at he
  rw [← Category.assoc, ← he, Category.assoc]

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)

private theorem finiteTraceFamily_coherent
    (wX : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wY : IntegralFiniteExtension.DualizingDatum l Y D hl E) (n : ℕ) :
    let a (k : ℕ) :=
      (sfCompactSupportFiniteReductionIso l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c E wX.omega k).hom ≫
      (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (k + 1)) c).map
        (wX.reduction k).hom ≫ finiteTrace D l E f c k ≫ (wY.reduction k).inv
    a (n + 1) ≫ normalizedDVRReductionTransition l E Y D hl n.le_succ wY.omega.obj =
      normalizedDVRReductionTransition l E Y D hl n.le_succ
          ((sfCompactSupportFiniteIntegralFunctor l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) c E).obj wX.omega).obj ≫
        (normalizedDVRRes l E Y n.le_succ).map (a n) := by
  exact coherent_trace_family
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 2)) c)
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c)
    (normalizedDVRRes l E X n.le_succ) (normalizedDVRRes l E Y n.le_succ)
    (finiteSupportRestriction l E c n.le_succ)
    (wX.reduction (n + 1)) (wX.reduction n) (wY.reduction (n + 1)) (wY.reduction n)
    (sfCompactSupportFiniteReductionIso l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E wX.omega (n + 1))
    (sfCompactSupportFiniteReductionIso l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E wX.omega n)
    (normalizedDVRReductionTransition l E X D hl n.le_succ wX.omega.obj)
    (normalizedDVRReductionTransition l E Y D hl n.le_succ wY.omega.obj)
    (integralDualizingExceptionalTransition l E D X hl n.le_succ)
    (integralDualizingExceptionalTransition l E D Y hl n.le_succ)
    (normalizedDVRReductionTransition l E Y D hl n.le_succ
      ((sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c E).obj wX.omega).obj)
    (finiteTrace D l E f c (n + 1)) (finiteTrace D l E f c n)
    (wX.coherent n.le_succ) (wY.coherent n.le_succ)
    ((congrArg (fun v ↦
      (sfCompactSupportFiniteReductionIso l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c E wX.omega (n + 1)).hom ≫ v)
      (outputTransition_eq D l hl E f c wX.omega n)).symm.trans
        (sfCompactSupportFiniteReductionIso_coherent D l hl E c wX.omega n))
    (finiteTrace_restriction D l hl E f c n)

/-- The canonical relative trace exists and is fixed by the finite structural traces.
Source: blueprint Steps 2 and 11
(blueprint: lem-coef-dual-formula-scalar-transpose).
Proof: conjugate the prescribed finite relative traces by the dualizing reduction
isomorphisms and the canonical compact-support reduction isomorphisms. Their
successor compatibility follows from the finite relative trace restriction square,
naturality of the support restriction comparison, and coherence of the specified
support reductions. The constructible mapping-limit bijection reconstructs a
unique integral morphism from this compatible family: its shifted finite Hom
groups are finite, so the Milnor lim-one term vanishes. Cancelling the dualizing
reduction isomorphisms gives exactly TraceNormalized and its uniqueness. -/
theorem trace_existsUnique
    (wX : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wY : IntegralFiniteExtension.DualizingDatum l Y D hl E) :
    ∃! t : (sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c E).obj wX.omega ⟶ wY.omega,
      TraceNormalized D l hl E f c wX wY t := by
  let a (n : ℕ) :=
    (sfCompactSupportFiniteReductionIso l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E wX.omega n).hom ≫
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
      (wX.reduction n).hom ≫ finiteTrace D l E f c n ≫ (wY.reduction n).inv
  obtain ⟨t, ht, hu⟩ := integralConstructibleAdjacentReductionHom D l hl E Y
    ((sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E).obj wX.omega)
    wY.omega a (finiteTraceFamily_coherent D l hl E f c wX wY)
  refine ⟨ObjectProperty.homMk t, ?_, ?_⟩
  · intro n
    change (scalarReductionDerivedExtension l E Y n).map t ≫ _ = _
    rw [ht n]
    exact cancel_trace_tail _ _ _ _
  · intro t' ht'
    apply ObjectProperty.hom_ext
    apply hu
    intro n
    exact eq_trace_tail _ _ _ _ _ (ht' n)

/-- The relative trace with its unique structural-counit normalization.
Source: blueprint Step 2
(blueprint: lem-coef-dual-formula-scalar-transpose). -/
def trace
    (wX : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wY : IntegralFiniteExtension.DualizingDatum l Y D hl E) :=
  (trace_existsUnique D l hl E f c wX wY).exists.choose

/-- Evaluation characterization of the canonical integral exceptional-formula component.
Its transpose uses the actual ordinary projection map, completion augmentation, and
structural relative trace. Source: blueprint Steps 2--3
(blueprint: lem-coef-dual-formula-scalar-transpose). -/
def FormulaNormalized
    (wX : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wY : IntegralFiniteExtension.DualizingDatum l Y D hl E)
    (aX : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (aZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (completedIntegralCommRingSheafUnrestricted l E c.Z))
    (aY : IntegralHom.TensorPresentation.{u, u} Y
      (completedIntegralCommRingSheafUnrestricted l E Y))
    (sX : IntegralVerdier.SignedSymmetry X _ aX)
    (G : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X)
    (adj : sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E ⊣ G)
    (M : sfIntegralConstructibleCategory l E Y)
    (k : (G.obj M).obj ≅ formulaObject D l hl E f wX wY M) : Prop :=
  ((PurCompactSupport.projectionMap (PurCompactSupport.completed l E) c
      (IntegralFiniteExtension.tensorModel X aX)
      (IntegralFiniteExtension.tensorModel c.Z aZ)
      (IntegralFiniteExtension.tensorModel Y aY)
      (PurCompactSupport.completedPull_comp l E c.i c.g)).app (G.obj M).obj).app
        ((IntegralVerdier.dual l E Y wY.omega.obj).obj (op M.obj)) ≫
    (PurCompactSupport.image (PurCompactSupport.completed l E) c).map
      (aX.tensor.map (Prod.mkHom (𝟙 (G.obj M).obj)
        ((pullCompletion l E f).app
          ((IntegralVerdier.dual l E Y wY.omega.obj).obj (op M.obj)))) ≫
      ((normalizedSignedSymmetry X _ aX sX).swap (G.obj M).obj
        ((integralDerivedPullback.{u, u} l E f).obj
        ((IntegralVerdier.dual l E Y wY.omega.obj).obj (op M.obj)))).hom ≫
      aX.tensor.map (Prod.mkHom (𝟙 _) k.hom) ≫
      (canonicalEvaluationAdjunction X _ aX ((integralDerivedPullback.{u, u} l E f).obj
        ((IntegralVerdier.dual l E Y wY.omega.obj).obj (op M.obj)))).counit.app wX.omega.obj) ≫
    (sfQcqsCompactSupportRealization l E D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c).hom.app wX.omega ≫
    (sfIntegralConstructible l E Y).ι.map (trace D l hl E f c wX wY) =
  aY.tensor.map (Prod.mkHom
    ((sfQcqsCompactSupportRealization l E D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c).hom.app (G.obj M) ≫
      (sfIntegralConstructible l E Y).ι.map (adj.counit.app M)) (𝟙 _)) ≫
    (canonicalEvaluationAdjunction Y _ aY M.obj).counit.app wY.omega.obj

private theorem evaluationPairing_precomp
    (wY : IntegralFiniteExtension.DualizingDatum l Y D hl E)
    (aY : IntegralHom.TensorPresentation.{u, u} Y
      (completedIntegralCommRingSheafUnrestricted l E Y))
    (P P' : IntegralVerdier.Ambient l E Y) (v : P ⟶ P')
    (M : sfIntegralConstructibleCategory l E Y) (g : P' ⟶ M.obj) :
    formulaEvaluationPairing D l hl E wY aY P M (v ≫ g) =
      aY.tensor.map (Prod.mkHom v
        (𝟙 ((IntegralVerdier.dual l E Y wY.omega.obj).obj (op M.obj)))) ≫
      formulaEvaluationPairing D l hl E wY aY P' M g := by
  exact tensor_precomp aY.tensor v g _

/-- The exceptional formula has a unique component with the evaluation normalization.
Source: blueprint Step 3; prop-coef-integral-exceptional-adjoint, formula clause
(blueprint: lem-coef-dual-formula-scalar-transpose).
Proof: at every finite coefficient level, apply the tensor-Hom bijections, ordinary
pullback/direct-image adjunction, and the absolute trace exchange. The inverse Hom
bijection sends h to delta_M inverse composed with the curry of its trace transpose.
By the fixed projection and trace equations this gives exactly FormulaNormalized.
Finite Verdier biduality makes this a bijection. Perform these constructions on
simultaneous coefficient-system resolutions, with the actual quotient units and
counits, and descend the one coherent mapping-system bijection through reduction and
total limit. Constructibility and the common Tor bounds are those of the integral
exceptional-adjoint proposition. The integral adjunction bijection and Yoneda give
existence and uniqueness of the displayed normalized isomorphism. -/
theorem formula_existsUnique
    (wX : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wY : IntegralFiniteExtension.DualizingDatum l Y D hl E)
    (aX : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (aZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (completedIntegralCommRingSheafUnrestricted l E c.Z))
    (aY : IntegralHom.TensorPresentation.{u, u} Y
      (completedIntegralCommRingSheafUnrestricted l E Y))
    (sX : IntegralVerdier.SignedSymmetry X _ aX)
    (G : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X)
    (adj : sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E ⊣ G)
    (M : sfIntegralConstructibleCategory l E Y) :
    ∃! k : (G.obj M).obj ≅ formulaObject D l hl E f wX wY M,
      FormulaNormalized D l hl E f c wX wY aX aZ aY sX G adj M k := by
  let t := trace D l hl E f c wX wY
  have ht : TraceNormalized D l hl E f c wX wY t :=
    (trace_existsUnique D l hl E f c wX wY).exists.choose_spec
  obtain ⟨ha, hb, hn⟩ := formulaPairing_perfect D l hl E f c
    wX wY aX aZ aY sX t ht
  let H := dualValue D l hl E X wX (pullDualValue D l hl E f wY M)
  let eta := sfQcqsCompactSupportRealization l E D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) c
  let P (K : sfIntegralConstructibleCategory l E X) :=
    aY.tensor.obj (((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj K.obj),
      (IntegralVerdier.dual l E Y wY.omega.obj).obj (op M.obj)) ⟶ wY.omega.obj
  let A (K : sfIntegralConstructibleCategory l E X) (h : K ⟶ H) : P K :=
    formulaTracePairing D l hl E f c wX wY aX aZ aY sX t K M h.hom
  let B (K : sfIntegralConstructibleCategory l E X) (g : K ⟶ G.obj M) : P K :=
    formulaEvaluationPairing D l hl E wY aY _ M
      (eta.hom.app K ≫ ((adj.homEquiv K M).symm g).hom)
  have hA (K : sfIntegralConstructibleCategory l E X) : Function.Bijective (A K) := by
    constructor
    · intro h h' hh
      apply ObjectProperty.hom_ext
      exact (ha K M).injective hh
    · intro p
      obtain ⟨h, hh⟩ := (ha K M).surjective p
      exact ⟨ObjectProperty.homMk h, hh⟩
  have hB (K : sfIntegralConstructibleCategory l E X) : Function.Bijective (B K) := by
    constructor
    · intro g g' hh
      have h := (hb K M).injective hh
      apply (adj.homEquiv K M).symm.injective
      apply ObjectProperty.hom_ext
      exact (Iso.cancel_iso_hom_left (eta.app K) _ _).mp h
    · intro p
      obtain ⟨g, hg⟩ := (hb K M).surjective p
      refine ⟨adj.homEquiv K M (ObjectProperty.homMk (eta.inv.app K ≫ g)), ?_⟩
      dsimp only [B]
      rw [Equiv.symm_apply_apply]
      change formulaEvaluationPairing D l hl E wY aY _ M
        (eta.hom.app K ≫ eta.inv.app K ≫ g) = p
      exact (congrArg (formulaEvaluationPairing D l hl E wY aY _ M)
        ((eta.app K).hom_inv_id_assoc g)).trans hg
  let pre {K K' : sfIntegralConstructibleCategory l E X} (v : K ⟶ K') (p : P K') : P K :=
    aY.tensor.map (Prod.mkHom
      ((PurCompactSupport.image (PurCompactSupport.completed l E) c).map v.hom)
      (𝟙 ((IntegralVerdier.dual l E Y wY.omega.obj).obj (op M.obj)))) ≫ p
  have hAn {K K' : sfIntegralConstructibleCategory l E X} (v : K ⟶ K') (h : K' ⟶ H) :
      A K (v ≫ h) = pre v (A K' h) := hn K K' M v h.hom
  have hBn {K K' : sfIntegralConstructibleCategory l E X}
      (v : K ⟶ K') (g : K' ⟶ G.obj M) : B K (v ≫ g) = pre v (B K' g) := by
    exact (congrArg (formulaEvaluationPairing D l hl E wY aY _ M)
      (adjunction_comparison_natural adj (sfIntegralConstructible l E X).ι
        (sfIntegralConstructible l E Y).ι
        (PurCompactSupport.image (PurCompactSupport.completed l E) c) eta v g)).trans
      (evaluationPairing_precomp D l hl E wY aY _ _ _ M _)
  obtain ⟨k, hk, hu⟩ := iso_of_pairings H (G.obj M) P A B hA hB
    (fun v p ↦ pre v p) (fun v h ↦ hAn v h) (fun v g ↦ hBn v g)
  let ka : (G.obj M).obj ≅ formulaObject D l hl E f wX wY M :=
    (sfIntegralConstructible l E X).ι.mapIso k
  refine ⟨ka, ?_, ?_⟩
  · change A (G.obj M) k.hom = _
    rw [hk]
    dsimp only [B]
    rw [adj.homEquiv_symm_id]
    rfl
  · intro k' hk'
    have hk'n : A (G.obj M) (ObjectProperty.homMk k'.hom) = B (G.obj M) (𝟙 _) := by
      dsimp only [B]
      rw [adj.homEquiv_symm_id]
      exact hk'
    apply Iso.ext
    change k'.hom = k.hom.hom
    exact congrArg (fun h ↦ h.hom) ((hA (G.obj M)).injective (hk'n.trans hk.symm))

/-- The exceptional-formula component selected by its unique evaluation characterization.
Source: blueprint definition of kappa
(blueprint: lem-coef-dual-formula-scalar-transpose). -/
def formulaIso
    (wX : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wY : IntegralFiniteExtension.DualizingDatum l Y D hl E)
    (aX : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (aZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (completedIntegralCommRingSheafUnrestricted l E c.Z))
    (aY : IntegralHom.TensorPresentation.{u, u} Y
      (completedIntegralCommRingSheafUnrestricted l E Y))
    (sX : IntegralVerdier.SignedSymmetry X _ aX)
    (G : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X)
    (adj : sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E ⊣ G)
    (M : sfIntegralConstructibleCategory l E Y) :=
  (formula_existsUnique D l hl E f c wX wY aX aZ aY sX G adj M).exists.choose

variable (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L)

end WeilConjectures.CoefDualFormulaScalarTranspose
