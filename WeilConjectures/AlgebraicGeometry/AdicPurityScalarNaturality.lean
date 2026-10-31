/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicPurityScalarNaturalityData
import WeilConjectures.AlgebraicGeometry.AdicPurityNormalizedComparisonConstruction
import WeilConjectures.AlgebraicGeometry.AdicPurityCanonicalSourceCoherence

/-! # Simultaneously natural integral smooth purity

The actual unit trace is extended to all finite coefficient fields. Its transposes
supply the prescribed reductions and the coherent coefficient comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.AdicPurityScalarNaturality

/-- Shift-compatible transformations are closed under conjugation and whiskering. -/
private theorem conjugate_commShift
    {A B A' B' : Type (u + 2)} [Category.{u + 2} A] [Category.{u + 2} B]
    [Category.{u + 2} A'] [Category.{u + 2} B']
    [HasShift A ℤ] [HasShift B ℤ] [HasShift A' ℤ] [HasShift B' ℤ]
    {H G : A ⥤ B} {H' G' : A' ⥤ B'} (V : B ⥤ B') (U : A ⥤ A')
    [H.CommShift ℤ] [G.CommShift ℤ] [H'.CommShift ℤ] [G'.CommShift ℤ]
    [V.CommShift ℤ] [U.CommShift ℤ]
    (e : H ≅ G) (e' : H' ≅ G') (a : H ⋙ V ⟶ U ⋙ H')
    [NatTrans.CommShift e.hom ℤ] [NatTrans.CommShift e'.hom ℤ]
    [NatTrans.CommShift a ℤ] :
    NatTrans.CommShift (Functor.whiskerRight e.inv V ≫ a ≫
      Functor.whiskerLeft U e'.hom) ℤ := by
  infer_instance

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)

variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

attribute [local irreducible] source target scalar associator scalarUnit targetShift

/-- The purity square transports source tensor and shift coherence to the
exceptional comparison, by cancellation of the invertible purity components. -/
private theorem comparison_coherence
    (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
    (P : ComparisonData D C f d S)
    (hsq : ∀ (E F : Field D C) (h : E ≤ F) (K : Cat D C E Y),
      (scalar D C P.scalarClosed E F h true).map ((P.gamma E).hom.app K) ≫
          (P.b E F h).hom.app K =
        (P.a E F h).hom.app K ≫
          (P.gamma F).hom.app ((scalar D C P.scalarClosed E F h false).obj K))
    (hgamma : ∀ E : Field D C,
      ShiftCompatibility (source D C f d E) (target D C f S E)
        (sourceShift D C f d E) (targetShift D C f S E) (P.gamma E))
    (ha :
    (∀ (E : Field D C) (K : Cat D C E Y),
    (P.a E E le_rfl).hom.app K ≫
        (source D C f d E).map ((scalarUnit D C P.scalarClosed E false).hom.app K) =
      (scalarUnit D C P.scalarClosed E true).hom.app ((source D C f d E).obj K)) ∧
    (∀ (E F L : Field D C) (h : E ≤ F) (k : F ≤ L) (K : Cat D C E Y),
    (associator D C P.scalarClosed E F L h k true).hom.app ((source D C f d E).obj K) ≫
        (P.a E L (h.trans k)).hom.app K =
      (scalar D C P.scalarClosed F L k true).map ((P.a E F h).hom.app K) ≫
        (P.a F L k).hom.app ((scalar D C P.scalarClosed E F h false).obj K) ≫
        (source D C f d L).map ((associator D C P.scalarClosed E F L h k false).hom.app K)) ∧
    (∀ (E F : Field D C) (h : E ≤ F),
    ShiftCompatibility
      (source D C f d E ⋙ scalar D C P.scalarClosed E F h true)
      (scalar D C P.scalarClosed E F h false ⋙ source D C f d F)
      (composeShift (source D C f d E) (scalar D C P.scalarClosed E F h true)
        (sourceShift D C f d E) (scalarShift D C P.scalarClosed E F h true))
      (composeShift (scalar D C P.scalarClosed E F h false) (source D C f d F)
        (scalarShift D C P.scalarClosed E F h false) (sourceShift D C f d F)) (P.a E F h))) :
    Coherence D C f d S P.scalarClosed P.gamma P.a P.b := by
  obtain ⟨haUnit, haComp, haShift⟩ := ha
  unfold Coherence
  refine ⟨hsq, haUnit, ?_, haComp, ?_, haShift, ?_, hgamma⟩
  · intro E K
    apply (Iso.cancel_iso_hom_left
      ((scalar D C P.scalarClosed E E le_rfl true).mapIso ((P.gamma E).app K)) _ _).mp
    dsimp only [Functor.mapIso, Iso.app]
    calc
      _ = (P.a E E le_rfl).hom.app K ≫
          (P.gamma E).hom.app ((scalar D C P.scalarClosed E E le_rfl false).obj K) ≫
          (target D C f S E).map ((scalarUnit D C P.scalarClosed E false).hom.app K) := by
            rw [← Category.assoc, hsq, Category.assoc]
      _ = (P.a E E le_rfl).hom.app K ≫
          (source D C f d E).map ((scalarUnit D C P.scalarClosed E false).hom.app K) ≫
          (P.gamma E).hom.app K := by
            simpa only [Functor.id_obj] using
              congrArg (fun v ↦ (P.a E E le_rfl).hom.app K ≫ v)
                ((P.gamma E).hom.naturality
                  ((scalarUnit D C P.scalarClosed E false).hom.app K)).symm
      _ = (scalarUnit D C P.scalarClosed E true).hom.app
          ((source D C f d E).obj K) ≫ (P.gamma E).hom.app K := by
            rw [← Category.assoc, haUnit]
      _ = _ := by
        exact ((scalarUnit D C P.scalarClosed E true).hom.naturality
          ((P.gamma E).hom.app K)).symm
  · intro E F L h k K
    let CX := scalar D C P.scalarClosed E F h true
    let DX := scalar D C P.scalarClosed F L k true
    let EX := scalar D C P.scalarClosed E L (h.trans k) true
    let CY := scalar D C P.scalarClosed E F h false
    let DY := scalar D C P.scalarClosed F L k false
    let AY := associator D C P.scalarClosed E F L h k false
    let AX := associator D C P.scalarClosed E F L h k true
    apply (Iso.cancel_iso_hom_left (DX.mapIso (CX.mapIso ((P.gamma E).app K))) _ _).mp
    dsimp only [Functor.mapIso, Iso.app]
    calc
      _ = AX.hom.app ((source D C f d E).obj K) ≫
          EX.map ((P.gamma E).hom.app K) ≫ (P.b E L (h.trans k)).hom.app K := by
            rw [← Category.assoc]
            simpa only [Functor.comp_map, Category.assoc] using
              congrArg (fun v ↦ v ≫ (P.b E L (h.trans k)).hom.app K)
                (AX.hom.naturality ((P.gamma E).hom.app K))
      _ = AX.hom.app ((source D C f d E).obj K) ≫
          (P.a E L (h.trans k)).hom.app K ≫ (P.gamma L).hom.app
            ((scalar D C P.scalarClosed E L (h.trans k) false).obj K) := by
            rw [hsq]
      _ = DX.map ((P.a E F h).hom.app K) ≫ (P.a F L k).hom.app (CY.obj K) ≫
          (source D C f d L).map (AY.hom.app K) ≫ (P.gamma L).hom.app
            ((scalar D C P.scalarClosed E L (h.trans k) false).obj K) := by
            simpa only [Category.assoc] using
              congrArg (fun v ↦ v ≫ (P.gamma L).hom.app
                ((scalar D C P.scalarClosed E L (h.trans k) false).obj K))
                (haComp E F L h k K)
      _ = DX.map ((P.a E F h).hom.app K) ≫ (P.a F L k).hom.app (CY.obj K) ≫
          (P.gamma L).hom.app (DY.obj (CY.obj K)) ≫
          (target D C f S L).map (AY.hom.app K) := by
            rw [(P.gamma L).hom.naturality]
      _ = DX.map ((P.a E F h).hom.app K) ≫
          DX.map ((P.gamma F).hom.app (CY.obj K)) ≫ (P.b F L k).hom.app (CY.obj K) ≫
          (target D C f S L).map (AY.hom.app K) := by
            simpa only [Category.assoc] using
              congrArg (fun v ↦ DX.map ((P.a E F h).hom.app K) ≫ v ≫
                (target D C f S L).map (AY.hom.app K)) (hsq F L k (CY.obj K)).symm
      _ = DX.map (CX.map ((P.gamma E).hom.app K)) ≫
          DX.map ((P.b E F h).hom.app K) ≫ (P.b F L k).hom.app (CY.obj K) ≫
          (target D C f S L).map (AY.hom.app K) := by
            have hm := congrArg (fun v ↦ DX.map v) (hsq E F h K)
            simp only [Functor.map_comp] at hm
            simpa only [Category.assoc] using
              congrArg (fun v ↦ v ≫ (P.b F L k).hom.app (CY.obj K) ≫
                (target D C f S L).map (AY.hom.app K)) hm.symm
  · intro E F h
    let sE : (source D C f d E).CommShift ℤ := sourceShift D C f d E
    let sF : (source D C f d F).CommShift ℤ := sourceShift D C f d F
    let tE : (target D C f S E).CommShift ℤ := targetShift D C f S E
    let tF : (target D C f S F).CommShift ℤ := targetShift D C f S F
    let cX : (scalar D C P.scalarClosed E F h true).CommShift ℤ :=
      scalarShift D C P.scalarClosed E F h true
    let cY : (scalar D C P.scalarClosed E F h false).CommShift ℤ :=
      scalarShift D C P.scalarClosed E F h false
    have hgE := hgamma E
    have hgF := hgamma F
    have haEF := haShift E F h
    dsimp only [ShiftCompatibility, composeShift] at hgE hgF haEF ⊢
    have hb : (P.b E F h).hom =
        Functor.whiskerRight (P.gamma E).inv
            (scalar D C P.scalarClosed E F h true) ≫
          (P.a E F h).hom ≫
          Functor.whiskerLeft (scalar D C P.scalarClosed E F h false) (P.gamma F).hom := by
      apply NatTrans.ext
      funext K
      apply (Iso.cancel_iso_hom_left
        ((scalar D C P.scalarClosed E F h true).mapIso ((P.gamma E).app K)) _ _).mp
      dsimp only [Functor.mapIso, Iso.app, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.whiskerLeft_app]
      rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp,
        Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
      exact hsq E F h K
    rw [hb]
    exact @conjugate_commShift
      (Cat D C E Y) (Cat D C E X) (Cat D C F Y) (Cat D C F X)
      _ _ _ _ _ _ _ _
      (source D C f d E) (target D C f S E)
      (source D C f d F) (target D C f S F)
      (scalar D C P.scalarClosed E F h true) (scalar D C P.scalarClosed E F h false)
      sE tE sF tF cX cY (P.gamma E) (P.gamma F) (P.a E F h).hom hgE hgF haEF


/-- Simultaneously natural integral purity with the ordinary completed-ring tensor
comparisons, counit transpose, tensor units, associators and shifts of the node.
Source: blueprint sec-smooth-purity/sk-thm-purity-transport, Steps 2--3
(blueprint: lem-pur-adic-purity-scalar-naturality).

Proof:
1. Restrict pullback, twists, compact support and the exceptional adjunction to the
uniform finite-Tor categories, using lem-pur-adic-operation-domains-source-comparison.
Its ordinary tensor comparisons give a and c, with the displayed normalizations.
2. Choose one base-field purity orientation. Form its trace and extend that trace
simultaneously to all finite subfields. Transpose the projection composites as in
lem-pur-adic-unit-trace-transpose-reductions. These give natural linear isomorphisms
with all the prescribed finite reductions. No uniqueness of arbitrary lifts is used.
3. Apply lem-pur-adic-scalar-trace-coherence to the scalar extensions of this single
trace. The ordinary tensor unit and canonical compact-support mate are the ones in c.
4. Apply lem-pur-adic-trace-transpose-coefficient-calculus. The counit transpose is
exactly bMate; the scalar trace equation gives puritySquare. Tensor unit and
associativity give the two unit and composition equations. The projection and
transpose shift equations of lem-pur-adic-projection-shift-coherence give aShift,
bShift and gammaShift. Invertibility follows from the constructed gamma and a;
the same construction supplies exactness and coefficient linearity. -/
theorem adicPurityScalarNaturality :
    ∃ S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f),
      Nonempty (Data D C f d S) := by
  obtain ⟨S, P, hsq, hgamma⟩ := normalizedComparisonConstruction D C f d
  have ha := canonicalSourceCoherence D C f d P.scalarClosed P.a P.aCanonical
  exact ⟨S, ⟨{
    toComparisonData := P
    coherence := comparison_coherence D C f d S P hsq hgamma ha }⟩⟩

end WeilConjectures.AdicPurityScalarNaturality
