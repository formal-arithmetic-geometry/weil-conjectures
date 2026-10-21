/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R7
-/
module

public import Sheaf.CategoryTheory.SystemEvaluationTopos
import all Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.CategoryTheory.SystemScalarCoherence
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-! # Simultaneous K-flat representatives for strict systems

Source: Stacks 06YS and 0G7E; Zheng, Construction 4.1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- Sequence-site flat-term K-flat complexes remain flat-term K-flat at every level.
Source: Stacks 0G7E (blueprint: lem-pur-system-evaluation-kflat).
Proof: vertical evaluation is the algebraic inverse image of a geometric morphism.
Apply K-flat pullback along its identity structural ring map. The normalized scalar
unit identifies extension along that identity with the original evaluation. Transport
K-flatness and flatness along this natural isomorphism. -/
theorem systemSequenceEvaluation_preservesKFlat (n : ℕ)
    (P : CochainComplex (systemSequenceModules B) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := systemSequenceRing B) P)
    (hf : ∀ i : ℤ, IsFlatOnSite (R := systemSequenceRing B) (P.X i)) :
    systemLevelKFlat B n
      (((systemSequenceEvaluation B n).mapHomologicalComplex (.up ℤ)).obj P) := by
  classical
  let A : SystemScalarModel (𝟙 (B.obj (op n))) := (nonempty_systemScalarModel _).some
  let F := systemSequenceEvaluation B n
  let T := F ⋙ A.model.E
  have : F.Additive := inferInstance
  have : T.Additive := inferInstance
  have ht := isKFlat_ringedToposPullback
    ((Prod.sectR n C).sheafPushforwardContinuous (Type w) J (coefficientSequenceTopology J))
    ((Prod.sectR n C).sheafPushforwardCocontinuous (Type w) J (coefficientSequenceTopology J))
    (systemSequenceEvaluationToposAdjunction (J := J) n)
    (systemSequenceEvaluationInverseImage B n) (𝟙 (B.obj (op n))) T
    (fun M ↦ A.model.obj_eq (F.obj M)) (fun f ↦ A.model.map_eq (F.map f)) P hP hf
  let e : T ≅ F := Functor.isoWhiskerLeft F (systemScalarModelUnit rfl A) ≪≫ F.rightUnitor
  let ec := (NatIso.mapHomologicalComplex e (.up ℤ)).app P
  exact ⟨kFlat_iso_independent (B.obj (op n)) ec ht.1,
    fun i ↦ flatOnSite_of_iso (B.obj (op n))
      ((HomologicalComplex.eval _ (.up ℤ) i).mapIso ec) (ht.2 i)⟩

/-- Every complex of strict systems has one strict representative which is flat-term
K-flat at every level. Source: Stacks 06YS and 0G7E; Zheng 4.1
(blueprint: lem-pur-system-evaluation-kflat).
Proof: transport the complex to the ringed sequence site and resolve it there by a
flat-term K-flat complex. Pull the resolution back through the sequence-site equivalence.
The unit identifies its augmentation target with the original strict complex. Exactness
of the equivalence preserves its quasi-isomorphism. Every slice is flat-term K-flat by
the evaluation pullback theorem, so the construction resolves all levels simultaneously. -/
theorem strictRingSystem_kFlatResolution (K : CochainComplex (StrictRingSystem B) ℤ) :
    ∃ (L : CochainComplex (StrictRingSystem B) ℤ) (f : L ⟶ K),
      systemComponentwiseKFlat B L ∧ QuasiIso f := by
  classical
  let E := strictSystemSequenceEquivalence B
  let e := E.mapHomologicalComplex (.up ℤ)
  obtain ⟨P, q, hP, hflat, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := systemSequenceRing B) (e.functor.obj K)
  have hflat' (i : ℤ) : IsFlatOnSite (R := systemSequenceRing B) (P.X i) :=
    (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso (systemSequenceRing B) (P.X i)).symm (hflat i)
  let L := e.inverse.obj P
  let f : L ⟶ K := e.inverse.map q ≫ e.unitIso.inv.app K
  have : QuasiIso q := hq
  have : QuasiIso (e.inverse.map q) := by
    change QuasiIso ((E.inverse.mapHomologicalComplex (.up ℤ)).map q)
    infer_instance
  refine ⟨L, f, ?_, ?_⟩
  · intro n
    change systemLevelKFlat B n
      (((systemSequenceEvaluation B n).mapHomologicalComplex (.up ℤ)).obj P)
    exact systemSequenceEvaluation_preservesKFlat B n P hP hflat'
  · dsimp only [f]
    infer_instance

end SheafOfModules
