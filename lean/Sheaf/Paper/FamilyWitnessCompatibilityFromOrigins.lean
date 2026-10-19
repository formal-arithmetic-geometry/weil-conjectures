/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P6
-/
module

public import Sheaf.Paper.WitnessCompatibility
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit

/-! # Functorial witnessed towers from quotient comparisons and etale origins

Source: blueprint amplification step (b); Stacks Tags 09C7 and 07A4
(blueprint: lem-weil-pbc-family-witness-compatibility-from-origins).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale


private def comparisonPlusFF (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] :
    ((comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategoryPlus ⋙
      DerivedCategory.Plus.ι).FullyFaithful := by
  letI := isIso_compactSupportComparisonUnit T Λ
  exact (derivedComparisonAdjunctionPlus (ModuleCat.{u + 1} Λ) T).fullyFaithfulLOfIsIsoUnit.comp
    (Functor.FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι)

private theorem comparisonReflectsPlus (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ]
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : DerivedCategory.TStructure.t.plus
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory.obj K)) :
    DerivedCategory.TStructure.t.plus K := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, (DerivedCategory.isGE_iff K a).2 ?_⟩
  have := isIso_comparisonAdjunction_unit (ModuleCat.{u + 1} Λ) T
  have := (comparisonAdjunction (ModuleCat.{u + 1} Λ) T).fullyFaithfulLOfIsIsoUnit.faithful
  intro i hi
  exact Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) T)
      ((DerivedCategory.isGE_iff _ a).1 ha i hi)

private def liftOriginIso (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ]
    (L M : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hM : DerivedCategory.TStructure.t.plus M)
    (e : (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory.obj L ≅
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory.obj M) : L ≅ M := by
  let hL := comparisonReflectsPlus T Λ L
    (DerivedCategory.TStructure.t.plus.prop_of_iso e.symm
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategoryPlus.obj ⟨M, hM⟩).property)
  exact DerivedCategory.Plus.ι.mapIso ((comparisonPlusFF T Λ).preimageIso
    (X := ⟨L, hL⟩) (Y := ⟨M, hM⟩) e)

private theorem liftOriginIso_map (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ]
    (L M : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hM : DerivedCategory.TStructure.t.plus M)
    (e : (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory.obj L ≅
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory.obj M) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory.map
      (liftOriginIso T Λ L M hM e).hom = e.hom := by
  exact (comparisonPlusFF T Λ).map_preimage _

private theorem comparisonMapInjective (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ]
    {L M : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.TStructure.t.plus L) (hM : DerivedCategory.TStructure.t.plus M)
    {a b : L ⟶ M}
    (h : (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory.map a =
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory.map b) : a = b := by
  exact congrArg (fun f ↦ f.hom) ((comparisonPlusFF T Λ).map_injective
    (f := ObjectProperty.homMk (X := ⟨L, hL⟩) (Y := ⟨M, hM⟩) a)
    (g := ObjectProperty.homMk b) h)

variable {A : Type (u + 1)} [CommRing A]

private def witnessMap (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A)
    (P Q : PbcWitnessedTower T d) (u : ∀ n, P.K n ⟶ Q.K n) (n : ℕ) :
    (P.origin n).L.obj ⟶ (Q.origin n).L.obj :=
  DerivedCategory.Plus.ι.map ((comparisonPlusFF T (PbcQuotient d n)).preimage
    (X := (P.origin n).L) (Y := (Q.origin n).L)
    ((P.alpha n).hom ≫ u n ≫ (Q.alpha n).inv))

private theorem witnessMap_comm (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A)
    (P Q : PbcWitnessedTower T d) (u : ∀ n, P.K n ⟶ Q.K n) (n : ℕ) :
    (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.map
      (witnessMap T d P Q u n) = (P.alpha n).hom ≫ u n ≫ (Q.alpha n).inv :=
  (comparisonPlusFF T (PbcQuotient d n)).map_preimage _

private theorem witnessMap_beta (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A)
    (P Q : PbcWitnessedTower T d) (u : ∀ n, P.K n ⟶ Q.K n)
    (hu : ∀ n, (pbcWitnessReduction T d n).map (u (n + 1)) ≫ (Q.theta n).hom =
      (P.theta n).hom ≫ u n) (n : ℕ) :
    (pbcWitnessEtaleReduction T d n).map (witnessMap T d P Q u (n + 1)) ≫
      (Q.beta n).hom = (P.beta n).hom ≫ witnessMap T d P Q u n := by
  apply comparisonMapInjective T (PbcQuotient d n)
    (DerivedCategory.TStructure.t.plus.prop_of_iso (P.beta n).symm (P.origin n).L.property)
    (Q.origin n).L.property
  apply (cancel_mono (Q.alpha n).hom).1
  simp only [Functor.map_comp, Category.assoc, PbcWitnessedTower.alpha]
  rw [Q.compatibility n]
  have hn := (pbcComparisonReduction T
    (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).inv.naturality
      (witnessMap T d P Q u (n + 1))
  change
    (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.map
        ((pbcWitnessEtaleReduction T d n).map (witnessMap T d P Q u (n + 1))) ≫
        (pbcComparisonReduction T
          (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).inv.app
            (Q.origin (n + 1)).L.obj =
      (pbcComparisonReduction T
          (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).inv.app
            (P.origin (n + 1)).L.obj ≫
        (pbcWitnessReduction T d n).map
          (CategoryTheory.Functor.map
            (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d (n + 1))) T).mapDerivedCategory
            (witnessMap T d P Q u (n + 1))) at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [witnessMap_comm]
  simp only [Functor.map_comp, Category.assoc, PbcWitnessedTower.alpha,
    Iso.map_inv_hom_id_assoc]
  rw [hu n, witnessMap_comm]
  simp only [Category.assoc, PbcWitnessedTower.alpha, Iso.inv_hom_id, Category.comp_id]
  simpa only [Category.assoc] using congrArg (fun v ↦ v ≫ u n) (P.compatibility n).symm

private def witnessHom (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A)
    (P Q : PbcWitnessedTower T d) (u : ∀ n, P.K n ⟶ Q.K n)
    (hu : ∀ n, (pbcWitnessReduction T d n).map (u (n + 1)) ≫ (Q.theta n).hom =
      (P.theta n).hom ≫ u n) : P ⟶ Q where
  u := u
  v := witnessMap T d P Q u
  theta_naturality := hu
  beta_naturality := witnessMap_beta T d P Q u hu
  origin_naturality := by
    intro n
    rw [witnessMap_comm]
    simp

private theorem witnessHom_ext (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A)
    {P Q : PbcWitnessedTower T d} (a b : P ⟶ Q) (hu : a.u = b.u) : a = b := by
  apply PbcWitnessedTowerHom.ext hu
  funext n
  apply comparisonMapInjective T (PbcQuotient d n)
    (P.origin n).L.property (Q.origin n).L.property
  apply (cancel_mono (Q.alpha n).hom).1
  rw [← a.origin_naturality, ← b.origin_naturality, hu]

private def outputTower {T S : Scheme.{u}} (d : Scheme.AdicCoefficientDatum A)
    (F : ∀ n : ℕ, PbcWitnessAmbient T d n ⥤ PbcWitnessAmbient S d n)
    (rho : ∀ n : ℕ,
      (pbcWitnessReductionDomain T d n).ι ⋙ F (n + 1) ⋙ pbcWitnessReduction S d n ≅
        (pbcWitnessReductionDomain T d n).ι ⋙ pbcWitnessReduction T d n ⋙ F n)
    (hB : ∀ (P : PbcWitnessedInputTowers T d) (n : ℕ), DerivedCategory.TStructure.t.plus
      ((finiteCoefficientRealization S (PbcQuotient d n)).mapDerivedCategory.obj
        ((F n).obj (P.obj.K n))))
    (W : ∀ (P : PbcWitnessedInputTowers T d) (n : ℕ), EtaleOriginWitness S (PbcQuotient d n)
      ⟨(finiteCoefficientRealization S (PbcQuotient d n)).mapDerivedCategory.obj
        ((F n).obj (P.obj.K n)), hB P n⟩)
    (P : PbcWitnessedInputTowers T d) : PbcWitnessedTower S d := by
  let alpha := fun n ↦ pbcFixedOriginAlpha S (PbcQuotient d n)
    ((F n).obj (P.obj.K n)) (hB P n) (W P n)
  let theta := fun n ↦
    (rho n).app ⟨P.obj.K (n + 1), pbcWitnessedInput_memReductionDomain T d P n⟩ ≪≫
      (F n).mapIso (P.obj.theta n)
  let e := fun n ↦
    (pbcComparisonReduction S
      (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).symm.app (W P (n + 1)).L.obj ≪≫
      (pbcWitnessReduction S d n).mapIso (alpha (n + 1)) ≪≫ theta n ≪≫ (alpha n).symm
  refine
    { K := fun n ↦ (F n).obj (P.obj.K n)
      boundedBelow := hB P
      origin := W P
      theta := theta
      beta := fun n ↦ liftOriginIso S (PbcQuotient d n) _ _ (W P n).L.property (e n)
      compatibility := ?_ }
  intro n
  rw [liftOriginIso_map]
  simp [e, alpha, Category.assoc]

private theorem familyOfWitnesses {T S : Scheme.{u}} (d : Scheme.AdicCoefficientDatum A)
    (F : ∀ n : ℕ, PbcWitnessAmbient T d n ⥤ PbcWitnessAmbient S d n)
    (rho : ∀ n : ℕ,
      (pbcWitnessReductionDomain T d n).ι ⋙ F (n + 1) ⋙ pbcWitnessReduction S d n ≅
        (pbcWitnessReductionDomain T d n).ι ⋙ pbcWitnessReduction T d n ⋙ F n)
    (hB : ∀ (P : PbcWitnessedInputTowers T d) (n : ℕ), DerivedCategory.TStructure.t.plus
      ((finiteCoefficientRealization S (PbcQuotient d n)).mapDerivedCategory.obj
        ((F n).obj (P.obj.K n))))
    (W : ∀ (P : PbcWitnessedInputTowers T d) (n : ℕ), EtaleOriginWitness S (PbcQuotient d n)
      ⟨(finiteCoefficientRealization S (PbcQuotient d n)).mapDerivedCategory.obj
        ((F n).obj (P.obj.K n)), hB P n⟩) :
    PbcFamilyWitnessCompatibility T S d F := by
  let O := outputTower d F rho hB W
  have htheta (P Q : PbcWitnessedInputTowers T d) (a : P ⟶ Q) (n : ℕ) :
      (pbcWitnessReduction S d n).map ((F (n + 1)).map (a.hom.u (n + 1))) ≫
        ((O Q).theta n).hom = ((O P).theta n).hom ≫ (F n).map (a.hom.u n) := by
    have hn := (rho n).hom.naturality
      (ObjectProperty.homMk
        (X := ⟨P.obj.K (n + 1), pbcWitnessedInput_memReductionDomain T d P n⟩)
        (Y := ⟨Q.obj.K (n + 1), pbcWitnessedInput_memReductionDomain T d Q n⟩)
        (a.hom.u (n + 1)))
    change
      (pbcWitnessReduction S d n).map ((F (n + 1)).map (a.hom.u (n + 1))) ≫
          (rho n).hom.app
            ⟨Q.obj.K (n + 1), pbcWitnessedInput_memReductionDomain T d Q n⟩ =
        (rho n).hom.app
            ⟨P.obj.K (n + 1), pbcWitnessedInput_memReductionDomain T d P n⟩ ≫
          (F n).map ((pbcWitnessReduction T d n).map (a.hom.u (n + 1))) at hn
    change _ ≫ (_ ≫ (F n).map (Q.obj.theta n).hom) =
      (_ ≫ (F n).map (P.obj.theta n).hom) ≫ _
    simp only [Iso.app_hom]
    rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
      a.hom.theta_naturality n, Functor.map_comp, Category.assoc]
  let lift : PbcWitnessedInputTowers T d ⥤ PbcWitnessedTower S d :=
    { obj := O
      map := fun a ↦ witnessHom S d _ _ (fun n ↦ (F n).map (a.hom.u n)) (htheta _ _ a)
      map_id := by
        intro P
        apply witnessHom_ext S d
        funext n
        change (F n).map (𝟙 _) = 𝟙 _
        exact (F n).map_id _
      map_comp := by
        intro P Q V a b
        apply witnessHom_ext S d
        funext n
        change (F n).map (a.hom.u n ≫ b.hom.u n) = _
        exact (F n).map_comp _ _ }
  refine ⟨rho, lift, fun _ _ ↦ rfl, ?_, ?_⟩
  · intro P Q a n
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · intro P n
    simp only [eqToHom_refl, Category.comp_id]
    rw [(pbcWitnessReduction S d n).map_id, Category.id_comp]
    rfl

/-- A natural family of quotient comparisons and actual bounded-below etale origins
extends to a functor on witnessed input towers with precisely the prescribed levels.
Source: blueprint amplification step (b); Stacks Tags 09C7 and 07A4
(blueprint: lem-weil-pbc-family-witness-compatibility-from-origins).

Proof: construct each output theta from rho and the input theta. Conjugate this
isomorphism by the two origin comparisons and the scalar/comparison isomorphism.
Exact faithful comparison reflects a lower bound of its source; bounded-below full
faithfulness lifts the conjugate uniquely to beta. For a levelwise output map lift
alpha_P followed by that map followed by alpha_Q inverse to the etale origins.
Naturality of rho gives its theta square. Applying faithful comparison and the
origin compatibility equations gives the beta square. The same faithfulness shows
maps are determined by their level components, so identities and composites follow
from the finite-level functors. The required level and theta equations are the
construction itself. The comparison preimages are unique, so no arbitrary witness
of an unproved existence statement is used. -/
theorem pbcFamilyWitnessCompatibility_of_origins
    {T S : Scheme.{u}} (d : Scheme.AdicCoefficientDatum A)
    (F : ∀ n : ℕ, PbcWitnessAmbient T d n ⥤ PbcWitnessAmbient S d n)
    (rho : ∀ n : ℕ,
      (pbcWitnessReductionDomain T d n).ι ⋙ F (n + 1) ⋙ pbcWitnessReduction S d n ≅
        (pbcWitnessReductionDomain T d n).ι ⋙ pbcWitnessReduction T d n ⋙ F n)
    (L : ∀ (_P : PbcWitnessedInputTowers T d) (n : ℕ),
      DerivedCategory.Plus (Sheaf S.smallEtaleTopology
        (ModuleCat.{u + 1} (PbcQuotient d n))))
    (e : ∀ (_P : PbcWitnessedInputTowers T d) (n : ℕ),
      (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) S).mapDerivedCategory.obj
        (L _P n).obj ≅ (F n).obj (_P.obj.K n)) :
    PbcFamilyWitnessCompatibility T S d F := by
  let er := fun P n ↦
    (Functor.mapDerivedCategoryCompIso
      (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) S)
      (finiteCoefficientRealization S (PbcQuotient d n))).app (L P n).obj ≪≫
        (finiteCoefficientRealization S (PbcQuotient d n)).mapDerivedCategory.mapIso (e P n)
  let hB := fun P n ↦ DerivedCategory.TStructure.t.plus.prop_of_iso (er P n)
    ((finiteCoefficientComparison S (PbcQuotient d n)).mapDerivedCategoryPlus.obj
      (L P n)).property
  exact familyOfWitnesses d F rho hB (fun P n ↦
    { L := L P n
      alpha := DerivedCategory.TStructure.t.plus.isoMk (er P n) })


end AlgebraicGeometry.ProEtale
