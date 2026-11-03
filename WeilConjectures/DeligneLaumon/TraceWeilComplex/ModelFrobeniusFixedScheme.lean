/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.TraceWeilComplex.TraceWeilComplex
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkPropSfRfShriekPreservation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkThmSfCompCompositionWitnesses
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.SmoothPurity.TraceFixedScheme
public import WeilConjectures.AlgebraicGeometry.FixedScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.TraceFormula.FiniteFieldDatum.FrobeniusAffineEqualizer.FrobeniusAffineEqualizerPresentation
import WeilConjectures.SixFunctors.FiniteFieldDatum.FiniteFieldRelationsEvaluation
import WeilConjectures.AlgebraicGeometry.AbsoluteFrobeniusNatural
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Algebra.Algebra.Pi
import WeilConjectures.AlgebraicGeometry.EqualizerPointChartDescent

/-!
# The fixed scheme of model Frobenius

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-tf-curve-local/sk-lem-tf-fixed-points/_section.md and sk-lem-tf-fixed-points.proof.md
(blueprint: sk-lem-tf-fixed-points).

The fixed scheme is the recorded graph-diagonal pullback. The displayed isomorphism is
in the category over `Spec k`, so it includes compatibility with the structure maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.TraceWeilComplex

open scoped TensorProduct
open FiniteFieldDatum.FrobeniusAffineEqualizer
attribute [local instance] Algebra.TensorProduct.rightAlgebra

-- The following proved local constructions reuse the geometric portions of
-- FrobeniusEvaluationAtlas and FrobeniusFixedPoints, without their coefficient APIs.
/-- Affine evaluation data, before any descent or tangent-space assertion.
The labels are the prescribed extension points, and the evaluation maps are normalized
as morphisms into the geometric fibre, rather than just abstract ring isomorphisms.
Source: latest blueprint, Frobenius fixed points, Steps 0–2
(blueprint: lem-trf-frobenius-evaluation-atlas). -/
private structure FrobeniusEvaluationAtlasData (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (m : ℕ) (hm : 1 ≤ m) (h : D.geometricFiber X₀ ⟶ D.geometricFiber X₀)
    (x : D.extensionPoints X₀ m hm → (Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)) where
  n : ℕ
  B : Fin n → CommAlgCat.{u} D.k
  c : ∀ j, Spec (.of (B j)) ⟶ (D.geometricFiber X₀).left
  openImmersion : ∀ j, IsOpenImmersion (c j)
  covers : ∀ z : (D.geometricFiber X₀).left, ∃ j, z ∈ Set.range (c j)
  overBase : ∀ j, c j ≫ (D.geometricFiber X₀).hom =
    Spec.map (CommRingCat.ofHom (algebraMap D.k (B j)))
  φ : ∀ j, B j →ₐ[D.k] B j
  commutes : ∀ j, Spec.map (CommRingCat.ofHom (φ j).toRingHom) ≫ c j = c j ≫ h.left
  I : ∀ j, Ideal (B j)
  differenceIdeal : ∀ j, I j = Ideal.span (Set.range (fun b : B j ↦ φ j b - b))
  Pj : Fin n → Set (D.extensionPoints X₀ m hm)
  labels : ∀ j y, y ∈ Pj j ↔ ∃ a : Spec (.of D.k) ⟶ Spec (.of (B j)), a ≫ c j = x y
  finiteLabels : ∀ j, Finite (Pj j)
  ε : ∀ j, (B j ⧸ I j) ≃ₐ[D.k] (Pj j → D.k)
  evaluation : ∀ j (y : Pj j),
    Spec.map (CommRingCat.ofHom
      ((Pi.evalRingHom (fun _ : Pj j ↦ D.k) y).comp
        ((ε j).toRingHom.comp (Ideal.Quotient.mk (I j))))) ≫ c j = x y.val

/-- Local evaluation and its precise geometric labels on one model affine.
This is only the point-label comparison after the polynomial quotient presentation;
it asserts neither an affine cover nor a global fixed-scheme decomposition.

Source: latest blueprint, `thm-trf-frobenius-fixed-points.proof.md`, Steps 1–2;
`lem-trf-finite-field-relations-evaluation`
(blueprint: lem-trf-frobenius-evaluation-atlas).

Proof:
1. Compose the given k-algebra isomorphism ν with finite-field relations evaluation.
   This gives a function algebra
   on a finite set of solution tuples, with its prescribed pure-tensor evaluation.
2. The evaluation lemma identifies the solution tuples with k₀-algebra maps
   k₀[t]/a → E. Precompose with p.symm to identify them with k₀-algebra maps A → E.
   The affine spectrum equivalence makes these E-points of the model chart.
   Composition with j gives global E-points injectively, since j is an open immersion.
3. A global E-point is in that image precisely when its scalar extension factors
   through chartMap. Base change proves one implication. Conversely its unique point
   maps into the model chart by the model projection equality, and the open-immersion
   lifting criterion provides its unique E-point lift. Define Pj as this image.
4. Reindex the function algebra by the resulting bijection. Equality of the two
   pullback projections identifies each evaluation summand with x_y: the model
   projection follows from the pure-tensor evaluation formula, the scalar projection
   from k-linearity. These arguments include empty solution sets and r=0. -/
private theorem frobenius_chart_evaluation (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (m : ℕ) (hm : 1 ≤ m)
    (A : CommAlgCat.{u} D.k₀)
    (j : FiniteFieldDatum.FrobeniusAffineEqualizer.model D A ⟶ X₀)
    [IsOpenImmersion j.left]
    (r : ℕ) (a : Ideal (MvPolynomial (Fin r) D.k₀))
    (p : (MvPolynomial (Fin r) D.k₀ ⧸ a) ≃ₐ[D.k₀] A)
    (ν : ((A ⊗[D.k₀] D.k) ⧸
        FiniteFieldDatum.FrobeniusAffineEqualizer.differenceIdeal D A m) ≃ₐ[D.k]
      (MvPolynomial (Fin r) D.k ⧸
        (FiniteFieldDatum.FrobeniusAffineEqualizer.extendedIdeal D r a ⊔
          FiniteFieldDatum.FrobeniusAffineEqualizer.powerIdeal D m r)))
    (hν : ∀ f : MvPolynomial (Fin r) D.k₀, ∀ c : D.k,
      ν (Ideal.Quotient.mk
        (FiniteFieldDatum.FrobeniusAffineEqualizer.differenceIdeal D A m)
          (p (Ideal.Quotient.mk a f) ⊗ₜ c)) =
      Ideal.Quotient.mk
        (FiniteFieldDatum.FrobeniusAffineEqualizer.extendedIdeal D r a ⊔
          FiniteFieldDatum.FrobeniusAffineEqualizer.powerIdeal D m r)
        (MvPolynomial.map (algebraMap D.k₀ D.k) f * MvPolynomial.C c))
    (x : D.extensionPoints X₀ m hm → (Spec (.of D.k) ⟶ (D.geometricFiber X₀).left))
    (hxs : ∀ y, x y ≫ (D.geometricFiber X₀).hom = 𝟙 _)
    (hxp : ∀ y, x y ≫ pullback.fst X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype) ≫ y.left) :
    ∃ Pj : Set (D.extensionPoints X₀ m hm),
      (∀ y, y ∈ Pj ↔ ∃ b : Spec (.of D.k) ⟶ Spec (.of (A ⊗[D.k₀] D.k)),
        b ≫ FiniteFieldDatum.FrobeniusAffineEqualizer.chartMap D X₀ A j = x y) ∧
      Finite Pj ∧
      ∃ ε : ((A ⊗[D.k₀] D.k) ⧸
          FiniteFieldDatum.FrobeniusAffineEqualizer.differenceIdeal D A m) ≃ₐ[D.k] (Pj → D.k),
        ∀ y : Pj, Spec.map (CommRingCat.ofHom
          ((Pi.evalRingHom (fun _ : Pj ↦ D.k) y).comp
            (ε.toRingHom.comp (Ideal.Quotient.mk
              (FiniteFieldDatum.FrobeniusAffineEqualizer.differenceIdeal D A m))))) ≫
          FiniteFieldDatum.FrobeniusAffineEqualizer.chartMap D X₀ A j = x y.val := by
  classical
  let : Algebra D.k₀ (D.extensionSubfield m hm) := (D.extensionEmbedding m hm).toAlgebra
  obtain ⟨_, e₂, points, _, _, _, _, hfinite, _, hnormal⟩ :=
    D.finite_field_relations_evaluation m hm r a
  let νk := ν
  let ε₀ : ((A ⊗[D.k₀] D.k) ⧸ differenceIdeal D A m) ≃ₐ[D.k]
      (D.relationSolutions m hm r a → D.k) := νk.trans e₂
  let ap (z : D.relationSolutions m hm r a) := (points z).comp p.symm.toAlgHom
  let yp (z : D.relationSolutions m hm r a) : D.extensionPoints X₀ m hm :=
    (affinePointEquiv D.k₀ A (D.extensionSubfield m hm) (ap z)) ≫ j
  have hyp : Function.Injective yp := by
    intro z w he
    have ht : affinePointEquiv D.k₀ A (D.extensionSubfield m hm) (ap z) =
        affinePointEquiv D.k₀ A (D.extensionSubfield m hm) (ap w) :=
      by
        apply Over.OverMorphism.ext
        apply (cancel_mono j.left).mp
        exact congrArg Over.Hom.left he
    have hpw : ap z = ap w := (affinePointEquiv D.k₀ A (D.extensionSubfield m hm)).injective ht
    apply points.injective
    apply AlgHom.ext
    intro b
    have hb := congrArg (fun f : A →ₐ[D.k₀] D.extensionSubfield m hm ↦ f (p b)) hpw
    change (points z) (p.symm (p b)) = (points w) (p.symm (p b)) at hb
    simpa only [AlgEquiv.symm_apply_apply] using hb
  have hε (z : D.relationSolutions m hm r a) (f : MvPolynomial (Fin r) D.k₀) (c : D.k) :
      ε₀ (Ideal.Quotient.mk (differenceIdeal D A m) (p (Ideal.Quotient.mk a f) ⊗ₜ c)) z =
        c * (D.extensionSubfield m hm).subtype (points z (Ideal.Quotient.mk a f)) := by
    change e₂ (ν (Ideal.Quotient.mk _ (p (Ideal.Quotient.mk a f) ⊗ₜ c))) z = _
    rw [hν]
    rw [mul_comm]
    exact hnormal z c f
  let Pj : Set (D.extensionPoints X₀ m hm) := Set.range yp
  let ι : D.relationSolutions m hm r a ≃ Pj := Equiv.ofInjective yp hyp
  let ε : ((A ⊗[D.k₀] D.k) ⧸ differenceIdeal D A m) ≃ₐ[D.k] (Pj → D.k) :=
    ε₀.trans (AlgEquiv.piCongrLeft' D.k (fun _ : D.relationSolutions m hm r a ↦ D.k) ι)
  let : Finite (D.relationSolutions m hm r a) := hfinite.to_subtype
  have hPj : Finite Pj := Finite.of_equiv _ ι
  let ev (z : D.relationSolutions m hm r a) : (A ⊗[D.k₀] D.k) →+* D.k :=
    (Pi.evalRingHom (fun _ : D.relationSolutions m hm r a ↦ D.k) z).comp
      (ε₀.toRingHom.comp (Ideal.Quotient.mk (differenceIdeal D A m)))
  have heval (z : D.relationSolutions m hm r a) :
      Spec.map (CommRingCat.ofHom
        ((Pi.evalRingHom (fun _ : D.relationSolutions m hm r a ↦ D.k) z).comp
          (ε₀.toRingHom.comp (Ideal.Quotient.mk (differenceIdeal D A m))))) ≫
        chartMap D X₀ A j = x (yp z) := by
    apply pullback.hom_ext
    · have hc : chartMap D X₀ A j ≫ pullback.fst X₀.hom
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom : A →+* (A ⊗[D.k₀] D.k))) ≫ j.left := by
        dsimp only [chartMap]
        simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst]
        rw [← Category.assoc]
        change ((pullbackSpecIso D.k₀ A D.k).inv ≫
          pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ A)))
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) ≫ j.left = _
        rw [pullbackSpecIso_inv_fst]
      have hf : (ev z).comp
          (Algebra.TensorProduct.includeLeftRingHom : A →+* (A ⊗[D.k₀] D.k)) =
            (D.extensionSubfield m hm).subtype.comp (ap z).toRingHom := by
        ext b
        obtain ⟨b', rfl⟩ := p.surjective b
        obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b'
        change ε₀ (Ideal.Quotient.mk _ (p (Ideal.Quotient.mk a f) ⊗ₜ 1)) z = _
        rw [hε]
        simp [ap]
      change (Spec.map (CommRingCat.ofHom (ev z)) ≫ chartMap D X₀ A j) ≫
        pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
          x (yp z) ≫ pullback.fst X₀.hom
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
      rw [Category.assoc, hc, hxp]
      change Spec.map (CommRingCat.ofHom (ev z)) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom : A →+* (A ⊗[D.k₀] D.k))) ≫ j.left =
        Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype) ≫
          Spec.map (CommRingCat.ofHom (ap z).toRingHom) ≫ j.left
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hf,
        CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    · have hc : chartMap D X₀ A j ≫ (D.geometricFiber X₀).hom =
          Spec.map (CommRingCat.ofHom (algebraMap D.k (A ⊗[D.k₀] D.k))) := by
        dsimp only [chartMap]
        simp only [FiniteFieldDatum.geometricFiber, Over.pullback_map_left,
          Over.pullback_obj_hom, Category.assoc, pullback.lift_snd]
        exact pullbackSpecIso_inv_snd D.k₀ A D.k
      change (_ ≫ chartMap D X₀ A j) ≫ (D.geometricFiber X₀).hom =
        x (yp z) ≫ (D.geometricFiber X₀).hom
      rw [Category.assoc, hc, hxs, ← Spec.map_comp]
      have hf : ((Pi.evalRingHom (fun _ : D.relationSolutions m hm r a ↦ D.k) z).comp
          (ε₀.toRingHom.comp (Ideal.Quotient.mk (differenceIdeal D A m)))).comp
            (algebraMap D.k (A ⊗[D.k₀] D.k)) = RingHom.id D.k := by
        ext c
        change ε₀ (algebraMap D.k ((A ⊗[D.k₀] D.k) ⧸ differenceIdeal D A m) c) z = c
        rw [AlgEquiv.commutes]
        rfl
      simp only [← CommRingCat.ofHom_comp, hf, CommRingCat.ofHom_id, Spec.map_id]
  refine ⟨Pj, ?_, hPj, ε, ?_⟩
  · intro y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨_, heval z⟩
    · rintro ⟨b, hb⟩
      have hc : chartMap D X₀ A j ≫ pullback.fst X₀.hom
              (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
            Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeLeftRingHom : A →+* (A ⊗[D.k₀] D.k))) ≫ j.left := by
        dsimp only [chartMap]
        simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst]
        rw [← Category.assoc]
        change ((pullbackSpecIso D.k₀ A D.k).inv ≫
          pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ A)))
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) ≫ j.left = _
        rw [pullbackSpecIso_inv_fst]
      have hp := congrArg (fun f ↦ f ≫ pullback.fst X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) hb
      rw [Category.assoc, hc, hxp] at hp
      have hrange : Set.range y.left ⊆ Set.range j.left := by
        rintro _ ⟨t, rfl⟩
        let s := IsLocalRing.closedPoint D.k
        have ht : Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype) s = t :=
          Subsingleton.elim _ _
        refine ⟨Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom : A →+* (A ⊗[D.k₀] D.k))) (b s), ?_⟩
        have hp' := congrArg (fun f : Spec (.of D.k) ⟶ X₀.left ↦ f s) hp
        change j.left _ = y.left _ at hp'
        exact hp'.trans (congrArg y.left ht)
      let bE := IsOpenImmersion.lift j.left y.left hrange
      have hbE : bE ≫ j.left = y.left := IsOpenImmersion.lift_fac j.left y.left hrange
      let w : Over.mk (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) ⟶
          model D A := Over.homMk bE (by
        change bE ≫ (model D A).hom = Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))
        rw [← Over.w j, ← Category.assoc, hbE]
        exact Over.w y)
      let φ := (affinePointEquiv D.k₀ A (D.extensionSubfield m hm)).symm w
      let z := points.symm (φ.comp p.toAlgHom)
      have hap : ap z = φ := by
        apply AlgHom.ext
        intro b
        change points (points.symm (φ.comp p.toAlgHom)) (p.symm b) = φ b
        rw [points.apply_symm_apply]
        simp
      have hw : affinePointEquiv D.k₀ A (D.extensionSubfield m hm) (ap z) = w := by
        rw [hap]
        exact (affinePointEquiv D.k₀ A (D.extensionSubfield m hm)).apply_symm_apply w
      refine ⟨z, ?_⟩
      apply Over.OverMorphism.ext
      change ((affinePointEquiv D.k₀ A (D.extensionSubfield m hm) (ap z)) ≫ j).left = y.left
      rw [hw]
      exact hbE
  · intro y
    obtain ⟨z, rfl⟩ := ι.surjective y
    have hev : (Pi.evalRingHom (fun _ : Pj ↦ D.k) (ι z)).comp
        (ε.toRingHom.comp (Ideal.Quotient.mk (differenceIdeal D A m))) = ev z := by
      apply RingHom.ext
      intro b
      change ε₀ (Ideal.Quotient.mk _ b) (ι.symm (ι z)) = ε₀ (Ideal.Quotient.mk _ b) z
      rw [ι.symm_apply_apply]
    change Spec.map (CommRingCat.ofHom
      ((Pi.evalRingHom (fun _ : Pj ↦ D.k) (ι z)).comp
        (ε.toRingHom.comp (Ideal.Quotient.mk (differenceIdeal D A m))))) ≫
        chartMap D X₀ A j = x (yp z)
    rw [hev]
    exact heval z


private theorem exists_evaluation_atlas (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (m : ℕ) (hm : 1 ≤ m) (h : D.geometricFiber X₀ ⟶ D.geometricFiber X₀)
    (hh : h.left = ((End.of (D.relativeFrobenius X₀)) ^ m))
    (x : D.extensionPoints X₀ m hm → (Spec (.of D.k) ⟶ (D.geometricFiber X₀).left))
    (hxs : ∀ y, x y ≫ (D.geometricFiber X₀).hom = 𝟙 _)
    (hxp : ∀ y, x y ≫ pullback.fst X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype) ≫ y.left) :
    Nonempty (FrobeniusEvaluationAtlasData D X₀ m hm h x) := by
  classical
  obtain ⟨⟨n, A, j, hA, hcover⟩, _, h', hh', hcharts⟩ := presentation D X₀ m hm
  let (i : Fin n) : Algebra.FiniteType D.k₀ (A i) := (hA i).1
  let (i : Fin n) : IsOpenImmersion (j i).left := (hA i).2
  have heval (i : Fin n) :
      ∃ Pj : Set (D.extensionPoints X₀ m hm),
        (∀ y, y ∈ Pj ↔ ∃ b : Spec (.of D.k) ⟶ Spec (.of (A i ⊗[D.k₀] D.k)),
          b ≫ chartMap D X₀ (A i) (j i) = x y) ∧
        Finite Pj ∧
        ∃ ε : ((A i ⊗[D.k₀] D.k) ⧸ differenceIdeal D (A i) m) ≃ₐ[D.k] (Pj → D.k),
          ∀ y : Pj, Spec.map (CommRingCat.ofHom
            ((Pi.evalRingHom (fun _ : Pj ↦ D.k) y).comp
              (ε.toRingHom.comp (Ideal.Quotient.mk (differenceIdeal D (A i) m))))) ≫
            chartMap D X₀ (A i) (j i) = x y.val := by
    obtain ⟨r, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp
      (inferInstance : Algebra.FiniteType D.k₀ (A i))
    let a := RingHom.ker f.toRingHom
    let p : (MvPolynomial (Fin r) D.k₀ ⧸ a) ≃ₐ[D.k₀] A i :=
      Ideal.quotientKerAlgEquivOfSurjective hf
    obtain ⟨_, _, _, e, _, hpres, _⟩ := hcharts (A i) (j i) inferInstance
    obtain ⟨θ, _, _, ν, hν, _⟩ := hpres r a p
    let νk : ((A i ⊗[D.k₀] D.k) ⧸ differenceIdeal D (A i) m) ≃ₐ[D.k]
        (MvPolynomial (Fin r) D.k ⧸ (extendedIdeal D r a ⊔ powerIdeal D m r)) :=
      { ν with
        commutes' := by
          intro c
          change ν (Ideal.Quotient.mk _ (1 ⊗ₜ c)) = Ideal.Quotient.mk _ (MvPolynomial.C c)
          simpa only [map_one, one_mul] using hν 1 c }
    exact frobenius_chart_evaluation D X₀ m hm (A i) (j i) r a p νk hν x hxs hxp
  choose Pj hlabels hfinite ε hevaluation using heval
  let φ (i : Fin n) : (A i ⊗[D.k₀] D.k) →ₐ[D.k] (A i ⊗[D.k₀] D.k) :=
    { (tensorFrobenius D (A i) m).toRingHom with
      commutes' := by
        intro c
        change tensorFrobenius D (A i) m (1 ⊗ₜ c) = 1 ⊗ₜ c
        simp [tensorFrobenius, Algebra.TensorProduct.map_tmul] }
  refine ⟨{
    n := n
    B := fun i ↦ CommAlgCat.of D.k (A i ⊗[D.k₀] D.k)
    c := fun i ↦ chartMap D X₀ (A i) (j i)
    openImmersion := fun i ↦ (geometric_chart_open_base D X₀ (A i) (j i)).1
    covers := geometric_chart_cover D X₀ n A j hcover
    overBase := fun i ↦ (geometric_chart_open_base D X₀ (A i) (j i)).2
    φ := φ
    commutes := ?_
    I := fun i ↦ differenceIdeal D (A i) m
    differenceIdeal := fun _ ↦ rfl
    Pj := Pj
    labels := hlabels
    finiteLabels := hfinite
    ε := ε
    evaluation := hevaluation }⟩
  intro i
  have hc := (hcharts (A i) (j i) inferInstance).2.1
  have heq : h'.left = h.left := hh'.trans hh.symm
  rw [heq] at hc
  exact hc

private theorem extension_point_family_fixed (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (m : ℕ) (hm : 1 ≤ m)
    (x : D.extensionPoints X₀ m hm → (Spec (.of D.k) ⟶ (D.geometricFiber X₀).left))
    (hxp : ∀ y, x y ≫ pullback.fst X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype) ≫ y.left) :
    ∀ y, x y ≫ ((End.of (D.relativeFrobenius X₀)) ^ m) = x y := by
  let X := D.geometricFiber X₀
  let π := pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  let P : End X.left := D.relativeFrobenius X₀
  let Q : End X₀.left := X₀.left.iterateFrobenius D.prime (D.model_characteristic X₀.hom) D.a
  have hP : P ≫ π = π ≫ Q := (D.relativeFrobenius_projections X₀).1
  have hQ : Q ^ m = X₀.left.iterateFrobenius D.prime
      (D.model_characteristic X₀.hom) (D.a * m) :=
    (absolute_mul X₀.left D.p D.prime (D.model_characteristic X₀.hom) D.a m).symm
  have hπ : ((End.of (D.relativeFrobenius X₀)) ^ m) ≫ π = π ≫
      X₀.left.iterateFrobenius D.prime (D.model_characteristic X₀.hom) (D.a * m) := by
    change (P ^ m) ≫ π = _
    rw [pow_intertwine P Q π hP, hQ]
  have hs : ((End.of (D.relativeFrobenius X₀)) ^ m) ≫ X.hom = X.hom := by
    have hc : P ≫ X.hom = X.hom := by
      change D.relativeFrobenius X₀ ≫ (D.geometricFiber X₀).hom = (D.geometricFiber X₀).hom
      exact (D.relativeFrobenius_projections X₀).2
    change (P ^ m) ≫ X.hom = X.hom
    calc
      (P ^ m) ≫ X.hom = X.hom ≫ (1 : End (Spec (.of D.k))) ^ m :=
        pow_intertwine P _ X.hom (hc.trans (Category.comp_id _).symm) m
      _ = X.hom := by rw [one_pow]; exact Category.comp_id _
  intro y
  have hy : y.left ≫ X₀.left.iterateFrobenius D.prime
      (D.model_characteristic X₀.hom) (D.a * m) = y.left := by
    have hroot (c : D.extensionSubfield m hm) : c ^ (D.q ^ m) = c := by
      apply Subtype.ext
      exact ((FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime
        D.exponent_pos D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.1 c.val).mp
          c.property
    have h := Scheme.isFrobenius_iterateFrobenius D.prime X₀.left
      (D.model_characteristic X₀.hom) (D.a * m) y.left
        (𝟙 (CommRingCat.of (D.extensionSubfield m hm))) (by
          intro c
          change c = c ^ (D.p ^ (D.a * m))
          rw [pow_mul, ← D.cardinality_eq]
          exact (hroot c).symm)
    simpa using h
  apply pullback.hom_ext
  · change (x y ≫ ((End.of (D.relativeFrobenius X₀)) ^ m)) ≫ π = x y ≫ π
    rw [Category.assoc, hπ, ← Category.assoc, hxp, Category.assoc, hy]
  · change (x y ≫ ((End.of (D.relativeFrobenius X₀)) ^ m)) ≫ X.hom = x y ≫ X.hom
    rw [Category.assoc, hs]



/-- The fixed scheme of the positive iterate of model Frobenius is a finite disjoint
union of the base point, indexed by the extension-valued points of the model. It is
finite, reduced, and proper over the algebraic closure.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-tf-curve-local/sk-lem-tf-fixed-points/_section.md
(blueprint: sk-lem-tf-fixed-points).

Proof: choose finitely many affine opens of the finite-type model. Absolute Frobenius
preserves each open, so their scalar extensions give a stable affine cover. On a chart
`k[t]/a`, model Frobenius fixes scalars and sends each coordinate to its `q^m`-th power.
Its difference ideal is generated by `t_i^(q^m)-t_i` (telescoping products gives the
inclusion for every polynomial). The affine fixed-point equations therefore give the
quotient by these relations and the defining equations. The separable polynomials
`t^(q^m)-t` split over `k`; evaluation identifies the quotient with the product of `k`
indexed by the rational solutions of the defining equations. Each index set is finite.
For an extension-valued point, its scalar extension is fixed, by naturality of absolute
Frobenius and `a^(q^m)=a` in the extension field. On each chart this scalar extension is
exactly the evaluation morphism. The equalizer point-chart descent lemma glues these
normalized descriptions on arbitrary overlaps and proves finiteness of the whole index
set and of the structural map. Its structural local rings are `k`, so the scheme is
reduced. Finally a finite morphism is proper. The calculation uses no reducedness of
the model and includes the empty scheme and empty index set. -/
theorem modelFrobenius_fixedScheme
    (D : FiniteFieldDatum.{u}) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (m : ℕ) (hm : 1 ≤ m) :
    Finite (D.extensionPoints X₀ m hm) ∧
      Nonempty
        (Over.mk
          (trfEndomorphismFixedInclusion (D.geometricFiber X₀)
            (frobeniusPower (modelFrobenius D X₀) m) ≫ (D.geometricFiber X₀).hom) ≅
          Over.mk (Sigma.desc fun _ : D.extensionPoints X₀ m hm ↦ 𝟙 (Spec (.of D.k)))) ∧
      IsFinite
        (trfEndomorphismFixedInclusion (D.geometricFiber X₀)
          (frobeniusPower (modelFrobenius D X₀) m) ≫ (D.geometricFiber X₀).hom) ∧
      IsReduced
        (trfEndomorphismFixedScheme (D.geometricFiber X₀)
          (frobeniusPower (modelFrobenius D X₀) m)) ∧
      IsProper
        (trfEndomorphismFixedInclusion (D.geometricFiber X₀)
          (frobeniusPower (modelFrobenius D X₀) m) ≫ (D.geometricFiber X₀).hom) := by
  classical
  let X := D.geometricFiber X₀
  let h := frobeniusPower (modelFrobenius D X₀) m
  have hpowers (n : ℕ) : (frobeniusPower (modelFrobenius D X₀) n).left =
      (End.of (D.relativeFrobenius X₀)) ^ n := by
    induction n with
    | zero => rfl
    | succ m ih =>
      change (frobeniusPower (modelFrobenius D X₀) m).left ≫
        (modelFrobenius D X₀).left = _
      rw [ih, modelFrobenius_left, pow_succ, End.mul_def]
      exact (Commute.self_pow (End.of (D.relativeFrobenius X₀)) m).eq
  have hh : h.left = (End.of (D.relativeFrobenius X₀)) ^ m := hpowers m
  obtain ⟨x, hxs, hxp⟩ := exists_extension_point_family D X₀ m hm
  have hfixed : ∀ y, x y ≫ h.left = x y := by
    rw [hh]
    exact extension_point_family_fixed D X₀ m hm x hxp
  obtain ⟨atlas⟩ := exists_evaluation_atlas D X₀ m hm h hh x hxs hxp
  have (j : Fin atlas.n) : IsOpenImmersion (atlas.c j) := atlas.openImmersion j
  have (j : Fin atlas.n) : Finite (atlas.Pj j) := atlas.finiteLabels j
  obtain ⟨hfinite, q, hq, _, hqiso, _, hfin, _, _⟩ :=
    equalizer_point_chart_descent D.k X.left X.hom h.left (Over.w h)
      (trfFixedGraphMap X h)
      (by simp [trfFixedGraphMap]) (by simp [trfFixedGraphMap])
      (Fin atlas.n) (fun j ↦ atlas.B j) atlas.c atlas.covers atlas.overBase
      atlas.φ atlas.commutes atlas.I atlas.differenceIdeal
      (D.extensionPoints X₀ m hm) x hxs hfixed atlas.Pj atlas.labels
      atlas.ε atlas.evaluation
  have : IsIso q := hqiso
  let C := fun _ : D.extensionPoints X₀ m hm ↦ Spec (.of D.k)
  let a := trfEndomorphismFixedInclusion X h ≫ X.hom
  let b := Sigma.desc fun _ : D.extensionPoints X₀ m hm ↦ 𝟙 (Spec (.of D.k))
  have hbase : q ≫ a = b := by
    apply Sigma.hom_ext
    intro y
    simpa only [a, b, Sigma.ι_desc, trfEndomorphismFixedInclusion, Category.assoc]
      using (congrArg (fun f ↦ f ≫ X.hom) (hq y)).trans (hxs y)
  have hredC : IsReduced (∐ C) := by
    apply isReduced_of_isOpenImmersion (sigmaSpec (fun _ : D.extensionPoints X₀ m hm ↦
      CommRingCat.of D.k))
  have hred : IsReduced (trfEndomorphismFixedScheme X h) :=
    isReduced_of_isOpenImmersion (inv q)
  have : IsFinite a := hfin
  refine ⟨hfinite, ⟨(Over.isoMk (asIso q) hbase).symm⟩, hfin, hred, ?_⟩
  infer_instance

end WeilConjectures.TraceWeilComplex
