/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FiniteFieldDatum.SchemeFrobenius
public import WeilConjectures.TraceFormula.FiniteFieldDatum.FrobeniusAffineEqualizer.FrobeniusAffineEqualizerPresentation
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.SixFunctors.FiniteFieldDatum.FiniteFieldRelationsEvaluation
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Algebra.Algebra.Pi

/-!
# Evaluation atlas for scheme Frobenius

Source: latest blueprint, `thm-trf-frobenius-fixed-points.proof.md`, Steps 0–2
(blueprint: lem-trf-frobenius-evaluation-atlas).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace WeilConjectures

open FiniteFieldDatum.FrobeniusAffineEqualizer

private noncomputable def affinePointEquiv (R A E : Type u) [CommRing R] [CommRing A]
    [CommRing E] [Algebra R A] [Algebra R E] :
    (A →ₐ[R] E) ≃
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R E))) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) where
  toFun f := Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A)) =
        Spec.map (CommRingCat.ofHom (algebraMap R E))
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (AlgHom.comp_algebraMap f))
  invFun f :=
    { (Spec.preimage f.left).hom with
      commutes' := by
        have hw := Over.w f
        change f.left ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
          Spec.map (CommRingCat.ofHom (algebraMap R E)) at hw
        have heCat : CommRingCat.ofHom
            ((Spec.preimage f.left).hom.comp (algebraMap R A)) =
            CommRingCat.ofHom (algebraMap R E) := by
          apply Spec.map_injective
          rw [CommRingCat.ofHom_comp, Spec.map_comp,
            CommRingCat.ofHom_hom, Spec.map_preimage]
          exact hw
        have he := congrArg CommRingCat.Hom.hom heCat
        exact fun r ↦ congrFun (congrArg DFunLike.coe he) r }
  left_inv f := by
    apply AlgHom.ext
    intro a
    change (Spec.preimage (Spec.map (CommRingCat.ofHom f.toRingHom))).hom a = f a
    rw [Spec.preimage_map]
    rfl
  right_inv f := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (Spec.preimage f.left).hom) = f.left
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]


/-- Affine evaluation data, before any descent or tangent-space assertion.
The labels are the prescribed extension points, and the evaluation maps are normalized
as morphisms into the geometric fibre, rather than just abstract ring isomorphisms.
Source: latest blueprint, Frobenius fixed points, Steps 0–2
(blueprint: lem-trf-frobenius-evaluation-atlas). -/
structure FrobeniusEvaluationAtlasData (D : FiniteFieldDatum.{u})
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
theorem frobenius_chart_evaluation (D : FiniteFieldDatum.{u})
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

end WeilConjectures
