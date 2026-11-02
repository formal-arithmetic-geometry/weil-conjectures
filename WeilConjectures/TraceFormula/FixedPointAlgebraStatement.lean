/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFieldDatum.FiniteFieldRelationsEvaluation
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.RelativeFrobeniusGeometricFiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.TraceFormula.FiniteFieldDatum.FrobeniusAffineEqualizer.FrobeniusFixedPointEquations

/-!
# Evaluation and the affine Frobenius fixed scheme

Source: latest blueprint, `sec-trace-formula/sk-lem-tf-fixed-points/`
`det-tf-fixed-point-algebra.md` and its proof
(blueprint: det-tf-fixed-point-algebra).

The two evaluation isomorphisms, their evaluation formulas and their identification of
surviving tuples with model algebra maps are the existing declaration
`FiniteFieldDatum.finite_field_relations_evaluation`; they are not restated here.
This module states the geometric consequence and its affine-open compatibility.
Mathlib's equalizer is the fixed scheme: it represents maps on which Frobenius is the
identity, equivalently the pullback of the graph along the diagonal. No coefficient or
cohomological realization enters this construction.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures

/-- Algebra maps from the presented model to the prescribed extension field are exactly
its field-valued scheme points over the finite base, with the usual contravariant Spec map.
Together with `finite_field_relations_evaluation`, this indexes the second evaluation
product by the field-valued points appearing in the node.

Source: latest blueprint `sec-trace-formula/sk-lem-tf-fixed-points/`
`det-tf-fixed-point-algebra.proof.md`, surviving rational solutions
(blueprint: det-tf-fixed-point-algebra).

Proof: Spec is fully faithful on commutative rings, so its morphisms between these affine
schemes are exactly the reversed ring homomorphisms. The equation of being over Spec k₀
is equivalent, by faithfulness, to commuting with the two coefficient maps. This is
exactly the algebra-homomorphism condition for the algebra structure induced by the
specified extension embedding. Restricting the Spec bijection to these maps gives the
equivalence and its displayed normalization. The zero ring is allowed: in that case both
sets are empty, since the target extension field is nontrivial. -/
theorem det_tf_fixed_point_algebra_points
    (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m) (r : ℕ)
    (a : Ideal (MvPolynomial (Fin r) D.k₀)) :
    letI : Algebra D.k₀ (D.extensionSubfield m hm) :=
      (D.extensionEmbedding m hm).toAlgebra
    ∃ e : D.relationModelPoints m hm r a ≃
        (Over.mk (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) ⟶
          Over.mk (Spec.map (CommRingCat.ofHom
            (algebraMap D.k₀ (MvPolynomial (Fin r) D.k₀ ⧸ a))))),
      ∀ φ : D.relationModelPoints m hm r a,
        (e φ).left = Spec.map (CommRingCat.ofHom φ.toRingHom) := by
  sorry

private theorem affine_polynomial_model (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsAffine X₀.left] :
    ∃ (r : ℕ) (a : Ideal (MvPolynomial (Fin r) D.k₀)),
      Nonempty (model D (CommAlgCat.of D.k₀ (MvPolynomial (Fin r) D.k₀ ⧸ a)) ≅ X₀) := by
  classical
  let R := Γ(X₀.left, ⊤)
  let φ : CommRingCat.of D.k₀ ⟶ R := Spec.preimage (X₀.left.isoSpec.inv ≫ X₀.hom)
  let : Algebra D.k₀ R := φ.hom.toAlgebra
  have hφ : Spec.map φ = X₀.left.isoSpec.inv ≫ X₀.hom := Spec.map_preimage _
  have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
  have ht : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  have : Algebra.FiniteType D.k₀ R := (RingHom.finiteType_algebraMap).mp ht
  obtain ⟨r, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp this
  let a := RingHom.ker f
  let p : (MvPolynomial (Fin r) D.k₀ ⧸ a) ≃ₐ[D.k₀] R :=
    Ideal.quotientKerAlgEquivOfSurjective hf
  let e : Spec (.of (MvPolynomial (Fin r) D.k₀ ⧸ a)) ≅ X₀.left :=
    (Scheme.Spec.mapIso p.symm.toRingEquiv.toCommRingCatIso.op) ≪≫ X₀.left.isoSpec.symm
  refine ⟨r, a, ⟨Over.isoMk e ?_⟩⟩
  change Spec.map (CommRingCat.ofHom p.symm.toRingHom) ≫
      X₀.left.isoSpec.inv ≫ X₀.hom =
    Spec.map (CommRingCat.ofHom (algebraMap D.k₀ (MvPolynomial (Fin r) D.k₀ ⧸ a)))
  rw [← hφ, ← Spec.map_comp]
  congr 1
  ext x
  exact p.symm.commutes x

/-- The equations and evaluation product give the normalized affine decomposition. -/
private theorem affine_fixed_decomposition
    (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsAffine X₀.left] :
    let X := D.geometricFiber X₀
    let Φ := (End.of (D.relativeFrobenius X₀)) ^ m
    let F := equalizer Φ (𝟙 X.left)
    let ι := equalizer.ι Φ (𝟙 X.left)
    let P := D.extensionPoints X₀ m hm
    let C := fun _ : P ↦ Spec (.of D.k)
    Finite P ∧ ∃ e : (∐ C) ≅ F,
      (∀ x : P, Sigma.ι C x ≫ e.hom ≫ ι ≫
        pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
          Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype) ≫ x.left) ∧
      (∀ x : P, Sigma.ι C x ≫ e.hom ≫ ι ≫ X.hom = 𝟙 _) ∧
      IsFinite (ι ≫ X.hom) ∧ IsReduced F := by
  classical
  let : Algebra D.k₀ (D.extensionSubfield m hm) :=
    (D.extensionEmbedding m hm).toAlgebra
  obtain ⟨r, a, ⟨j⟩⟩ := affine_polynomial_model D X₀
  let A := CommAlgCat.of D.k₀ (MvPolynomial (Fin r) D.k₀ ⧸ a)
  obtain ⟨h, hh, θ, hθ, π, hπ, _, ee, hee, _⟩ :=
    fixedPointEquations D X₀ A j r a (AlgEquiv.refl) m hm
  obtain ⟨_, e₂, pts, _, _, _, _, hfinite, _, hscalar⟩ :=
    D.finite_field_relations_evaluation m hm r a
  dsimp only [extendedIdeal, powerIdeal, FiniteFieldDatum.extendedRelationIdeal,
    FiniteFieldDatum.relationEquationIdeal] at θ hθ π hπ ee hee e₂ hscalar
  obtain ⟨pointEquiv, hpoint⟩ := det_tf_fixed_point_algebra_points D m hm r a
  let S := D.relationSolutions m hm r a
  let P := D.extensionPoints X₀ m hm
  let lab : S ≃ P := pts.trans (pointEquiv.trans
    { toFun := fun x ↦ x ≫ j.hom
      invFun := fun x ↦ x ≫ j.inv
      left_inv := by intro x; simp [Category.assoc]
      right_inv := by intro x; simp [Category.assoc] })
  have hlab (x : S) : (lab x).left =
      Spec.map (CommRingCat.ofHom (pts x).toRingHom) ≫ j.hom.left := by
    change (pointEquiv (pts x)).left ≫ j.hom.left = _
    rw [hpoint]
  have : Finite S := hfinite.to_subtype
  have : Finite P := Finite.of_equiv S lab
  have hh' : h.left = (End.of (D.relativeFrobenius X₀)) ^ m := hh
  let k : equalizer h.left (𝟙 _) ≅
      equalizer ((End.of (D.relativeFrobenius X₀)) ^ m) (𝟙 _) :=
    { hom := equalizer.lift (equalizer.ι h.left (𝟙 _))
        (by rw [← hh']; exact equalizer.condition _ _)
      inv := equalizer.lift (equalizer.ι ((End.of (D.relativeFrobenius X₀)) ^ m) (𝟙 _))
        (by rw [hh']; exact equalizer.condition _ _)
      hom_inv_id := by apply equalizer.hom_ext; simp [Category.assoc]
      inv_hom_id := by apply equalizer.hom_ext; simp [Category.assoc] }
  have hk : k.hom ≫ equalizer.ι _ _ = equalizer.ι h.left (𝟙 _) := by
    exact equalizer.lift_ι _ _
  let C := fun _ : P ↦ Spec (.of D.k)
  let T := C ∘ lab
  let d : (∐ T) ≅ equalizer ((End.of (D.relativeFrobenius X₀)) ^ m) (𝟙 _) :=
    asIso (sigmaSpec (fun _ : S ↦ CommRingCat.of D.k)) ≪≫
      Scheme.Spec.mapIso e₂.toRingEquiv.toCommRingCatIso.op ≪≫ ee.symm ≪≫ k
  let e : (∐ C) ≅ equalizer ((End.of (D.relativeFrobenius X₀)) ^ m) (𝟙 _) :=
    (Sigma.reindex lab C).symm ≪≫ d
  let v (x : S) : (A ⊗[D.k₀] D.k) →+* D.k :=
    (Pi.evalRingHom (fun _ : S ↦ D.k) x).comp
      (e₂.toRingHom.comp (π.comp θ.toRingHom))
  have hv (x : S) (f : MvPolynomial (Fin r) D.k₀) (z : D.k) :
      v x (Ideal.Quotient.mk a f ⊗ₜ z) =
        z * (D.extensionSubfield m hm).subtype (pts x (Ideal.Quotient.mk a f)) := by
    change e₂ (π (θ (Ideal.Quotient.mk a f ⊗ₜ z))) x = _
    exact (congrArg (fun b ↦ e₂ (π b) x) (hθ f z)).trans
      ((congrArg (fun b ↦ e₂ b x)
        (hπ (MvPolynomial.map (algebraMap D.k₀ D.k) f * MvPolynomial.C z))).trans
          (by simpa only [mul_comm] using hscalar x z f))
  have hvleft (x : S) :
      (v x).comp Algebra.TensorProduct.includeLeftRingHom =
        (D.extensionSubfield m hm).subtype.comp (pts x).toRingHom := by
    apply RingHom.ext
    intro b
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
    simpa using hv x f 1
  have hvright (x : S) :
      (v x).comp (Algebra.TensorProduct.includeRight.toRingHom) = RingHom.id D.k := by
    apply RingHom.ext
    intro z
    simpa using hv x 1 z
  have hd (x : S) : Sigma.ι T x ≫ d.hom ≫ equalizer.ι _ _ =
      Spec.map (CommRingCat.ofHom (v x)) ≫ chartMap D X₀ A j.hom := by
    have hee' : ee.inv ≫ equalizer.ι h.left (𝟙 _) =
        Spec.map (CommRingCat.ofHom π) ≫ Spec.map (CommRingCat.ofHom θ.toRingHom) ≫
          chartMap D X₀ A j.hom := by
      rw [← hee]
      simp
    dsimp only [d, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, Category.assoc, Category.assoc, hk, hee']
    change Sigma.ι (fun _ : S ↦ Spec (.of D.k)) x ≫
      sigmaSpec (fun _ : S ↦ CommRingCat.of D.k) ≫
      Spec.map (CommRingCat.ofHom e₂.toRingHom) ≫ Spec.map (CommRingCat.ofHom π) ≫
      Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ chartMap D X₀ A j.hom = _
    rw [ι_sigmaSpec_assoc]
    simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    rfl
  have hdfst (x : S) : Sigma.ι T x ≫ d.hom ≫ equalizer.ι _ _ ≫
      pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
        Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype) ≫
          (lab x).left := by
    rw [reassoc_of% hd x, hlab]
    simp only [chartMap, Category.assoc, Over.pullback_map_left,
      pullback.lift_fst]
    dsimp only [model, Over.mk_hom]
    rw [pullbackSpecIso_inv_fst_assoc]
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hvleft]
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  have hdbase (x : S) : Sigma.ι T x ≫ d.hom ≫ equalizer.ι _ _ ≫
      (D.geometricFiber X₀).hom = 𝟙 _ := by
    rw [reassoc_of% hd x]
    change Spec.map (CommRingCat.ofHom (v x)) ≫
      chartMap D X₀ A j.hom ≫ pullback.snd _ _ = _
    simp only [chartMap, Category.assoc, Over.pullback_map_left,
      pullback.lift_snd]
    dsimp only [model, Over.mk_hom]
    rw [pullbackSpecIso_inv_snd]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact (congrArg (fun f : D.k →+* D.k ↦ Spec.map (CommRingCat.ofHom f))
      (hvright x)).trans (Spec.map_id _)
  have hefst (x : P) : Sigma.ι C x ≫ e.hom ≫ equalizer.ι _ _ ≫
      pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
        Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype) ≫ x.left := by
    obtain ⟨x, rfl⟩ := lab.surjective x
    simpa only [e, Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
      Sigma.ι_reindex_inv, T, C, Function.comp_def] using hdfst x
  have hebase (x : P) : Sigma.ι C x ≫ e.hom ≫ equalizer.ι _ _ ≫
      (D.geometricFiber X₀).hom = 𝟙 _ := by
    obtain ⟨x, rfl⟩ := lab.surjective x
    simpa only [e, Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
      Sigma.ι_reindex_inv, T, C, Function.comp_def] using hdbase x
  refine ⟨inferInstance, e, hefst, hebase, ?_, ?_⟩
  · let z := Spec.map (CommRingCat.ofHom (algebraMap D.k (P → D.k)))
    have hz : IsFinite z := by
      apply (IsFinite.SpecMap_iff _).mpr
      exact RingHom.finite_algebraMap.mpr inferInstance
    have he : e.hom ≫ equalizer.ι _ _ ≫ (D.geometricFiber X₀).hom =
        sigmaSpec (fun _ : P ↦ CommRingCat.of D.k) ≫ z := by
      apply Sigma.hom_ext
      intro x
      rw [hebase]
      change 𝟙 (Spec (.of D.k)) =
        Sigma.ι (fun _ : P ↦ Spec (.of D.k)) x ≫
          sigmaSpec (fun _ : P ↦ CommRingCat.of D.k) ≫ z
      rw [ι_sigmaSpec_assoc]
      dsimp only [z]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact (Spec.map_id _).symm
    have hf : IsFinite (e.hom ≫ equalizer.ι _ _ ≫ (D.geometricFiber X₀).hom) := by
      rw [he]
      infer_instance
    have hf' : IsFinite
        (e.inv ≫ (e.hom ≫ equalizer.ι _ _ ≫ (D.geometricFiber X₀).hom)) := inferInstance
    simpa only [Iso.inv_hom_id_assoc] using hf'
  · have : IsReduced (∐ C) :=
      isReduced_of_isOpenImmersion (sigmaSpec (fun _ : P ↦ CommRingCat.of D.k))
    exact isReduced_of_isOpenImmersion e.inv

end WeilConjectures
