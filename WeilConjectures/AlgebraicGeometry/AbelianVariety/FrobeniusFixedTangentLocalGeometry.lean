/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FiniteFieldDatum.SchemeFrobenius
public import WeilConjectures.SmoothPurity.TraceFixedScheme
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.LinearAlgebra.Prod
import WeilConjectures.AlgebraicGeometry.PowerMapLocalData.PowerMapSmoothGraphLocalData
import WeilConjectures.TraceFormula.FiniteFieldDatum.FrobeniusAffineEqualizer.FrobeniusAffineEqualizerPresentation
import WeilConjectures.PointCount
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Regular local geometry of Frobenius fixed points

Source: latest blueprint, `thm-trf-frobenius-fixed-points.proof.md`, Step 3,
and its regular-local expansion in the parent DAG
(blueprint: lem-trf-frobenius-fixed-tangent-local-geometry).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures

open scoped TensorProduct
open FiniteFieldDatum.FrobeniusAffineEqualizer AlgebraicGeometry.PowerMapLocalData
attribute [local instance] Algebra.TensorProduct.rightAlgebra

private theorem geometric_chart_open_base (D : FiniteFieldDatum.{u}) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (A : CommAlgCat.{u} D.k₀) (j : model D A ⟶ X₀) [IsOpenImmersion j.left] :
    IsOpenImmersion (chartMap D X₀ A j) ∧
    chartMap D X₀ A j ≫ (D.geometricFiber X₀).hom =
      Spec.map (CommRingCat.ofHom (algebraMap D.k (A ⊗[D.k₀] D.k))) := by
  have hj : ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j).left =
      pullback.map (model D A).hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j.left (𝟙 _) (𝟙 _)
        (by simp [Over.w]) (by simp) := by
    apply pullback.hom_ext <;> simp
  constructor
  · dsimp only [chartMap]
    rw [hj]
    infer_instance
  · dsimp only [chartMap]
    simp only [FiniteFieldDatum.geometricFiber, Over.pullback_map_left,
      Over.pullback_obj_hom, Category.assoc, pullback.lift_snd]
    exact pullbackSpecIso_inv_snd D.k₀ A D.k

private theorem geometric_chart_cover (D : FiniteFieldDatum.{u}) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (n : ℕ) (A : Fin n → CommAlgCat.{u} D.k₀) (j : ∀ i, model D (A i) ⟶ X₀)
    [∀ i, IsOpenImmersion (j i).left]
    (hcover : ∀ x : X₀.left, ∃ i, x ∈ Set.range (j i).left) :
    ∀ x : (D.geometricFiber X₀).left, ∃ i, x ∈ Set.range (chartMap D X₀ (A i) (j i)) := by
  intro x
  obtain ⟨i, a, ha⟩ := hcover
    (pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) x)
  let π := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  let b := pullback.map (model D (A i)).hom π X₀.hom π
    (j i).left (𝟙 _) (𝟙 _) (by simp [Over.w]) (by simp)
  have hb : IsPullback (pullback.fst (model D (A i)).hom π) b (j i).left
      (pullback.fst X₀.hom π) := by
    refine IsPullback.of_bot ?_ (by simp [b]) (IsPullback.of_hasPullback X₀.hom π)
    have h1 : b ≫ pullback.snd X₀.hom π = pullback.snd (model D (A i)).hom π := by
      simp [b]
    rw [h1]
    simpa only [Over.w] using IsPullback.of_hasPullback (model D (A i)).hom π
  have hxmem : x ∈ Set.range b := by
    rw [Scheme.range_snd_of_isPullback hb]
    exact ⟨a, ha⟩
  obtain ⟨z, hz⟩ := hxmem
  refine ⟨i, (pullbackSpecIso D.k₀ (A i) D.k).hom z, ?_⟩
  change ((pullbackSpecIso D.k₀ (A i) D.k).hom ≫
    (pullbackSpecIso D.k₀ (A i) D.k).inv ≫ b) z = x
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact hz


private theorem tensor_generators (D : FiniteFieldDatum.{u}) (A : CommAlgCat.{u} D.k₀)
    [Algebra.FiniteType D.k₀ A] (m : ℕ)
    (hφ : ∀ a : A, ∀ c : D.k,
      tensorFrobenius D A m (a ⊗ₜ c) = (a ^ (D.q ^ m)) ⊗ₜ c) :
    ∃ (r : ℕ) (t : Fin r → A ⊗[D.k₀] D.k),
      Subring.closure (Set.range (algebraMap D.k (A ⊗[D.k₀] D.k)) ∪ Set.range t) = ⊤ ∧
      ∀ i, tensorFrobenius D A m (t i) = t i ^ (D.q ^ m) := by
  classical
  obtain ⟨r, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp
    (inferInstance : Algebra.FiniteType D.k₀ A)
  let t (i : Fin r) := f (MvPolynomial.X i) ⊗ₜ[D.k₀] (1 : D.k)
  let S := Subring.closure (Set.range (algebraMap D.k (A ⊗[D.k₀] D.k)) ∪ Set.range t)
  have hc (c : D.k) : (1 : A) ⊗ₜ[D.k₀] c ∈ S :=
    Subring.subset_closure (.inl ⟨c, rfl⟩)
  have ht (i : Fin r) : t i ∈ S := Subring.subset_closure (.inr ⟨i, rfl⟩)
  have hleft (b : A) : b ⊗ₜ[D.k₀] (1 : D.k) ∈ S := by
    obtain ⟨g, rfl⟩ := hf b
    induction g using MvPolynomial.induction_on with
    | C c =>
      have he : f (MvPolynomial.C c) ⊗ₜ[D.k₀] (1 : D.k) =
          (1 : A) ⊗ₜ[D.k₀] algebraMap D.k₀ D.k c := by
        rw [MvPolynomial.algHom_C]
        exact (Algebra.TensorProduct.includeLeft.commutes c).trans
          (Algebra.TensorProduct.includeRight.commutes c).symm
      rw [he]
      exact hc _
    | add g h hg hh => simpa only [map_add, TensorProduct.add_tmul] using S.add_mem hg hh
    | mul_X g i hg =>
      have H := S.mul_mem hg (ht i)
      simpa only [t, map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul] using H
  have hall (b : A ⊗[D.k₀] D.k) : b ∈ S := by
    induction b using TensorProduct.induction_on with
    | zero => exact S.zero_mem
    | tmul a c =>
      simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using
        S.mul_mem (hleft a) (hc c)
    | add a b ha hb => exact S.add_mem ha hb
  refine ⟨r, t, eq_top_iff.mpr (fun b _ ↦ hall b), ?_⟩
  intro i
  change tensorFrobenius D A m (f (MvPolynomial.X i) ⊗ₜ 1) = _
  rw [hφ]
  simp [t, Algebra.TensorProduct.tmul_pow]
private theorem appLE_eq_of_eq {X Y : Scheme.{u}} (f g : X ⟶ Y) (e : f = g)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

private theorem chart_sections (k B : Type u) [Field k] [CommRing B] [Algebra k B]
    (X : Scheme.{u}) (s : X ⟶ Spec (.of k))
    (c : Spec (.of B) ⟶ X) [IsOpenImmersion c]
    (hbase : c ≫ s = Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (h : X ⟶ X) (φ : B →+* B)
    (hcomm : Spec.map (CommRingCat.ofHom φ) ≫ c = c ≫ h)
    (hstable : c.opensRange ≤ h ⁻¹ᵁ c.opensRange) :
    ∃ e : B ≃+* Γ(X, c.opensRange),
      (∀ b : k, e (algebraMap k B b) = PowerMapLocalData.sectionStructure s c.opensRange b) ∧
      ∀ b : B, (h.appLE c.opensRange c.opensRange hstable).hom (e b) = e (φ b) := by
  let O := c.opensRange
  have hcO : (⊤ : (Spec (.of B)).Opens) ≤ c ⁻¹ᵁ O := by
    rw [show c ⁻¹ᵁ O = ⊤ from c.preimage_opensRange]
  have : IsIso (homOfLE hcO) := homOfLE_isIso_of_eq hcO (le_antisymm hcO le_top)
  have : IsIso (c.app O) := c.isIso_app O le_rfl
  have : IsIso (c.appLE O ⊤ hcO) := by
    dsimp only [Scheme.Hom.appLE]
    infer_instance
  let a : Γ(X, O) ⟶ CommRingCat.of B := c.appLE O ⊤ hcO ≫ (Scheme.ΓSpecIso (.of B)).hom
  have : IsIso a := inferInstance
  let e := (asIso a).symm.commRingCatIsoToRingEquiv
  have he (b : B) : a (e b) = b := by
    exact ConcreteCategory.congr_hom (IsIso.inv_hom_id a) b
  have hscalar :
      (Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ O le_top ≫ a =
        CommRingCat.ofHom (algebraMap k B) := by
    dsimp only [a]
    rw [← Category.assoc (s.appLE _ _ _), Scheme.Hom.appLE_comp_appLE]
    change (Scheme.ΓSpecIso (.of k)).inv ≫ (c ≫ s).appTop ≫
      (Scheme.ΓSpecIso (.of B)).hom = _
    rw [hbase, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have hφ : h.appLE O O hstable ≫ a = a ≫ CommRingCat.ofHom φ := by
    dsimp only [a]
    rw [← Category.assoc (h.appLE _ _ _), Scheme.Hom.appLE_comp_appLE]
    have hother : (⊤ : (Spec (.of B)).Opens) ≤
        (Spec.map (CommRingCat.ofHom φ) ≫ c) ⁻¹ᵁ O := by
      change ⊤ ≤ (Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ (c ⁻¹ᵁ O)
      rw [show c ⁻¹ᵁ O = ⊤ from c.preimage_opensRange]
      simp
    rw [appLE_eq_of_eq (c ≫ h) (Spec.map (CommRingCat.ofHom φ) ≫ c)
      hcomm.symm O ⊤ _ hother]
    rw [← Scheme.Hom.appLE_comp_appLE
      (Spec.map (CommRingCat.ofHom φ)) c O ⊤ ⊤ hcO (by simp)]
    change c.appLE O ⊤ hcO ≫ (Spec.map (CommRingCat.ofHom φ)).appTop ≫
      (Scheme.ΓSpecIso (.of B)).hom = _
    rw [Scheme.ΓSpecIso_naturality, Category.assoc]
  refine ⟨e, ?_, ?_⟩
  · intro b
    apply e.symm.injective
    rw [e.symm_apply_apply]
    change algebraMap k B b = a (PowerMapLocalData.sectionStructure s O b)
    exact (ConcreteCategory.congr_hom hscalar b).symm
  · intro b
    apply e.symm.injective
    rw [e.symm_apply_apply]
    change a ((h.appLE O O hstable) (e b)) = φ b
    have H := ConcreteCategory.congr_hom hφ (e b)
    change a ((h.appLE O O hstable) (e b)) = φ (a (e b)) at H
    rwa [he] at H

private theorem exists_stable_power_chart (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (m : ℕ) (hm : 1 ≤ m) (h : D.geometricFiber X₀ ⟶ D.geometricFiber X₀)
    (hh : h.left = D.schemeFrobeniusIterate X₀ m)
    (x : (D.geometricFiber X₀).left) :
    ∃ (O : (D.geometricFiber X₀).left.Opens) (_hO : IsAffineOpen O), x ∈ O ∧
      ∃ (hstable : O ≤ h.left ⁻¹ᵁ O) (r : ℕ) (t : Fin r → Γ((D.geometricFiber X₀).left, O)),
        Subring.closure
          (Set.range (PowerMapLocalData.sectionStructure (D.geometricFiber X₀).hom O) ∪
            Set.range t) = ⊤ ∧
        ∀ i, (h.left.appLE O O hstable).hom (t i) = t i ^ (D.p ^ (D.a * m)) := by
  classical
  obtain ⟨⟨n, A, j, hA, hcover⟩, _, h', hh', hcharts⟩ := presentation D X₀ m hm
  let (i : Fin n) : Algebra.FiniteType D.k₀ (A i) := (hA i).1
  let (i : Fin n) : IsOpenImmersion (j i).left := (hA i).2
  obtain ⟨i, hxi⟩ := geometric_chart_cover D X₀ n A j hcover x
  let c := chartMap D X₀ (A i) (j i)
  have : IsOpenImmersion c := (geometric_chart_open_base D X₀ (A i) (j i)).1
  let O := c.opensRange
  have hO : IsAffineOpen O := isAffineOpen_opensRange c
  have hdata := hcharts (A i) (j i) inferInstance
  have hcomm : Spec.map (CommRingCat.ofHom (tensorFrobenius D (A i) m).toRingHom) ≫ c =
      c ≫ h.left := by simpa only [hh', ← hh] using hdata.2.1
  have hrange : h.left ⁻¹' Set.range c = Set.range c := by
    simpa only [hh', ← hh] using hdata.2.2.1
  have hstable : O ≤ h.left ⁻¹ᵁ O := by
    intro z hz
    change h.left z ∈ Set.range c
    exact (Set.ext_iff.mp hrange z).mpr hz
  obtain ⟨r, t, ht, hpower⟩ := tensor_generators D (A i) m hdata.1
  obtain ⟨e, hescalar, heφ⟩ := chart_sections D.k (A i ⊗[D.k₀] D.k)
    (D.geometricFiber X₀).left (D.geometricFiber X₀).hom c
    (geometric_chart_open_base D X₀ (A i) (j i)).2 h.left
    (tensorFrobenius D (A i) m).toRingHom hcomm hstable
  let t' (i : Fin r) := e (t i)
  let S := Subring.closure
    (Set.range (PowerMapLocalData.sectionStructure (D.geometricFiber X₀).hom O) ∪ Set.range t')
  have hall : (⊤ : Subring (A i ⊗[D.k₀] D.k)) ≤ S.comap e.toRingHom := by
    rw [← ht]
    apply Subring.closure_le.mpr
    rintro b (⟨a, rfl⟩ | ⟨v, rfl⟩)
    · change e (algebraMap D.k (A i ⊗[D.k₀] D.k) a) ∈ S
      rw [hescalar]
      exact Subring.subset_closure (.inl ⟨a, rfl⟩)
    · exact Subring.subset_closure (.inr ⟨v, rfl⟩)
  have htop : S = ⊤ := by
    apply eq_top_iff.mpr
    intro a _
    obtain ⟨b, rfl⟩ := e.surjective a
    exact hall trivial
  refine ⟨O, hO, hxi, hstable, r, t', htop, ?_⟩
  intro v
  change (h.left.appLE O O hstable).hom (e (t v)) = e (t v) ^ (D.p ^ (D.a * m))
  rw [heφ]
  change e ((tensorFrobenius D (A i) m) (t v)) = _
  rw [hpower, map_pow]
  rw [pow_mul, ← D.cardinality_eq]


private theorem residue_point_base (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (.of k)) (x : X) :
    X.fromSpecResidueField x ≫ p =
      Spec.map (CommRingCat.ofHom (residueStructure k X p x)) := by
  rw [← p.specMap_residueFieldAlgebraMap]
  congr 2
  rw [Scheme.Hom.residueFieldAlgebraMap, Scheme.Spec.algebraMap_residueFieldIso_inv_assoc,
    Scheme.residue_residueFieldMap]
  rfl

private theorem residue_structure_natural (k : Type u) [Field k] (X Y : Scheme.{u})
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (x : X) :
    (f.residueFieldMap x).hom.comp (residueStructure k Y pY (f x)) =
      residueStructure k X pX x := by
  suffices h : CommRingCat.ofHom ((f.residueFieldMap x).hom.comp
      (residueStructure k Y pY (f x))) =
        CommRingCat.ofHom (residueStructure k X pX x) from
    congrArg CommRingCat.Hom.hom h
  apply Spec.map_inj.mp
  rw [CommRingCat.ofHom_comp, Spec.map_comp, ← residue_point_base, ← Category.assoc]
  change (Spec.map (f.residueFieldMap x) ≫ Y.fromSpecResidueField (f x)) ≫ pY = _
  rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, Category.assoc, hf,
    residue_point_base]

set_option maxHeartbeats 2000000 in
-- The dependent tangent-map value and residue-field coefficient transport need extra elaboration.
private theorem tangent_map_value_at (k : Type u) [Field k] (X Y : Scheme.{u})
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (x : X) (y : Y) (hxy : f x = y)
    (he : Function.Bijective (f.residueFieldMap x).hom)
    (hr : Function.Bijective (residueStructure k X pX x)) :
    ∀ v, (Eq.mp (congrArg (schemeTangentSpace k Y pY) hxy)
        (schemeTangentMap k X Y pX pY f hf x he v)).val =
      Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom
        ((residueStructure k Y pY y).comp
          (RingEquiv.ofBijective (residueStructure k X pX x) hr).symm.toRingHom))) ≫
        v.val ≫ f := by
  subst y
  let e := RingEquiv.ofBijective (f.residueFieldMap x).hom he
  let eX := RingEquiv.ofBijective (residueStructure k X pX x) hr
  have hinv : e.symm.toRingHom = (residueStructure k Y pY (f x)).comp eX.symm.toRingHom := by
    apply RingHom.ext
    intro a
    apply e.injective
    change e (e.symm a) = e (residueStructure k Y pY (f x) (eX.symm a))
    rw [e.apply_symm_apply]
    change a = (f.residueFieldMap x).hom
      (residueStructure k Y pY (f x) (eX.symm a))
    rw [← RingHom.comp_apply, residue_structure_natural k X Y pX pY f hf x]
    exact (eX.apply_symm_apply a).symm
  intro v
  change (schemeTangentMap k X Y pX pY f hf x he v).val = _
  calc
    _ = Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom e.symm.toRingHom)) ≫
        v.val ≫ f :=
      Classical.choose_spec (exists_tangentMap_linear k X Y pX pY f hf x he) v
    _ = _ := by rw [hinv]

private theorem restrict_rational_equiv
    (k R S : Type u) [Field k] [Field R] [Field S]
    (T V : Type u) [AddCommGroup T] [Module R T] [AddCommGroup V] [Module S V]
    (f : k →+* R) (q : k →+* S) (hf : Function.Bijective f)
    (E : letI := Module.compHom T f
      let := Module.compHom V q
      T ≃ₗ[k] (V × V)) :
    let a := q.comp (RingEquiv.ofBijective f hf).symm.toRingHom
    let := Module.compHom V a
    ∃ E' : T ≃ₗ[R] (V × V), ∀ w, E' w = E w := by
  let := Module.compHom T f
  let := Module.compHom V q
  let a := q.comp (RingEquiv.ofBijective f hf).symm.toRingHom
  let := Module.compHom V a
  refine ⟨{ E.toAddEquiv with map_smul' := ?_ }, fun _ ↦ rfl⟩
  intro b v
  obtain ⟨c, rfl⟩ := hf.2 b
  have ha : a (f c) = q c := by
    change q ((RingEquiv.ofBijective f hf).symm ((RingEquiv.ofBijective f hf) c)) = q c
    rw [RingEquiv.symm_apply_apply]
  change E (f c • v) = (a (f c) • (E v).1, a (f c) • (E v).2)
  rw [ha]
  exact E.map_smul c v

private theorem span_inverse_graph
    (K : Type u) [Field K] (W V : Type u)
    [AddCommGroup W] [Module K W] [AddCommGroup V] [Module K V]
    (E : W ≃ₗ[K] (V × V)) (L : V →ₗ[K] V) (f : V → W)
    (hf : ∀ v, f v = E.symm (v, L v)) :
    Submodule.span K (Set.range f) = L.graph.comap E.toLinearMap := by
  have hrange : Set.range f = (L.graph.comap E.toLinearMap : Set W) := by
    ext w
    constructor
    · rintro ⟨v, rfl⟩
      change (E (f v)).2 = L (E (f v)).1
      rw [hf, E.apply_symm_apply]
    · intro hw
      change (E w).2 = L (E w).1 at hw
      refine ⟨(E w).1, ?_⟩
      apply E.injective
      rw [hf, E.apply_symm_apply]
      exact Prod.ext rfl hw.symm
  rw [hrange, Submodule.span_eq]

set_option maxHeartbeats 2000000 in
-- Elaborating the dependent product tangent and stalk transports exceeds the default budget.
/-- The tangent comparison and regular local rings needed for the
intersection calculation. This does not assert any Tor statement or construct the
fixed-scheme decomposition. The caller supplies its fixed rational section, structural stalk map
and graph/diagonal
point and residue-map identities.

Source: latest blueprint, `thm-trf-frobenius-fixed-points.proof.md`, Step 3;
`lem-trf-power-map-smooth-graph-local-data`
(blueprint: lem-trf-frobenius-fixed-tangent-local-geometry).

Proof:
1. Use the stable affine charts from the Frobenius presentation theorem. Choose model
   polynomial generators; after extension to k these generate the geometric chart over k.
   On them the endomorphism is t_i ↦ t_i^(q^m), with q^m = p^(a*m) and a*m ≥ 1.
2. The given rational section r of the fixed scheme, composed with the fixed inclusion,
   is a fixed rational section of X by the defining graph/diagonal pullback. Its given
   closed-point equality identifies its underlying point with x = i(z). The equalizer
   property supplies its fixed identity without any residue-field choice.
3. Apply powerMap_smooth_graph_local_data using the chart coordinates of step 1 and this
   rational section. Its zero differential and product tangent equivalence have graph
   image (v,0) and diagonal image (v,v). The specified value formula for schemeTangentMap
   agrees with the lemma's formulas, because the structural residue maps are bijective.
   Transport the diagonal along hx; spanning over the ambient residue field changes
   neither image. Restrict the k-linear comparison along the inverse ambient structural
   residue isomorphism to obtain the ambient-residue-field linear equivalence E.
   Its inverse image of the horizontal graph is G and of the identity graph is Δ.
   These are the two asserted submodule equalities; complementarity is proved by the caller.
4. For a smooth open U, the structural-stalk hypothesis at this same fixed point supplies
   the lemma's fixed-stalk bijectivity hypothesis. Its smooth product open immersion has
   image W containing the graph point; smoothness transports to W. Its graph and diagonal
   kernel quotients are regular local of dimension d; the ambient stalk has dimension
   2d, and their sum is its maximal ideal. Transport the common product point and stalks
   to the graph point. The transported diagonal stalk map is exactly the stalkCongr
   composite in the conclusion, so these are the prescribed ideals, not chosen ones.
   All transports use equality of the actual points and proof irrelevance. The case d=0
   uses the same regular-local statements, with no positive-dimension assumption. -/
theorem frobenius_fixed_tangent_local_geometry (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (m : ℕ) (hm : 1 ≤ m) (h : D.geometricFiber X₀ ⟶ D.geometricFiber X₀)
    (hh : h.left = D.schemeFrobeniusIterate X₀ m)
    (z : trfEndomorphismFixedScheme (D.geometricFiber X₀) h)
    (r : Spec (.of D.k) ⟶ trfEndomorphismFixedScheme (D.geometricFiber X₀) h)
    (hrs : r ≫ (trfEndomorphismFixedInclusion (D.geometricFiber X₀) h ≫
      (D.geometricFiber X₀).hom) = 𝟙 _)
    (hrz : r (IsLocalRing.closedPoint D.k) = z)
    (hF : Function.Bijective (StructureSheaf.toStalk D.k
      ((trfEndomorphismFixedInclusion (D.geometricFiber X₀) h ≫
        (D.geometricFiber X₀).hom) z) ≫
      (trfEndomorphismFixedInclusion (D.geometricFiber X₀) h ≫
        (D.geometricFiber X₀).hom).stalkMap z).hom)
    (U : (D.geometricFiber X₀).left.Opens)
    (hz : trfEndomorphismFixedInclusion (D.geometricFiber X₀) h z ∈ U)
    (hU : Smooth (U.ι ≫ (D.geometricFiber X₀).hom))
    (hx : pullback.diagonal (D.geometricFiber X₀).hom
        (trfEndomorphismFixedInclusion (D.geometricFiber X₀) h z) =
      trfFixedGraphMap (D.geometricFiber X₀) h
        (trfEndomorphismFixedInclusion (D.geometricFiber X₀) h z))
    (heG : Function.Bijective ((trfFixedGraphMap (D.geometricFiber X₀) h).residueFieldMap
      (trfEndomorphismFixedInclusion (D.geometricFiber X₀) h z)).hom)
    (heΔ : Function.Bijective ((pullback.diagonal (D.geometricFiber X₀).hom).residueFieldMap
      (trfEndomorphismFixedInclusion (D.geometricFiber X₀) h z)).hom) :
    let X := D.geometricFiber X₀
    let x' := trfEndomorphismFixedInclusion X h z
    let P := pullback X.hom X.hom
    let pP := pullback.fst X.hom X.hom ≫ X.hom
    let g := trfFixedGraphMap X h
    let δ := pullback.diagonal X.hom
      let tG := schemeTangentMap D.k X.left P X.hom pP g
        (by
          dsimp [g, pP, trfFixedGraphMap]
          rw [← Category.assoc, pullback.lift_fst]
          exact Category.id_comp _) x' heG
      let tΔ := schemeTangentMap D.k X.left P X.hom pP δ
        (by
          dsimp [δ, pP]
          rw [← Category.assoc, pullback.diagonal_fst]
          exact Category.id_comp _) x' heΔ
      let G := Submodule.span (P.residueField (g x')) (Set.range tG)
      let Δ := Submodule.span (P.residueField (g x'))
        ((fun v ↦ Eq.mp (congrArg (schemeTangentSpace D.k P pP) hx) v) '' Set.range tΔ)
      let A := P.presheaf.stalk (g x')
      let I := RingHom.ker (g.stalkMap x').hom
      let J := RingHom.ker
        ((P.presheaf.stalkCongr (by rw [hx]; exact Inseparable.rfl)).hom ≫ δ.stalkMap x').hom
      (∃ W : P.Opens, g x' ∈ W ∧ Smooth (W.ι ≫ pP)) ∧
      (∃ (V : Type u) (vAdd : AddCommGroup V),
        letI := vAdd
        ∃ vModule : Module (P.residueField (g x')) V,
          letI := vModule
          ∃ E : schemeTangentSpace D.k P pP (g x') ≃ₗ[P.residueField (g x')] (V × V),
            G = (0 : V →ₗ[P.residueField (g x')] V).graph.comap E.toLinearMap ∧
            Δ = (LinearMap.id : V →ₗ[P.residueField (g x')] V).graph.comap E.toLinearMap) ∧
      ∃ d : ℕ, IsRegularLocalRing A ∧ IsRegularLocalRing (A ⧸ I) ∧
        IsRegularLocalRing (A ⧸ J) ∧
        ringKrullDim A = (2 * d : ℕ) ∧
        ringKrullDim (A ⧸ I) = (d : ℕ) ∧
        ringKrullDim (A ⧸ J) = (d : ℕ) ∧
        I ⊔ J = IsLocalRing.maximalIdeal A := by
  classical
  let X := D.geometricFiber X₀
  let : LocallyOfFiniteType X.hom := by
    change LocallyOfFiniteType (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    infer_instance
  let : QuasiCompact X.hom := by
    change QuasiCompact (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    infer_instance
  let i := trfEndomorphismFixedInclusion X h
  let x : Spec (.of D.k) ⟶ X.left := r ≫ i
  have xs : x ≫ X.hom = 𝟙 _ := by
    simpa only [x, i, Category.assoc] using hrs
  have xh : x ≫ h.left = x :=
    (trfEndomorphismFixedScheme_equalizer X h (Spec (.of D.k)) x).1 r
  have hxz : x (IsLocalRing.closedPoint D.k) = i z := by
    change i (r (IsLocalRing.closedPoint D.k)) = i z
    rw [hrz]
  have hLift : fixedLift X.hom h.left (Over.w h) x xh = r := by
    obtain ⟨l, hl, hu⟩ :=
      (trfEndomorphismFixedScheme_equalizer X h (Spec (.of D.k)) x).2.mpr xh
    have h1 : fixedLift X.hom h.left (Over.w h) x xh ≫ i = x :=
      pullback.lift_fst _ _ _
    exact (hu _ h1).trans (hu r rfl).symm
  have hfixed : fixedPoint X.hom h.left (Over.w h) x xh = z := by
    change fixedLift X.hom h.left (Over.w h) x xh (IsLocalRing.closedPoint D.k) = z
    rw [hLift]
    exact hrz
  have hfixedStalk : Function.Bijective
      (stalkStructure D.k (fixedScheme X.hom h.left (Over.w h))
        (fixedStructure X.hom h.left (Over.w h))
        (fixedPoint X.hom h.left (Over.w h) x xh)) := by
    rw [hfixed]
    exact hF
  have hk : (D.p : D.k) = 0 := by
    simpa only [map_natCast, map_zero] using
      congrArg (Scheme.ΓSpecIso (.of D.k)).hom.hom
        (D.model_characteristic (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
  let : CharP D.k D.p := (CharP.charP_iff_prime_eq_zero D.prime).mpr hk
  obtain ⟨O, hO, hxO, hstable, rgen, t, ht, hpower⟩ :=
    exists_stable_power_chart D X₀ m hm h hh (x (IsLocalRing.closedPoint D.k))
  have H := powerMap_smooth_graph_local_data D.k D.p D.prime X.left X.hom
    h.left (Over.w h) x xs xh O hO hxO hstable rgen t ht (D.a * m)
      (by have := Nat.mul_le_mul D.exponent_pos hm; simpa using this) hpower
  have hgraph : graph X.hom h.left (Over.w h) = trfFixedGraphMap X h := by
    rfl
  simp only [hgraph] at H
  rw [hxz] at H
  generalize hproduct : productPoint X.hom x = w at H
  clear hproduct
  obtain ⟨hr, hg, hd, differential, hdiff, hdiffzero, hdiffid, E,
    hE1, hE2, hEg, hEd, hinter, hspan, hregular⟩ := H
  cases hg
  have hregular' := hregular U hz hU hfixedStalk
  obtain ⟨d, hdX, hdT, W, V, hWV, hVU, hxW, hW, hV, hWh, hsm,
    hWmap, hWmap_eq, gW, dW, hgf, hgs, hdf, hds, hgc, hdc,
    mP, hmf, hms, hmP, hxP, I, J, hI, hJ, hA, hRI, hRJ,
    hrP, hrI, hrJ, hdim, hIdim, hJdim, hIJ, hrest⟩ := hregular'
  have hI' : I = RingHom.ker ((trfFixedGraphMap X h).stalkMap (i z)).hom := by
    simpa [stalkMapAt] using hI
  have hJ' : J = RingHom.ker
      (((pullback X.hom X.hom).presheaf.stalkCongr
        (by rw [hx]; exact Inseparable.rfl)).hom ≫
        (pullback.diagonal X.hom).stalkMap (i z)).hom := by
    simpa only [stalkMapAt, TopCat.Presheaf.stalkCongr_inv,
      TopCat.Presheaf.stalkCongr_hom] using hJ
  clear hI hJ hrI hrJ hrest
  subst I
  subst J
  dsimp only
  refine ⟨?_, ?_, d, hA, hRI, hRJ, ?_, hIdim, hJdim, hIJ⟩
  · let : IsOpenImmersion mP := hmP
    let O' := mP.opensRange
    have hrange : Set.range mP = Set.range O'.ι := by
      rw [Scheme.Opens.range_ι]
      rfl
    let e := IsOpenImmersion.isoOfRangeEq mP O'.ι hrange
    have he : e.inv ≫ mP = O'.ι :=
      IsOpenImmersion.isoOfRangeEq_inv_fac mP O'.ι hrange
    have hsm' : Smooth (mP ≫ (pullback.fst X.hom X.hom ≫ X.hom)) := by
      rw [← Category.assoc, hmf, Category.assoc]
      exact hsm
    let := hsm'
    have hsm'' : Smooth (e.inv ≫ (mP ≫ (pullback.fst X.hom X.hom ≫ X.hom))) :=
      inferInstance
    refine ⟨O', hxP, ?_⟩
    simpa only [← Category.assoc, he] using hsm''
  · let P := pullback X.hom X.hom
    let pP := pullback.fst X.hom X.hom ≫ X.hom
    let y := trfFixedGraphMap X h (i z)
    let T := schemeTangentSpace D.k X.left X.hom (i z)
    let f := residueStructure D.k P pP y
    let q := residueStructure D.k X.left X.hom (i z)
    let a := q.comp (RingEquiv.ofBijective f hrP).symm.toRingHom
    let : Module (P.residueField y) T := Module.compHom T a
    obtain ⟨Eκ, hEκ⟩ := restrict_rational_equiv D.k (P.residueField y)
      (X.left.residueField (i z)) (schemeTangentSpace D.k P pP y) T f q hrP E
    have hEsymm (v : T × T) : Eκ.symm v = E.symm v := by
      apply Eκ.injective
      rw [Eκ.apply_symm_apply, hEκ, E.apply_symm_apply]
    refine ⟨T, inferInstance, inferInstance, Eκ, ?_, ?_⟩
    · apply span_inverse_graph _ _ _ Eκ (0 : T →ₗ[P.residueField y] T)
      intro v
      apply Subtype.ext
      rw [hEsymm]
      exact (tangent_map_value_at D.k X.left P X.hom pP (trfFixedGraphMap X h)
        (by
          dsimp [pP, trfFixedGraphMap]
          rw [← Category.assoc, pullback.lift_fst]
          exact Category.id_comp _) (i z) y rfl heG hr v).trans (hEg v).symm
    · have himage :
          ((fun v ↦ Eq.mp (congrArg (schemeTangentSpace D.k P pP) hx) v) ''
            Set.range (schemeTangentMap D.k X.left P X.hom pP (pullback.diagonal X.hom)
              (by
                dsimp [pP]
                rw [← Category.assoc, pullback.diagonal_fst]
                exact Category.id_comp _) (i z) heΔ)) =
          Set.range (fun v : T ↦ Eq.mp (congrArg (schemeTangentSpace D.k P pP) hx)
            (schemeTangentMap D.k X.left P X.hom pP (pullback.diagonal X.hom)
              (by
                dsimp [pP]
                rw [← Category.assoc, pullback.diagonal_fst]
                exact Category.id_comp _) (i z) heΔ v)) := (Set.range_comp _ _).symm
      rw [himage]
      apply span_inverse_graph _ _ _ Eκ (LinearMap.id : T →ₗ[P.residueField y] T)
      intro v
      apply Subtype.ext
      rw [hEsymm]
      exact (tangent_map_value_at D.k X.left P X.hom pP (pullback.diagonal X.hom)
        (by
          dsimp [pP]
          rw [← Category.assoc, pullback.diagonal_fst]
          exact Category.id_comp _) (i z) y hx heΔ hr v).trans (hEd v).symm
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hdim

end WeilConjectures
