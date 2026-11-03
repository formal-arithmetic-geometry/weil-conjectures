/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.SchemeFrobenius
public import WeilConjectures.SmoothPurity.TraceFixedScheme
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import Mathlib.RingTheory.Length
public import Mathlib.CategoryTheory.Monoidal.Tor
import WeilConjectures.TraceFormula.FrobeniusEvaluationAtlas
import WeilConjectures.AlgebraicGeometry.AbelianVariety.FrobeniusFixedTangentLocalGeometry
import WeilConjectures.AlgebraicGeometry.EqualizerPointChartDescent
import WeilConjectures.RingTheory.RegularLocalComplementaryQuotientsTor
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import WeilConjectures.AlgebraicGeometry.AbsoluteFrobeniusNatural
import WeilConjectures.PointCount
import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusFactorization
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
public import WeilConjectures.Compactification.FiniteFieldDatum.TraceFormulaSchemeFrobeniusGeometry
public import WeilConjectures.TraceFormula.FixedSchemeGeometry

/-!
# Frobenius fixed points

Source: Weil conjectures blueprint, `thm-trf-frobenius-fixed-points` (blueprint:
thm-trf-frobenius-fixed-points).

The theorem states the scheme-theoretic fixed-point decomposition, its finite étale and
local properties, the tangent differential, and the smooth-locus transverse intersection
and Tor multiplicity clauses.  The fixed scheme is the recorded equalizer construction.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures

open scoped TensorProduct
open FiniteFieldDatum.FrobeniusAffineEqualizer
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


private theorem exists_evaluation_atlas (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (m : ℕ) (hm : 1 ≤ m) (h : D.geometricFiber X₀ ⟶ D.geometricFiber X₀)
    (hh : h.left = D.coefficientFreeSchemeFrobeniusIterate X₀ m)
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
  simpa only [hh', ← hh] using hc

private theorem exists_extension_point_family (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (m : ℕ) (hm : 1 ≤ m) :
    ∃ x : D.extensionPoints X₀ m hm → (Spec (.of D.k) ⟶ (D.geometricFiber X₀).left),
      (∀ y, x y ≫ (D.geometricFiber X₀).hom = 𝟙 _) ∧
      ∀ y, x y ≫ pullback.fst X₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
        Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype) ≫ y.left := by
  have hbase : (D.extensionSubfield m hm).subtype.comp (D.extensionEmbedding m hm) =
      algebraMap D.k₀ D.k :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.2.2.2.2.2.choose_spec
  have hc (y : D.extensionPoints X₀ m hm) :
      (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype) ≫ y.left) ≫
        X₀.hom = (𝟙 (Spec (.of D.k))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
    rw [Category.assoc, Over.w y, Category.id_comp]
    change Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype) ≫
      Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hbase]
  refine ⟨fun y ↦ pullback.lift
    (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype) ≫ y.left)
      (𝟙 _) (hc y), ?_, ?_⟩
  · intro y
    exact pullback.lift_snd _ _ _
  · intro y
    exact pullback.lift_fst _ _ _

private theorem pow_intertwine {C : Type u} [Category C] {X Y : C}
    (P : End X) (Q : End Y) (f : X ⟶ Y) (hf : P ≫ f = f ≫ Q) (n : ℕ) :
    (P ^ n) ≫ f = f ≫ Q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    change (P ≫ (P ^ n)) ≫ f = f ≫ Q ≫ Q ^ n
    rw [Category.assoc, ih, ← Category.assoc, hf, Category.assoc]

private theorem absolute_mul (X : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (a m : ℕ) :
    X.iterateFrobenius hp hX (a * m) =
      (End.of (X.iterateFrobenius hp hX a)) ^ m := by
  induction m with
  | zero => simp [Scheme.iterateFrobenius_zero, End.one_def]
  | succ m ih =>
    rw [Nat.mul_succ, Scheme.iterateFrobenius_add, ih, pow_succ, End.mul_def]
    exact (Commute.self_pow (End.of (X.iterateFrobenius hp hX a)) m).eq

private theorem extension_point_family_fixed (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (m : ℕ) (hm : 1 ≤ m)
    (x : D.extensionPoints X₀ m hm → (Spec (.of D.k) ⟶ (D.geometricFiber X₀).left))
    (hxp : ∀ y, x y ≫ pullback.fst X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype) ≫ y.left) :
    ∀ y, x y ≫ D.coefficientFreeSchemeFrobeniusIterate X₀ m = x y := by
  let X := D.geometricFiber X₀
  let π := pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  let P : End X.left := D.coefficientFreeSchemeFrobenius X₀
  let Q : End X₀.left := X₀.left.iterateFrobenius D.prime (D.model_characteristic X₀.hom) D.a
  have hP : P ≫ π = π ≫ Q := (D.relativeFrobenius_projections X₀).1
  have hQ : Q ^ m = X₀.left.iterateFrobenius D.prime
      (D.model_characteristic X₀.hom) (D.a * m) :=
    (absolute_mul X₀.left D.p D.prime (D.model_characteristic X₀.hom) D.a m).symm
  have hπ : D.coefficientFreeSchemeFrobeniusIterate X₀ m ≫ π = π ≫
      X₀.left.iterateFrobenius D.prime (D.model_characteristic X₀.hom) (D.a * m) := by
    change (P ^ m) ≫ π = _
    rw [pow_intertwine P Q π hP, hQ]
  have hs : D.coefficientFreeSchemeFrobeniusIterate X₀ m ≫ X.hom = X.hom := by
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
  · change (x y ≫ D.coefficientFreeSchemeFrobeniusIterate X₀ m) ≫ π = x y ≫ π
    rw [Category.assoc, hπ, ← Category.assoc, hxp, Category.assoc, hy]
  · change (x y ≫ D.coefficientFreeSchemeFrobeniusIterate X₀ m) ≫ X.hom = x y ≫ X.hom
    rw [Category.assoc, hs]

private theorem stalk_iso_of_global_structure (k : Type u) [Field k] (F : Scheme.{u})
    (s : F ⟶ Spec (.of k)) (z : F)
    (hs : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ s.appTop ≫ F.presheaf.Γgerm z)) :
    ∃ e : F.presheaf.stalk z ≅ CommRingCat.of k,
      (StructureSheaf.toStalk k (s z) ≫ s.stalkMap z) ≫ e.hom = 𝟙 _ := by
  have heq : StructureSheaf.toStalk k (s z) ≫ s.stalkMap z =
      (Scheme.ΓSpecIso (.of k)).inv ≫ s.appTop ≫ F.presheaf.Γgerm z := by
    change (Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec (.of k)).presheaf.germ ⊤ (s z) trivial ≫ s.stalkMap z = _
    rw [s.germ_stalkMap]
    rfl
  have : IsIso (StructureSheaf.toStalk k (s z) ≫ s.stalkMap z) := heq.symm ▸ hs
  exact ⟨(asIso (StructureSheaf.toStalk k (s z) ≫ s.stalkMap z)).symm,
    IsIso.hom_inv_id _⟩

private theorem tangent_map_zero_of_constant_postcomposition
    (k : Type u) [Field k] (X Y : Scheme.{u})
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (x : X)
    (he : Function.Bijective (f.residueFieldMap x).hom)
    (hpost : ∀ v : schemeTangentSpace k X pX x,
      v.val ≫ f = Spec.map (CommRingCat.ofHom
        (TrivSqZeroExt.inlHom (X.residueField x) (X.residueField x))) ≫
          X.fromSpecResidueField x ≫ f) :
    schemeTangentMap k X Y pX pY f hf x he = 0 := by
  let e := RingEquiv.ofBijective (f.residueFieldMap x).hom he
  let a : Spec (Y.residueField (f x)) ⟶ Spec (X.residueField x) :=
    Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  let d : Spec (.of (DualNumber (Y.residueField (f x)))) ⟶
      Spec (.of (DualNumber (X.residueField x))) :=
    Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom e.symm.toRingHom))
  let qX : Spec (.of (DualNumber (X.residueField x))) ⟶ Spec (X.residueField x) :=
    Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.inlHom (X.residueField x) (X.residueField x)))
  let qY : Spec (.of (DualNumber (Y.residueField (f x)))) ⟶ Spec (Y.residueField (f x)) :=
    Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.inlHom (Y.residueField (f x)) (Y.residueField (f x))))
  have hab : a ≫ X.fromSpecResidueField x ≫ f = Y.fromSpecResidueField (f x) := by
    rw [← f.SpecMap_residueFieldMap_fromSpecResidueField x, ← Spec.map_comp_assoc]
    have hi : f.residueFieldMap x ≫ CommRingCat.ofHom e.symm.toRingHom =
        𝟙 (Y.residueField (f x)) := by
      ext z
      exact e.symm_apply_apply z
    rw [hi, Spec.map_id, Category.id_comp]
  have hdq : d ≫ qX = qY ≫ a := by
    dsimp [d, qX, qY, a]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    change DualNumber.mapRingHom e.symm.toRingHom (TrivSqZeroExt.inl z) =
      TrivSqZeroExt.inl (e.symm z)
    apply TrivSqZeroExt.ext <;> simp
  have hzero : (0 : schemeTangentSpace k Y pY (f x)).val =
      qY ≫ Y.fromSpecResidueField (f x) :=
    (Classical.choose_spec
      (Classical.choose_spec (exists_tangentVectors_vectorSpace k Y pY (f x)).2.2.2)).1
  let : Module (X.residueField x) (schemeTangentSpace k Y pY (f x)) :=
    Module.compHom (schemeTangentSpace k Y pY (f x)) e.symm.toRingHom
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change (schemeTangentMap k X Y pX pY f hf x he v).val =
    (0 : schemeTangentSpace k Y pY (f x)).val
  rw [show (schemeTangentMap k X Y pX pY f hf x he v).val = d ≫ v.val ≫ f from
    Classical.choose_spec (exists_tangentMap_linear k X Y pX pY f hf x he) v]
  rw [hpost v, hzero]
  change d ≫ qX ≫ X.fromSpecResidueField x ≫ f = qY ≫ Y.fromSpecResidueField (f x)
  rw [← Category.assoc d qX, hdq]
  simpa only [Category.assoc] using congrArg (fun g ↦ qY ≫ g) hab

private theorem absolute_postcomposition
    (k : Type u) [Field k] (X : Scheme.{u}) (s : X ⟶ Spec (.of k))
    (p n : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (hn : 0 < n)
    (x : X) (v : schemeTangentSpace k X s x) :
    v.val ≫ X.iterateFrobenius hp hX n =
      Spec.map (CommRingCat.ofHom
        (TrivSqZeroExt.inlHom (X.residueField x) (X.residueField x))) ≫
          X.fromSpecResidueField x ≫ X.iterateFrobenius hp hX n := by
  let K := X.residueField x
  let R := DualNumber K
  have hK : (p : K) = 0 := by
    simpa only [map_natCast, map_zero] using
      congrArg (X.presheaf.Γgerm x ≫ X.residue x).hom hX
  have hR : (p : R) = 0 := by
    change (p : DualNumber K) = 0
    apply TrivSqZeroExt.ext <;> simp only [TrivSqZeroExt.fst_natCast,
      TrivSqZeroExt.snd_natCast, TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_zero, hK]
  let φK : K →+* K := iterateFrobeniusOfPrime K hp hK n
  let φR : R →+* R := iterateFrobeniusOfPrime R hp hR n
  have hφ : φR = (TrivSqZeroExt.inlHom K K).comp
      (φK.comp (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    apply RingHom.ext
    intro z
    change z ^ (p ^ n) = TrivSqZeroExt.inl (z.fst ^ (p ^ n))
    apply TrivSqZeroExt.ext
    · exact TrivSqZeroExt.fst_pow (z : DualNumber K) (p ^ n)
    · change (z ^ (p ^ n)).snd = 0
      exact (TrivSqZeroExt.snd_pow (z : DualNumber K) (p ^ n)).trans (by
        rw [nsmul_eq_mul, Nat.cast_pow, hK, zero_pow (Nat.ne_of_gt hn), zero_mul])
  have hv := Scheme.isFrobenius_iterateFrobenius hp X hX n v.val
    (CommRingCat.ofHom φR) (fun r ↦ rfl)
  have hx := Scheme.isFrobenius_iterateFrobenius hp X hX n
    (X.fromSpecResidueField x) (CommRingCat.ofHom φK) (fun r ↦ rfl)
  rw [hv, hφ, CommRingCat.ofHom_comp, Spec.map_comp,
    CommRingCat.ofHom_comp, Spec.map_comp]
  simp only [Category.assoc]
  rw [v.property.1, hx]

private theorem frobenius_postcomposition (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (m : ℕ) (hm : 1 ≤ m) (h : D.geometricFiber X₀ ⟶ D.geometricFiber X₀)
    (hh : h.left = D.coefficientFreeSchemeFrobeniusIterate X₀ m)
    (x : (D.geometricFiber X₀).left)
    (v : schemeTangentSpace D.k (D.geometricFiber X₀).left (D.geometricFiber X₀).hom x) :
    v.val ≫ h.left = Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.inlHom ((D.geometricFiber X₀).left.residueField x)
        ((D.geometricFiber X₀).left.residueField x))) ≫
          (D.geometricFiber X₀).left.fromSpecResidueField x ≫ h.left := by
  let X := D.geometricFiber X₀
  let S : End X.left := (D.geometricFrobenius X₀).inv
  have hS : IsIso S := by
    dsimp [S]
    infer_instance
  have : IsIso (S ^ m) :=
    (isUnit_iff_isIso _).mp (((isUnit_iff_isIso S).mpr hS).pow m)
  apply (cancel_mono (S ^ m)).mp
  have hp := absolute_postcomposition D.k X.left X.hom D.p (D.a * m)
    D.prime (D.model_characteristic
      (pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ X₀.hom))
      (Nat.mul_pos D.exponent_pos (by omega)) x v
  rw [(D.absoluteFrobenius_factorization X₀ m hm).1] at hp
  simpa only [hh, Category.assoc] using hp

private theorem section_residue_bijective {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hf : f ≫ g = 𝟙 X) (x : X) : Function.Bijective (f.residueFieldMap x).hom := by
  have : SurjectiveOnStalks (f ≫ g) := by rw [hf]; infer_instance
  let : SurjectiveOnStalks f := SurjectiveOnStalks.of_comp f g
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  intro b
  obtain ⟨a, ha⟩ := X.residue_surjective x b
  obtain ⟨c, hc⟩ := f.stalkMap_surjective x a
  refine ⟨Y.residue (f x) c, ?_⟩
  change (Y.residue (f x) ≫ f.residueFieldMap x) c = b
  rw [Scheme.residue_residueFieldMap f x]
  change X.residue x (f.stalkMap x c) = b
  rw [hc, ha]

private theorem fixed_graph_diagonal_point {D : FiniteFieldDatum.{u}}
    (X : Over (Spec (.of D.k))) (h : X ⟶ X)
    (z : geometricEndomorphismFixedScheme X h) :
    pullback.diagonal X.hom (geometricEndomorphismFixedInclusion X h z) =
      geometricFixedGraphMap X h (geometricEndomorphismFixedInclusion X h z) := by
  let i := geometricEndomorphismFixedInclusion X h
  let d := pullback.snd (geometricFixedGraphMap X h) (pullback.diagonal X.hom)
  have hid : i = d := by
    have hc := congrArg (fun f ↦ f ≫ pullback.fst X.hom X.hom)
      (pullback.condition (f := geometricFixedGraphMap X h) (g := pullback.diagonal X.hom))
    simpa [i, d, geometricEndomorphismFixedInclusion, geometricFixedGraphMap, Category.assoc]
      using hc
  have hc : i ≫ geometricFixedGraphMap X h = i ≫ pullback.diagonal X.hom := by
    calc
      i ≫ geometricFixedGraphMap X h = d ≫ pullback.diagonal X.hom := pullback.condition
      _ = i ≫ pullback.diagonal X.hom := by rw [hid]
  exact (congrArg
    (fun f : geometricEndomorphismFixedScheme X h ⟶ pullback X.hom X.hom ↦ f z) hc).symm

private theorem graph_diagonal_residue_bijective {D : FiniteFieldDatum.{u}}
    (X : Over (Spec (.of D.k))) (h : X ⟶ X) (x : X.left) :
    Function.Bijective ((geometricFixedGraphMap X h).residueFieldMap x).hom ∧
    Function.Bijective ((pullback.diagonal X.hom).residueFieldMap x).hom := by
  constructor
  · exact section_residue_bijective (geometricFixedGraphMap X h) (pullback.fst X.hom X.hom)
      (by simp [geometricFixedGraphMap]) x
  · exact section_residue_bijective (pullback.diagonal X.hom) (pullback.fst X.hom X.hom)
      (by simp) x

private theorem complementary_graphs (K : Type u) [Field K] (V W : Type u)
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (E : W ≃ₗ[K] (V × V)) (G Δ : Submodule K W)
    (hG : G = (0 : V →ₗ[K] V).graph.comap E.toLinearMap)
    (hΔ : Δ = (LinearMap.id : V →ₗ[K] V).graph.comap E.toLinearMap) :
    G ⊔ Δ = ⊤ ∧ G ⊓ Δ = ⊥ := by
  constructor
  · apply top_unique
    intro w _
    let a := (E w).1
    let b := (E w).2
    have hg : E.symm (a - b, 0) ∈ G := by
      rw [hG]
      change E (E.symm (a - b, 0)) ∈ (0 : V →ₗ[K] V).graph
      simp only [LinearEquiv.apply_symm_apply, LinearMap.mem_graph_iff,
        LinearMap.zero_apply]
    have hd : E.symm (b, b) ∈ Δ := by
      rw [hΔ]
      change E (E.symm (b, b)) ∈ (LinearMap.id : V →ₗ[K] V).graph
      simp only [LinearEquiv.apply_symm_apply, LinearMap.mem_graph_iff,
        LinearMap.id_apply]
    have hw : w = E.symm (a - b, 0) + E.symm (b, b) := by
      apply E.injective
      simp only [map_add, LinearEquiv.apply_symm_apply]
      exact Prod.ext (by dsimp [a, b]; simp) (by dsimp [b]; simp)
    rw [hw]
    exact Submodule.add_mem_sup hg hd
  · apply le_antisymm ?_ bot_le
    intro w hw
    have hg : (E w).2 = 0 := by
      have := hw.1
      rw [hG] at this
      change E w ∈ (0 : V →ₗ[K] V).graph at this
      simpa only [LinearMap.mem_graph_iff, LinearMap.zero_apply] using this
    have hd : (E w).2 = (E w).1 := by
      have := hw.2
      rw [hΔ] at this
      change E w ∈ (LinearMap.id : V →ₗ[K] V).graph at this
      simpa only [LinearMap.mem_graph_iff, LinearMap.id_apply] using this
    change w = 0
    apply E.injective
    rw [map_zero]
    exact Prod.ext (hd.symm.trans hg) hg

private theorem section_of_stalk_bijection (k : Type u) [Field k] (F : Scheme.{u})
    (s : F ⟶ Spec (.of k)) (z : F)
    (hs : Function.Bijective (StructureSheaf.toStalk k (s z) ≫ s.stalkMap z).hom) :
    ∃ r : Spec (.of k) ⟶ F, r ≫ s = 𝟙 _ ∧ r (IsLocalRing.closedPoint k) = z := by
  let b : k →+* F.residueField z :=
    (StructureSheaf.toStalk k (s z) ≫ s.stalkMap z ≫ F.residue z).hom
  have hb : Function.Bijective b :=
    ⟨b.injective, IsLocalRing.residue_surjective.comp hs.surjective⟩
  let e := RingEquiv.ofBijective b hb
  have hbase : F.fromSpecResidueField z ≫ s = Spec.map (CommRingCat.ofHom b) := by
    rw [← s.specMap_residueFieldAlgebraMap]
    congr 2
    rw [Scheme.Hom.residueFieldAlgebraMap, Scheme.Spec.algebraMap_residueFieldIso_inv_assoc,
      Scheme.residue_residueFieldMap]
    rfl
  refine ⟨Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ F.fromSpecResidueField z, ?_, ?_⟩
  · rw [Category.assoc, hbase, ← Spec.map_comp]
    have he : CommRingCat.ofHom b ≫ CommRingCat.ofHom e.symm.toRingHom = 𝟙 (CommRingCat.of k) := by
      ext c
      exact e.symm_apply_apply c
    rw [he, Spec.map_id]
  · change F.fromSpecResidueField z _ = z
    exact F.fromSpecResidueField_apply z _

private theorem complementary_quotients_tor (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (d : ℕ) (I J : Ideal A) (hI : I ≠ ⊤) (hJ : J ≠ ⊤)
    [IsRegularLocalRing (A ⧸ I)] [IsRegularLocalRing (A ⧸ J)]
    (hdim : ringKrullDim A = (2 * d : ℕ))
    (hIdim : ringKrullDim (A ⧸ I) = (d : ℕ))
    (hJdim : ringKrullDim (A ⧸ J) = (d : ℕ))
    (htrans : I ⊔ J = IsLocalRing.maximalIdeal A) :
    Module.length A (((Tor' (ModuleCat A) 0).obj
      (ModuleCat.of A (A ⧸ I))).obj (ModuleCat.of A (A ⧸ J))) = 1 ∧
    ∀ i : ℕ, 0 < i → IsZero (((Tor' (ModuleCat A) i).obj
      (ModuleCat.of A (A ⧸ I))).obj (ModuleCat.of A (A ⧸ J))) := by
  obtain ⟨f, g, hfg, hparam, hspan, hreg, hregJ, hfree, hbound, haug,
    htensor, hdelta, hres, hvanish, hequiv, hfinite, hsum⟩ :=
    RingTheory.regularLocal_complementary_quotients_tor A d d
      (by simpa only [two_mul] using hdim) I J hI hJ hIdim hJdim htrans
  obtain ⟨eTensor, eTor, hmul, hcompare⟩ := hequiv
  refine ⟨?_, hvanish⟩
  rw [eTor.toLinearEquiv.length_eq]
  rw [Module.length_eq_of_surjective (R := IsLocalRing.ResidueField A)
    (S := A) (M := IsLocalRing.ResidueField A) IsLocalRing.residue_surjective]
  exact Module.length_eq_one _ _

-- Preserve the original statement, whose inline zero-iterate proof binds an unused hm.
set_option linter.unusedVariables false in
set_option maxHeartbeats 2000000 in
-- Elaborating the dependent graph, tangent and stalk transports exceeds the default budget.
/-- Scheme-theoretic fixed points of iterated scheme Frobenius over a finite field.

Source: latest blueprint, `sec-smooth-purity`,
`sk-cor-sp-all-coefficients/thm-trf-frobenius-fixed-points.proof.md`, Steps 0--3;
the DAG's nine expanded proof steps, especially the smooth-locus qualification in steps 8--9;
Stacks Project, Tag 0B1I, `intersection-lemma-transversal`
(blueprint: thm-trf-frobenius-fixed-points).

Proof (the numbered steps are those of the node):
1. Construct the extension-point family x_y by the pullback universal property and the
   unique-subfield embedding compatibility. Each x_y is fixed: relative Frobenius
   commutes with the model projection, its m-th iterate lies over the (a*m)-th absolute
   Frobenius of X₀, which fixes every E-point since c^(q^m)=c on E; pullback uniqueness.
2. From lem-trf-frobenius-affine-equalizer-presentation take a finite stable model affine
   cover. Its scalar-extended charts are open immersions covering X. Present each chart
   algebra as k₀[t]/a, extract the normalized quotient isomorphism ν, check its
   k-linearity at f=1, and apply frobenius_chart_evaluation
   (lem-trf-frobenius-evaluation-atlas) chart by chart: this is the descent atlas.
3. equalizer_point_chart_descent on that atlas gives the canonical coproduct isomorphism
   (inverse of its point map q), the two summand formulas by composing with both
   fibre-product projections, finiteness, étaleness, the structural stalk isomorphisms
   and length one.
4. The differential clause holds at every topologically fixed point with bijective
   residue map: in residue-field dual numbers the p^(a*m)-power map kills epsilon, so by
   absolute Frobenius naturality v;Frob is constant; the absolute/relative/arithmetic
   factorization (prop-trf-frobenius-factorization) and cancelling the arithmetic
   automorphism transfer this to h; the value formula of schemeTangentMap gives 0.
5. At a fixed-scheme point z the stalk bijection k≃O_{F,z} gives a rational section r
   through z. The graph and diagonal are sections of pr₁, hence their point equality hx
   and residue bijections heG, heΔ. frobenius_fixed_tangent_local_geometry
   (lem-trf-frobenius-fixed-tangent-local-geometry) at a smooth U gives the smooth open
   W, the tangent comparison E with G=E⁻¹(graph 0), Δ=E⁻¹(graph id), and the regular
   local rings A, A/I, A/J of dimensions 2d, d, d with I+J the maximal ideal.
   Complementarity: (a,b)=(a-b,0)+(b,b), and the meet is zero by comparing coordinates.
6. regularLocal_complementary_quotients_tor with r=s=d gives Tor_i=0 for i>0 and
   Tor₀≅κ(A); its A-length is one by restriction along the surjective residue map.
   The alternating Serre length sum is therefore one. Empty point sets and d=0 included.

The two tangent ranges are spanned over the ambient residue field, after transporting
along hx. This is exactly their range subspace: schemeTangentMap is linear over the
source residue field and heG/heΔ identify it isomorphically with the ambient one.
The witnesses hx, heG and heΔ assert canonical point equality and residue bijections;
they do not allow choices of tangent subspaces or ideals. -/
theorem frobenius_fixed_points
    (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (m : ℕ) (hm : 1 ≤ m) :
    let X := D.geometricFiber X₀
    let h : X ⟶ X :=
      Over.homMk (D.coefficientFreeSchemeFrobeniusIterate X₀ m) (by
        revert hm
        induction m with
        | zero => intro hm; simp [FiniteFieldDatum.coefficientFreeSchemeFrobeniusIterate, X]
        | succ m ih =>
          intro hm
          cases m with
          | zero =>
            simpa [FiniteFieldDatum.coefficientFreeSchemeFrobeniusIterate,
              FiniteFieldDatum.coefficientFreeSchemeFrobenius, X] using
              (FiniteFieldDatum.relativeFrobenius_projections D X₀).2
          | succ m =>
            let Φ : End X.left := D.coefficientFreeSchemeFrobenius X₀
            have ih' : (Φ ^ (Nat.succ m)) ≫ X.hom = X.hom := by
              simpa [FiniteFieldDatum.coefficientFreeSchemeFrobeniusIterate, Φ] using ih (by omega)
            have hΦ : Φ ≫ X.hom = X.hom := by
              simpa [Φ, X, FiniteFieldDatum.coefficientFreeSchemeFrobenius] using
                (FiniteFieldDatum.relativeFrobenius_projections D X₀).2
            change (Φ ^ (Nat.succ (Nat.succ m))) ≫ X.hom = X.hom
            rw [pow_succ]
            simp [Category.assoc, ih', hΦ])
    let F := geometricEndomorphismFixedScheme X h
    ∃ e : F ≅ ∐ fun _ : D.extensionPoints X₀ m hm => Spec (.of D.k),
      (Finite (D.extensionPoints X₀ m hm) ∧
        IsFinite (geometricEndomorphismFixedInclusion X h ≫ X.hom) ∧
        Etale (geometricEndomorphismFixedInclusion X h ≫ X.hom)) ∧
      (∀ y : D.extensionPoints X₀ m hm,
        (Sigma.ι (fun _ : D.extensionPoints X₀ m hm => Spec (.of D.k)) y ≫
            e.inv ≫ geometricEndomorphismFixedInclusion X h ≫ X.hom = 𝟙 (Spec (.of D.k))) ∧
        (Sigma.ι (fun _ : D.extensionPoints X₀ m hm => Spec (.of D.k)) y ≫
            e.inv ≫ geometricEndomorphismFixedInclusion X h ≫
            pullback.fst X₀.hom
              (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
          Scheme.Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype).op ≫ y.left)) ∧
      (∀ z : F,
        ∃ e₀ : F.presheaf.stalk z ≅ CommRingCat.of D.k,
          (StructureSheaf.toStalk D.k ((geometricEndomorphismFixedInclusion X h ≫ X.hom) z) ≫
            (geometricEndomorphismFixedInclusion X h ≫ X.hom).stalkMap z) ≫ e₀.hom =
              𝟙 (CommRingCat.of D.k) ∧
          Module.length (F.presheaf.stalk z) (F.presheaf.stalk z) = 1) ∧
      (∀ x : X.left, h.left x = x →
        ∀ he : Function.Bijective (h.left.residueFieldMap x).hom,
          AlgebraicGeometry.schemeTangentMap D.k X.left X.left X.hom X.hom h.left
            (by exact Over.w h) x he = 0) ∧
      (∀ (x : F) (U : X.left.Opens),
        geometricEndomorphismFixedInclusion X h x ∈ U → Smooth (U.ι ≫ X.hom) →
        let x' := geometricEndomorphismFixedInclusion X h x
        let P := pullback X.hom X.hom
        let pP := pullback.fst X.hom X.hom ≫ X.hom
        let g := geometricFixedGraphMap X h
        let δ := pullback.diagonal X.hom
        ∃ (hx : δ x' = g x')
          (heG : Function.Bijective (g.residueFieldMap x').hom)
          (heΔ : Function.Bijective (δ.residueFieldMap x').hom),
          let tG := schemeTangentMap D.k X.left P X.hom pP g
            (by
              dsimp [g, pP, geometricFixedGraphMap]
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
          G ⊔ Δ = ⊤ ∧ G ⊓ Δ = ⊥ ∧
          Module.length A
            (((CategoryTheory.Tor' (ModuleCat A) 0).obj
              (ModuleCat.of A (A ⧸ I))).obj (ModuleCat.of A (A ⧸ J))) = 1 ∧
          ∀ i : ℕ, 0 < i →
            IsZero (((CategoryTheory.Tor' (ModuleCat A) i).obj
              (ModuleCat.of A (A ⧸ I))).obj (ModuleCat.of A (A ⧸ J)))) := by
  classical
  dsimp only
  let X := D.geometricFiber X₀
  let h : X ⟶ X :=
    Over.homMk (D.coefficientFreeSchemeFrobeniusIterate X₀ m) (by
      revert hm
      induction m with
      | zero => intro hm; simp [FiniteFieldDatum.coefficientFreeSchemeFrobeniusIterate, X]
      | succ m ih =>
        intro hm
        cases m with
        | zero =>
          simpa [FiniteFieldDatum.coefficientFreeSchemeFrobeniusIterate,
            FiniteFieldDatum.coefficientFreeSchemeFrobenius, X] using
            (FiniteFieldDatum.relativeFrobenius_projections D X₀).2
        | succ m =>
          let Φ : End X.left := D.coefficientFreeSchemeFrobenius X₀
          have ih' : (Φ ^ (Nat.succ m)) ≫ X.hom = X.hom := by
            simpa [FiniteFieldDatum.coefficientFreeSchemeFrobeniusIterate, Φ] using ih (by omega)
          have hΦ : Φ ≫ X.hom = X.hom := by
            simpa [Φ, X, FiniteFieldDatum.coefficientFreeSchemeFrobenius] using
              (FiniteFieldDatum.relativeFrobenius_projections D X₀).2
          change (Φ ^ (Nat.succ (Nat.succ m))) ≫ X.hom = X.hom
          rw [pow_succ]
          simp [Category.assoc, ih', hΦ])
  change ∃ e : geometricEndomorphismFixedScheme X h ≅ _, _
  obtain ⟨x, hxs, hxp⟩ := exists_extension_point_family D X₀ m hm
  have hfixed : ∀ y, x y ≫ h.left = x y :=
    extension_point_family_fixed D X₀ m hm x hxp
  obtain ⟨atlas⟩ := exists_evaluation_atlas D X₀ m hm h rfl x hxs hxp
  have (j : Fin atlas.n) : IsOpenImmersion (atlas.c j) := atlas.openImmersion j
  have (j : Fin atlas.n) : Finite (atlas.Pj j) := atlas.finiteLabels j
  obtain ⟨hfinite, q, hq, _hunique, hqiso, _hcharts, hfin, het, hstalk⟩ :=
    equalizer_point_chart_descent D.k X.left X.hom h.left (Over.w h)
      (geometricFixedGraphMap X h)
      (by simp [geometricFixedGraphMap]) (by simp [geometricFixedGraphMap])
      (Fin atlas.n) (fun j ↦ atlas.B j) atlas.c atlas.covers atlas.overBase
      atlas.φ atlas.commutes atlas.I atlas.differenceIdeal
      (D.extensionPoints X₀ m hm) x hxs hfixed atlas.Pj atlas.labels
      atlas.ε atlas.evaluation
  have : IsIso q := hqiso
  let e := (asIso q).symm
  have hstalk' (z : geometricEndomorphismFixedScheme X h) :
      ∃ e₀ : (geometricEndomorphismFixedScheme X h).presheaf.stalk z ≅ CommRingCat.of D.k,
        (StructureSheaf.toStalk D.k
          ((geometricEndomorphismFixedInclusion X h ≫ X.hom) z) ≫
          (geometricEndomorphismFixedInclusion X h ≫ X.hom).stalkMap z) ≫ e₀.hom = 𝟙 _ :=
    stalk_iso_of_global_structure D.k _ _ z (hstalk z).1
  have hbij (z : geometricEndomorphismFixedScheme X h) :
      Function.Bijective (StructureSheaf.toStalk D.k
        ((geometricEndomorphismFixedInclusion X h ≫ X.hom) z) ≫
        (geometricEndomorphismFixedInclusion X h ≫ X.hom).stalkMap z).hom := by
    obtain ⟨e₀, he₀⟩ := hstalk' z
    have heq : StructureSheaf.toStalk D.k
        ((geometricEndomorphismFixedInclusion X h ≫ X.hom) z) ≫
        (geometricEndomorphismFixedInclusion X h ≫ X.hom).stalkMap z = e₀.inv := by
      rw [← cancel_mono e₀.hom, he₀, e₀.inv_hom_id]
    rw [heq]
    exact ConcreteCategory.bijective_of_isIso e₀.inv
  have hzero (x : X.left) (_hx : h.left x = x)
      (he : Function.Bijective (h.left.residueFieldMap x).hom) :
      schemeTangentMap D.k X.left X.left X.hom X.hom h.left (Over.w h) x he = 0 :=
    tangent_map_zero_of_constant_postcomposition D.k X.left X.left X.hom X.hom
      h.left (Over.w h) x he
        (fun v ↦ frobenius_postcomposition D X₀ m hm h rfl x v)
  refine ⟨e, ⟨hfinite, hfin, het⟩, ?_, ?_, hzero, ?_⟩
  · intro y
    constructor
    · simpa only [e, Iso.symm_inv, asIso_hom, geometricEndomorphismFixedInclusion,
        Scheme.Spec_map, Quiver.Hom.unop_op, Category.assoc] using
        (congrArg (fun f ↦ f ≫ X.hom) (hq y)).trans (hxs y)
    · change Sigma.ι (fun _ : D.extensionPoints X₀ m hm ↦ Spec (.of D.k)) y ≫
        e.inv ≫ geometricEndomorphismFixedInclusion X h ≫
          pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
            Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype) ≫ y.left
      simpa only [e, Iso.symm_inv, asIso_hom, geometricEndomorphismFixedInclusion,
        Category.assoc] using
        (congrArg (fun f ↦ f ≫ pullback.fst X₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) (hq y)).trans (hxp y)
  · intro z
    obtain ⟨e₀, he₀⟩ := hstalk' z
    exact ⟨e₀, he₀, (hstalk z).2⟩
  · intro z U hz hU
    obtain ⟨r, hrs, hrz⟩ := section_of_stalk_bijection D.k
      (geometricEndomorphismFixedScheme X h)
      (geometricEndomorphismFixedInclusion X h ≫ X.hom) z (hbij z)
    have hx := fixed_graph_diagonal_point (D := D) X h z
    obtain ⟨heG, heΔ⟩ := graph_diagonal_residue_bijective (D := D) X h
      (geometricEndomorphismFixedInclusion X h z)
    have hlocal := frobenius_fixed_tangent_local_geometry D X₀ m hm h rfl
      z r hrs hrz (hbij z) U hz hU hx heG heΔ
    obtain ⟨hW, hcomparison, d, hA, hI, hJ, hdim, hIdim, hJdim, hIJ⟩ := hlocal
    obtain ⟨V, vAdd, hcomparison⟩ := hcomparison
    let := vAdd
    obtain ⟨vModule, E, hG, hΔ⟩ := hcomparison
    let := vModule
    obtain ⟨hsup, hinf⟩ := complementary_graphs _ _ _ E _ _ hG hΔ
    refine ⟨hx, heG, heΔ, hW, hsup, hinf, ?_⟩
    have := hA
    have := hI
    have := hJ
    exact complementary_quotients_tor _ d _ _
      (Ideal.Quotient.nontrivial_iff.mp inferInstance)
      (Ideal.Quotient.nontrivial_iff.mp inferInstance) hdim hIdim hJdim hIJ

end WeilConjectures
