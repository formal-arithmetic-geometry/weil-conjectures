/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed

/-!
# Henselian rings and strictly henselian local rings via sections of étale algebras

The zero ideal of any commutative ring is henselian (`HenselianRing.bot`).

A local ring `R` such that every étale `R`-algebra `B` has, through every prime of `B` over the
closed point, an `R`-algebra section `B →ₐ[R] R`, is henselian with separably closed residue
field. Both statements are tested on standard étale algebras `R[X][1/f']/(f)` for a monic `f`:
a section sends `X` to a root of `f`.

## Main results

- `HenselianRing.bot`: the zero ideal of any ring is henselian.
- `HenselianLocalRing.of_exists_algHom_comap_maximalIdeal_eq`: such a local ring is henselian.
- `IsLocalRing.isSepClosed_residueField_of_exists_algHom_comap_maximalIdeal_eq`: such a local
  ring has separably closed residue field.

The henselian pairs `(A, I)` of the blueprint (`def-weil-pbc-henselian-terminology`) are
Mathlib's `HenselianRing A I`; a henselian local ring is `HenselianLocalRing`, and it is
strictly henselian when moreover `IsSepClosed (IsLocalRing.ResidueField A)`.
-/

@[expose] public section

/-- The zero ideal of any ring is henselian. -/
instance HenselianRing.bot (R : Type*) [CommRing R] : HenselianRing R ⊥ where
  jac := bot_le
  is_henselian f _ a₀ h _ := ⟨a₀, by simpa using h, by simp⟩

universe u

open Polynomial IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Let `R` be a local ring such that every prime of an étale `R`-algebra lying over the maximal
ideal is the preimage of the maximal ideal under an `R`-algebra map to `R`. If `K` is a field
over `R` whose structure map has kernel the maximal ideal, then every simple root `x : K` of a
monic `f : R[X]` is the image of a root of `f` in `R`. -/
theorem IsLocalRing.exists_isRoot_algebraMap_eq_of_exists_algHom_comap_maximalIdeal_eq
    (H : ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra.Etale R B] (q : Ideal B) [q.IsPrime],
      q.comap (algebraMap R B) = maximalIdeal R →
        ∃ ψ : B →ₐ[R] R, (maximalIdeal R).comap ψ = q)
    {K : Type*} [Field K] [Algebra R K] (hK : RingHom.ker (algebraMap R K) = maximalIdeal R)
    {f : R[X]} (hf : f.Monic) {x : K} (hx : aeval x f = 0) (hx' : aeval x (derivative f) ≠ 0) :
    ∃ a : R, f.IsRoot a ∧ algebraMap R K a = x := by
  let P := StandardEtalePair.ofMonic hf 1
  have hP : P.HasMap x := ⟨hx, by simpa [P, StandardEtalePair.ofMonic] using hx'⟩
  let χ := P.lift x hP
  have hq : (RingHom.ker χ).comap (algebraMap R P.Ring) = maximalIdeal R := by
    ext r
    rw [← hK, Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, AlgHom.commutes]
  have := RingHom.ker_isPrime χ
  obtain ⟨ψ, hψ⟩ := H P.Ring (RingHom.ker χ) hq
  refine ⟨ψ P.X, ?_, ?_⟩
  · have h := congr_arg ψ (StandardEtalePair.hasMap_X (P := P)).1
    rwa [← aeval_algHom_apply, map_zero, aeval_def, Algebra.algebraMap_self, eval₂_id] at h
  · have hmem : P.X - algebraMap R P.Ring (ψ P.X) ∈ (maximalIdeal R).comap ψ := by
      simp [Ideal.mem_comap]
    rw [hψ, RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at hmem
    rw [← hmem]
    exact P.lift_X x hP

/-- A local ring `R` is henselian if every prime `q` lying over the maximal ideal of an étale
`R`-algebra `B` is the preimage of the maximal ideal under an `R`-algebra map `B →ₐ[R] R`. -/
theorem HenselianLocalRing.of_exists_algHom_comap_maximalIdeal_eq
    (H : ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra.Etale R B] (q : Ideal B) [q.IsPrime],
      q.comap (algebraMap R B) = maximalIdeal R →
        ∃ ψ : B →ₐ[R] R, (maximalIdeal R).comap ψ = q) :
    HenselianLocalRing R := by
  refine ((HenselianLocalRing.TFAE R).out 1 0).mp fun f hf a₀ h₁ h₂ ↦ ?_
  have hK : RingHom.ker (algebraMap R (ResidueField R)) = maximalIdeal R := by
    rw [ResidueField.algebraMap_eq, ker_residue]
  simpa [ResidueField.algebraMap_eq] using
    exists_isRoot_algebraMap_eq_of_exists_algHom_comap_maximalIdeal_eq H hK hf h₁ h₂

/-- A local ring `R` has separably closed residue field if every prime `q` lying over the
maximal ideal of an étale `R`-algebra `B` is the preimage of the maximal ideal under an
`R`-algebra map `B →ₐ[R] R`. -/
theorem IsLocalRing.isSepClosed_residueField_of_exists_algHom_comap_maximalIdeal_eq
    (H : ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra.Etale R B] (q : Ideal B) [q.IsPrime],
      q.comap (algebraMap R B) = maximalIdeal R →
        ∃ ψ : B →ₐ[R] R, (maximalIdeal R).comap ψ = q) :
    IsSepClosed (ResidueField R) := by
  refine IsSepClosed.of_exists_root _ fun h hm hirr hsep ↦ ?_
  obtain ⟨f, rfl, -, hf⟩ := lifts_and_natDegree_eq_and_monic
    (map_surjective _ residue_surjective h) hm
  have := Fact.mk hirr
  have hK : RingHom.ker (algebraMap R (AdjoinRoot (f.map (residue R)))) = maximalIdeal R := by
    ext r
    rw [← ker_residue, RingHom.mem_ker, RingHom.mem_ker,
      IsScalarTower.algebraMap_apply R (ResidueField R),
      map_eq_zero, ResidueField.algebraMap_eq]
  have hroot₀ : aeval (AdjoinRoot.root (f.map (residue R))) (f.map (residue R)) = 0 :=
    AdjoinRoot.aeval_eq _ |>.trans AdjoinRoot.mk_self
  have hroot : aeval (AdjoinRoot.root (f.map (residue R))) f = 0 := by
    rw [← aeval_map_algebraMap (ResidueField R), ResidueField.algebraMap_eq]
    exact hroot₀
  have hroot' : aeval (AdjoinRoot.root (f.map (residue R))) (derivative f) ≠ 0 := by
    rw [← aeval_map_algebraMap (ResidueField R), ResidueField.algebraMap_eq, ← derivative_map]
    exact hsep.aeval_derivative_ne_zero hroot₀
  obtain ⟨a, ha, -⟩ := exists_isRoot_algebraMap_eq_of_exists_algHom_comap_maximalIdeal_eq H hK hf
    hroot hroot'
  exact ⟨residue R a, by simpa using congr(residue R $ha)⟩

/-! ### Ported from the `proetale` package (`Proetale.Mathlib.RingTheory.Henselian`) -/

-- Rename `HenselianRing` to `IsHenselianRing`, ``HenselianLocalRing` to `IsHenselianLocalRing`.

class IsStrictlyHenselianLocalRing (R : Type*) [CommRing R] : Prop
    extends HenselianLocalRing R where
  isSepClosed_residueField : IsSepClosed (IsLocalRing.ResidueField R)

instance (R : Type*) [CommRing R] [IsStrictlyHenselianLocalRing R] :
    IsSepClosed (IsLocalRing.ResidueField R) :=
  IsStrictlyHenselianLocalRing.isSepClosed_residueField

/-- A local ring is strictly Henselian if and only if it is Henselian and its residue
field is separably closed. -/
theorem isStrictlyHenselianLocalRing_iff_henselianLocalRing_and_isSepClosed
    (R : Type*) [CommRing R] [IsLocalRing R] :
    IsStrictlyHenselianLocalRing R ↔
      HenselianLocalRing R ∧ IsSepClosed (IsLocalRing.ResidueField R) :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩,
    fun h ↦ have := h.1; ⟨h.2⟩⟩

/-- `HenselianLocalRing` transfers along a ring isomorphism. -/
theorem HenselianLocalRing.of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [HenselianLocalRing R] (e : R ≃+* S) : HenselianLocalRing S := by
  have : IsLocalRing S := e.isLocalRing
  refine HenselianLocalRing.mk fun f hf a₀ hmem hunit => ?_
  let f' : Polynomial R := f.map e.symm.toRingHom
  have heval : f'.eval (e.symm a₀) = e.symm (f.eval a₀) :=
    Polynomial.eval_map_apply (p := f) e.symm.toRingHom a₀
  have hderiv : f'.derivative.eval (e.symm a₀) = e.symm (f.derivative.eval a₀) := by
    rw [Polynomial.derivative_map (f := e.symm.toRingHom)]
    exact Polynomial.eval_map_apply (p := f.derivative) e.symm.toRingHom a₀
  have hmem' : f'.eval (e.symm a₀) ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal] at hmem
    rw [heval, IsLocalRing.mem_maximalIdeal]
    intro hu
    exact hmem (by simpa using hu.map e)
  have hunit' : IsUnit (f'.derivative.eval (e.symm a₀)) :=
    hderiv ▸ hunit.map e.symm.toRingHom
  obtain ⟨a, ha_root, ha_diff⟩ :=
    HenselianLocalRing.is_henselian f' (hf.map _) (e.symm a₀) hmem' hunit'
  refine ⟨e a, ?_, ?_⟩
  · have hf_eq : f'.map e.toRingHom = f := by
      simp [f', Polynomial.map_map]
    have key : f.eval (e a) = e (f'.eval a) := by
      rw [← hf_eq]; exact Polynomial.eval_map_apply (p := f') e.toRingHom a
    rw [Polynomial.IsRoot.def, key, Polynomial.IsRoot.def.mp ha_root, map_zero]
  · rw [IsLocalRing.mem_maximalIdeal] at ha_diff ⊢
    intro hu
    apply ha_diff
    have : a - e.symm a₀ = e.symm (e a - a₀) := by simp
    rw [this]
    exact hu.map e.symm.toRingHom

/-- `IsStrictlyHenselianLocalRing` transfers along a ring isomorphism. -/
theorem IsStrictlyHenselianLocalRing.of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsStrictlyHenselianLocalRing R] (e : R ≃+* S) : IsStrictlyHenselianLocalRing S :=
  have : HenselianLocalRing S := .of_ringEquiv e
  ⟨IsSepClosed.of_ringEquiv (IsLocalRing.ResidueField.mapEquiv e)⟩

universe v

noncomputable section
open Polynomial
open MvPolynomial Ideal Quotient Algebra

variable {R : Type u} [CommRing R] (f : R[X])

-- f(X), f'(X)Y - 1
def idealJ (f : R[X]) : Ideal (MvPolynomial (Fin 2) R) :=
  (span (Set.range
    ![toMvPolynomial (0 : Fin 2) f, (toMvPolynomial (0 : Fin 2) f.derivative) * X 1 - 1]))

def S : Type u := MvPolynomial (Fin 2) R ⧸ (idealJ f)

instance : CommRing (S f) := by
  unfold S
  infer_instance

instance : Algebra R (S f) := by
  unfold S
  infer_instance

def presentationS : Presentation R (S f) (Fin 2) (Fin 2) := by
  let s : (S f) → (MvPolynomial (Fin 2) R) :=
    Function.surjInv (f := (Ideal.Quotient.mk (idealJ f))) Quotient.mk_surjective
  have hs (x : S f) : Ideal.Quotient.mk _ (s x) = x := by
    rw [Function.surjInv_eq (f := (Ideal.Quotient.mk (idealJ f)))]
  apply Presentation.naive s hs

def preSubmersivePresentationS : PreSubmersivePresentation R (S f) (Fin 2) (Fin 2) := {
  toPresentation := presentationS f
  map := id
  map_inj _ _ h := h
}

@[simp]
theorem pderiv_toMvPolynomial_eq_zero_of_ne (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    (pderiv i) ((toMvPolynomial j) f) = 0 := by
  induction f using Polynomial.induction_on with
  | C a => simp
  | add p q _ _ => simp_all
  | monomial n a _ => simp [Pi.single_eq_of_ne h.symm]

@[simp]
theorem pderiv_toMvPolynomial_eq_toMvPolynomial_pderiv (n : ℕ) (i : Fin n) :
    (pderiv i) ((toMvPolynomial i) f) = (toMvPolynomial i) f.derivative := by
  induction f using Polynomial.induction_on with
  | C a => simp
  | add p q _ _ => simp_all
  | monomial n a _ => simp

lemma preSubmersivePresentationS_jacobiMatrix_00 :
    (preSubmersivePresentationS f).jacobiMatrix 0 0 =
    (mk (idealJ f) (toMvPolynomial (0 : Fin 2) f.derivative)) := by
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  simp [preSubmersivePresentationS, presentationS]

lemma preSubmersivePresentationS_jacobiMatrix_11 :
    (preSubmersivePresentationS f).jacobiMatrix 1 1 =
    (mk (idealJ f) (toMvPolynomial (0 : Fin 2) f.derivative)) := by
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  simp [preSubmersivePresentationS, presentationS]

lemma preSubmersivePresentationS_jacobiMatrix_01 :
    (preSubmersivePresentationS f).jacobiMatrix 1 0 = 0 := by
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  simp [preSubmersivePresentationS, presentationS]

def submersivePresentationS (f : R[X]) : SubmersivePresentation R (S f) (Fin 2) (Fin 2) := {
  toPreSubmersivePresentation := preSubmersivePresentationS f
  jacobian_isUnit := by
    let f' := (mk (idealJ f) (toMvPolynomial (0 : Fin 2) f.derivative))
    have unit_f' : IsUnit f' := by
      apply IsUnit.of_mul_eq_one (mk (idealJ f) (X 1))
      rw [← map_mul, ← map_one (Ideal.Quotient.mk _), mk_eq_mk_iff_sub_mem]
      apply Ideal.subset_span
      simp
    have : (preSubmersivePresentationS f).jacobian = f' * f' := by
      rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
      rw [Matrix.det_fin_two]
      have (x : (MvPolynomial (Fin 2) R)) :
          (algebraMap (preSubmersivePresentationS f).Ring (S f)) x = mk (idealJ f) x := by rfl
      rw [this]
      simp only [Fin.isValue, map_sub, map_mul]
      rw [preSubmersivePresentationS_jacobiMatrix_00]
      rw [preSubmersivePresentationS_jacobiMatrix_11]
      rw [preSubmersivePresentationS_jacobiMatrix_01]
      simp [f']
    rw [this]
    simp [unit_f']
}

instance : IsStandardSmoothOfRelativeDimension 0 R (S f) := by
  unfold S
  constructor
  use (Fin 2), (Fin 2), inferInstance, inferInstance, (submersivePresentationS f)
  simp [Presentation.dimension]

theorem aeval_zero_of_mem_span {I : Ideal R} {f : R[X]} {a₀ : R}
    (e : Polynomial.eval a₀ f ∈ I)
    (u : IsUnit ((mk I) ((derivative f).eval a₀))) {a : MvPolynomial (Fin 2) R}
    (ha : a ∈ idealJ f) :
    (MvPolynomial.aeval
    ![(mk I) a₀, u.unit.inv]) a = 0 := by
  suffices hJ : idealJ f ≤ RingHom.ker (MvPolynomial.aeval ![(mk I) a₀, u.unit.inv]) by
    exact hJ ha
  simp only [idealJ, Nat.succ_eq_add_one, Nat.reduceAdd, span_le]
  intro a ha
  simp only [Fin.isValue, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.union_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  symm at ha
  cases ha with
  | inl ha =>
    rw [ha]
    simp only [SetLike.mem_coe, RingHom.mem_ker, aeval_toMvPolynomial,
      Matrix.cons_val_zero]
    rw [← Ideal.Quotient.algebraMap_eq, Polynomial.aeval_algebraMap_apply,
      Ideal.Quotient.algebraMap_eq]
    simp [Ideal.Quotient.eq_zero_iff_mem, e]
  | inr ha =>
    rw [ha]
    simp only [Fin.isValue, SetLike.mem_coe, RingHom.mem_ker, map_sub,
      map_mul, aeval_toMvPolynomial, Matrix.cons_val_zero, MvPolynomial.aeval_X,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, map_one]
    conv =>
      enter [1, 1, 1]
      rw [← Ideal.Quotient.algebraMap_eq, Polynomial.aeval_algebraMap_apply,
        Ideal.Quotient.algebraMap_eq]
    simp

def g {I : Ideal R} {f : R[X]} {a₀ : R} (e : Polynomial.eval a₀ f ∈ I)
    (u : IsUnit ((Ideal.Quotient.mk I) (Polynomial.eval a₀ (derivative f)))) : S f →ₐ[R] R ⧸ I :=
  Ideal.Quotient.liftₐ (idealJ f)
    (MvPolynomial.aeval ![(mk I) a₀, u.unit.inv])
    (fun _ ↦ aeval_zero_of_mem_span e u)

theorem henselian_if_exists_section (R : Type u)
    [CommRing R] (I : Ideal R) (hI : I ≤ Ring.jacobson R)
    (h : ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.Etale R S] (g : S →ₐ[R] R ⧸ I),
    ∃ σ : S →ₐ[R] R, (Ideal.Quotient.mk I).comp (σ : S →+* R) = g) :
    HenselianRing R I where
  jac := Ideal.jacobson_bot (R := R) ▸ hI
  is_henselian := by
    intro f monic a₀ e u
    obtain ⟨σ, hσ⟩ := h (S f) (g e u)
    use σ (mk _ (X 0))
    constructor
    · rw [IsRoot]
      suffices hs : Polynomial.aeval (mk (idealJ f) (X 0)) f = 0 by
        calc
          _ = aeval (σ ((Ideal.Quotient.mk (idealJ f)) (MvPolynomial.X 0))) f := rfl
          _ = σ (aeval ((Ideal.Quotient.mk (idealJ f)) (MvPolynomial.X 0)) f) :=
                Polynomial.aeval_algHom_apply _ _ _
          _ = 0 := by rw [hs]; simp
      suffices ht : Ideal.Quotient.mk (idealJ f) (Polynomial.aeval (X 0) f) = 0 by
        rw [← Ideal.Quotient.mkₐ_eq_mk R, Polynomial.aeval_algHom_apply,
          Ideal.Quotient.mkₐ_eq_mk R, ht]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      simp only [idealJ, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.range_cons,
        Matrix.range_empty, Set.union_empty, Set.union_singleton]
      suffices this : (Polynomial.aeval (MvPolynomial.X (0 : Fin 2))) f = (toMvPolynomial 0) f by
        rw [this]
        apply Ideal.subset_span
        simp
      rfl
    · suffices hq : (Ideal.Quotient.mk I) (σ ((Ideal.Quotient.mk (idealJ f)) (X 0)) - a₀) = 0 by
        apply Ideal.Quotient.eq_zero_iff_mem.mp hq
      calc
        _ = (Ideal.Quotient.mk I) (σ ((Ideal.Quotient.mk (idealJ f)) (X 0)))
              - (Ideal.Quotient.mk I) a₀ := by simp
        _ = ((Ideal.Quotient.mk I).comp σ.toRingHom) ((Ideal.Quotient.mk (idealJ f)) (X 0))
              - (Ideal.Quotient.mk I) a₀ := by simp
        _ = (g e u).toRingHom ((Ideal.Quotient.mk (idealJ f)) (X 0))
              - (Ideal.Quotient.mk I) a₀ := by simp [hσ]
        _ = 0 := by
          rw [sub_eq_zero, g]
          exact (Ideal.Quotient.lift_mk _ _ _).trans (by simp)

-- Success

open CategoryTheory CommAlgCat Limits

universe u₁ v₁ u₂ v₂ w

variable (Q : MorphismProperty CommRingCat) (R : CommRingCat.{u})

noncomputable
def CommRingCat.Under.inclusion :
    MorphismProperty.Under Q ⊤ R ⥤ CommAlgCat R :=
  MorphismProperty.Under.forget _ _ _ ⋙ (commAlgCatEquivUnder R).inverse

abbrev CategoryTheory.CommRingCat.Etale : MorphismProperty CommRingCat :=
  RingHom.toMorphismProperty RingHom.Etale

instance {C : Type*} [Category C] [HasColimits C] (X : C) : HasColimits (Under X) := by
  constructor
  intro J _
  constructor
  intro K
  constructor
  constructor
  refine ⟨?_, ?_⟩
  · exact WithInitial.coconeEquiv.inverse.obj (colimit.cocone _)
  · apply WithInitial.isColimitEquiv.toFun
    apply IsColimit.ofIsoColimit _ (WithInitial.coconeEquiv.counitIso.app _).symm
    exact colimit.isColimit (WithInitial.liftFromUnder.obj K)

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (S : C ⥤ D) (T : D)

instance foo [EssentiallySmall.{w} C] [∀ (X : C), Small.{w} (S.obj X ⟶ T)] :
    EssentiallySmall.{w} (CostructuredArrow S T) := by
  obtain ⟨C', _, ⟨e⟩⟩ := EssentiallySmall.equiv_smallCategory (C := C)
  let eq : CostructuredArrow (e.inverse ⋙ S) T ⥤ CostructuredArrow S T :=
    Comma.map (F₂ := 𝟭 _) (Functor.rightUnitor _).inv (𝟙 _)
  have : eq.IsEquivalence := Comma.isEquivalenceMap _ _
  let f (x : CostructuredArrow (e.inverse ⋙ S) T) : Σ (X : C'), (S.obj (e.inverse.obj X) ⟶ T) :=
    ⟨x.1, x.3⟩
  have : Function.Injective f := by
    intro ⟨x, ⟨⟨⟩⟩, x3⟩ ⟨y, ⟨⟨⟩⟩, y3⟩ h
    obtain rfl : x = y := congr($(h).1)
    congr
    exact congr($(h).2)
  have : Small.{w} (CostructuredArrow (e.inverse ⋙ S) T) := small_of_injective this
  have : LocallySmall.{w} (CostructuredArrow (e.inverse ⋙ S) T) := by
    constructor
    intro X Y
    exact small_of_injective ((CostructuredArrow.proj _ _).map_injective)
  have := essentiallySmall_of_small_of_locallySmall (CostructuredArrow (e.inverse ⋙ S) T)
  apply essentiallySmall_of_fully_faithful.{w} (eq.asEquivalence.inverse)

instance : EssentiallySmall.{u, u, u + 1} (CommRingCat.Etale.Under ⊤ R) := by
  apply essentiallySmall_of_le
  intro X Y f hf
  exact .of_finitePresentation hf.2

instance (R : Type u) [CommRing R] :
    (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R)).HasPointwiseLeftKanExtension
    (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R)) := by
  dsimp [Functor.HasPointwiseLeftKanExtension]
  rintro _
  dsimp [Functor.HasPointwiseLeftKanExtensionAt]
  apply (config := {allowSynthFailures := true}) Limits.HasColimitsOfShape.has_colimit
  apply hasColimitsOfShape_of_essentiallySmall

def henselizationFunctor (R : Type u) [CommRing R] :
    (CommAlgCat R) ⥤ CommAlgCat R :=
  (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R)).leftKanExtension
    (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R))

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

def Henselization : Type u := (henselizationFunctor R).obj (of R S)

instance : CommRing (Henselization R S) := by
  unfold Henselization
  infer_instance

instance : Algebra R (Henselization R S) := by
  unfold Henselization
  infer_instance

def henselization_isom_colim : CommAlgCat.of R (Henselization R S) ≅
    Limits.colimit ((CostructuredArrow.proj (CommRingCat.Under.inclusion
    CommRingCat.Etale (CommRingCat.of R)) (CommAlgCat.of R S)).comp (CommRingCat.Under.inclusion
    CommRingCat.Etale (CommRingCat.of R))) :=
  CategoryTheory.Functor.leftKanExtensionObjIsoColimit _ _ _
