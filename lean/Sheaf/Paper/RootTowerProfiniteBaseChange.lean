/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FullParameterRootTower
public import Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Full root towers under ring and profinite base change

Source: main-20261015, direct-image proof (3), agent-extracted full-root input;
Stacks 01I4, 097D, 094U, 01SH and the explicit seven-step proof in the DAG
(blueprint: lem-sfb-root-tower-profinite-base-change).

The maps are induced on the existing compatible-root quotient presentations.
The isomorphisms below are specified by their coefficient, root and projection
equations. Principal opens are compared as schemes with their restricted sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped TensorProduct
open AlgebraicGeometry.Scheme.UniversalCover

namespace AlgebraicGeometry.ProEtale

private theorem fullRoot_hom_ext {J R C : Type u} [Fintype J] [CommRing R] [CommRing C]
    (p : ℕ) (t : J → R) {f g : FullParameterRootAlgebra p t →+* C}
    (hc : ∀ r, f (algebraMap R _ r) = g (algebraMap R _ r))
    (hx : ∀ n i, f (fullParameterRoot p t n i) = g (fullParameterRoot p t n i)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · exact hc
  · rintro ⟨i, n⟩
    simpa only [fullParameterRoot, Equiv.apply_symm_apply, RingHom.comp_apply] using
      hx n ((Fintype.equivFin J).symm i)

/-- Coefficient change carries every defining root relation to a defining relation.
Source: DAG proof step 1, polynomial evaluation and quotient universal property
(blueprint: lem-sfb-root-tower-profinite-base-change).

Proof: map each power relation using f(t i)=t' i. The divisibility relations have
integer exponents and coefficient 1, so coefficient change preserves them. Apply
the span universal property to obtain the asserted inclusion of ideals. -/
theorem fullRootRelations_map {J R S : Type u} [Fintype J] [CommRing R] [CommRing S]
    (p : ℕ) (t : J → R) (t' : J → S) (f : R →+* S) (ht : ∀ i, f (t i) = t' i) :
    Ideal.span (tameRootRelations p (fun i ↦ t ((Fintype.equivFin J).symm i))) ≤
      (Ideal.span (tameRootRelations p (fun i ↦ t' ((Fintype.equivFin J).symm i)))).comap
        (MvPolynomial.map f) := by
  apply Ideal.span_le.mpr
  intro a ha
  apply Ideal.subset_span
  rcases ha with ⟨i, n, rfl⟩ | ⟨i, n, m, hnm, rfl⟩
  · left
    exact ⟨i, n, by simp [ht]⟩
  · right
    exact ⟨i, n, m, hnm, by simp⟩

/-- Coefficient change on the actual full-root algebra, preserving each root label.
Source: DAG proof steps 1 and 2, quotient of coefficient change on polynomials
(blueprint: lem-sfb-root-tower-profinite-base-change). -/
def fullRootFamilyMap {J R S : Type u} [Fintype J] [CommRing R] [CommRing S]
    (p : ℕ) (t : J → R) (t' : J → S) (f : R →+* S) (ht : ∀ i, f (t i) = t' i) :
    FullParameterRootAlgebra p t →+* FullParameterRootAlgebra p t' :=
  Ideal.quotientMap _ (MvPolynomial.map f) (fullRootRelations_map p t t' f ht)

/-- The arbitrary ring-base-change specialization of the coefficient map.
Source: DAG proof step 2 (blueprint: lem-sfb-root-tower-profinite-base-change). -/
def fullRootBaseMap {J R S : Type u} [Fintype J] [CommRing R] [CommRing S]
    (p : ℕ) (t : J → R) (f : R →+* S) :
    FullParameterRootAlgebra p t →+* FullParameterRootAlgebra p (fun i ↦ f (t i)) :=
  fullRootFamilyMap p t (fun i ↦ f (t i)) f (fun _ ↦ rfl)

/-- Coefficients and labelled roots characterize the coefficient-change map.
Source: DAG proof steps 1 and 2 (blueprint: lem-sfb-root-tower-profinite-base-change).

Proof: quotient evaluation sends C(r) to C(f(r)) and each X(i,n) to itself.
Surjectivity of the quotient and polynomial induction give uniqueness. -/
theorem fullRootFamilyMap_normalization
    {J R S : Type u} [Fintype J] [CommRing R] [CommRing S]
    (p : ℕ) (t : J → R) (t' : J → S) (f : R →+* S) (ht : ∀ i, f (t i) = t' i) :
    (∀ a : R, fullRootFamilyMap p t t' f ht (algebraMap R _ a) =
      algebraMap S _ (f a)) ∧
    (∀ (n : TameRootOrder p) (i : J),
      fullRootFamilyMap p t t' f ht (fullParameterRoot p t n i) =
        fullParameterRoot p t' n i) ∧
    (∀ b : FullParameterRootAlgebra p t →+* FullParameterRootAlgebra p t',
      (∀ a : R, b (algebraMap R _ a) = algebraMap S _ (f a)) →
      (∀ (n : TameRootOrder p) (i : J),
        b (fullParameterRoot p t n i) = fullParameterRoot p t' n i) →
      b = fullRootFamilyMap p t t' f ht) := by
  have hc : ∀ a : R, fullRootFamilyMap p t t' f ht (algebraMap R _ a) =
      algebraMap S _ (f a) := by
    intro a
    change Ideal.quotientMap _ _ _ (Ideal.Quotient.mk _ (MvPolynomial.C a)) = _
    simp only [Ideal.quotientMap_mk, MvPolynomial.map_C]
    rfl
  have hx : ∀ (n : TameRootOrder p) (i : J),
      fullRootFamilyMap p t t' f ht (fullParameterRoot p t n i) =
        fullParameterRoot p t' n i := by
    intro n i
    simp [fullParameterRoot, fullRootFamilyMap]
  refine ⟨hc, hx, ?_⟩
  intro b hb hb'
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    exact (hb a).trans (hc a).symm
  · rintro ⟨i, n⟩
    simpa [fullParameterRoot] using
      (hb' n ((Fintype.equivFin J).symm i)).trans
        (hx n ((Fintype.equivFin J).symm i)).symm

/-- The canonical S-algebra isomorphism, with its complete pure-tensor formula.
Source: DAG proof steps 1 and 2, Stacks 01I4
(blueprint: lem-sfb-root-tower-profinite-base-change).

Proof: the root presentation represents compatible prime-to-p root families by
polynomial evaluation, quotient descent and the filtered-colimit universal property.
Map s tensor a to s times the coefficient-changed a by the tensor pushout property.
Conversely, the elements 1 tensor x(i,n) satisfy every power and transition relation,
so the root presentation over S gives the inverse. Both composites fix coefficients
and roots, hence are identities by quotient generation and tensor uniqueness. -/
theorem fullRoot_baseChange {J R S : Type u} [Fintype J] [CommRing R] [CommRing S]
    [Algebra R S] (p : ℕ) (hp : p.Prime) (t : J → R) :
    ∃ e : S ⊗[R] FullParameterRootAlgebra p t ≃ₐ[S]
        FullParameterRootAlgebra p (fun i ↦ algebraMap R S (t i)),
      ∀ (s : S) (a : FullParameterRootAlgebra p t),
        e (s ⊗ₜ[R] a) = algebraMap S _ s * fullRootBaseMap p t (algebraMap R S) a := by
  have _ := hp
  let A := FullParameterRootAlgebra p t
  let B := FullParameterRootAlgebra p (fun i ↦ algebraMap R S (t i))
  let q : MvPolynomial (Fin (Fintype.card J) × TameRootOrder p) R →+* A :=
    Ideal.Quotient.mk _
  let j : A →ₐ[R] S ⊗[R] A := Algebra.TensorProduct.includeRight
  let c : A →ₐ[R] B :=
    { __ := fullRootBaseMap p t (algebraMap R S)
      commutes' := (fullRootFamilyMap_normalization p t
        (fun i ↦ algebraMap R S (t i)) (algebraMap R S) (fun _ ↦ rfl)).1 }
  let φ : S ⊗[R] A →ₐ[S] B :=
    Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId S B) c
  let ev : MvPolynomial (Fin (Fintype.card J) × TameRootOrder p) S →+*
      S ⊗[R] A := MvPolynomial.eval₂Hom (algebraMap S _) (fun z ↦ j (q (MvPolynomial.X z)))
  have hev : Ideal.span (tameRootRelations p
      (fun i ↦ algebraMap R S (t ((Fintype.equivFin J).symm i)))) ≤ RingHom.ker ev := by
    apply Ideal.span_le.mpr
    intro z hz
    rcases hz with ⟨i, n, rfl⟩ | ⟨i, n, m, hnm, rfl⟩
    · have hq : q (MvPolynomial.X (i, n) ^ n.val -
          MvPolynomial.C (t ((Fintype.equivFin J).symm i))) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inl ⟨i, n, rfl⟩))
      have h := congrArg j hq
      have hC : q (MvPolynomial.C (t ((Fintype.equivFin J).symm i))) =
          algebraMap R A (t ((Fintype.equivFin J).symm i)) := rfl
      simp only [map_sub, map_pow, hC, map_zero] at h
      change ev _ = 0
      simp only [ev, map_sub, map_pow, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
      rw [← IsScalarTower.algebraMap_apply R S (S ⊗[R] A), ← j.commutes]
      exact h
    · have hq : q (MvPolynomial.X (i, m) ^ (m.val / n.val) -
          MvPolynomial.X (i, n)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span (Or.inr ⟨i, n, m, hnm, rfl⟩))
      have h := congrArg j hq
      simpa [ev, q, j, map_sub, map_pow] using h
  let ψ : B →ₐ[S] S ⊗[R] A :=
    { __ := Ideal.Quotient.lift _ ev (fun z hz ↦ hev hz)
      commutes' := by intro s; change ev (MvPolynomial.C s) = _; simp [ev] }
  have hφψ : φ.comp ψ = AlgHom.id S B := by
    apply AlgHom.coe_ringHom_injective
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro s
      change φ (ev (MvPolynomial.C s)) = _
      simp [ev]
      rfl
    · intro z
      change φ (ev (MvPolynomial.X z)) = Ideal.Quotient.mk _ (MvPolynomial.X z)
      simp only [ev, MvPolynomial.eval₂Hom_X', j,
        Algebra.TensorProduct.includeRight_apply, φ,
        Algebra.TensorProduct.productLeftAlgHom, Algebra.TensorProduct.lift_tmul,
        map_one, one_mul]
      change c (q (MvPolynomial.X z)) = _
      change Ideal.Quotient.mk _ (MvPolynomial.map _ (MvPolynomial.X z)) = _
      simp
  have hψφ : ψ.comp φ = AlgHom.id S (S ⊗[R] A) := by
    apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · apply AlgHom.coe_ringHom_injective
      apply Ideal.Quotient.ringHom_ext
      apply MvPolynomial.ringHom_ext
      · intro r
        change ψ (φ (1 ⊗ₜ[R] q (MvPolynomial.C r))) = j (q (MvPolynomial.C r))
        simp only [φ, Algebra.TensorProduct.productLeftAlgHom,
          Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        change ev (MvPolynomial.map (algebraMap R S) (MvPolynomial.C r)) = _
        simp only [MvPolynomial.map_C, ev, MvPolynomial.eval₂Hom_C]
        change algebraMap S (S ⊗[R] A) (algebraMap R S r) = j (algebraMap R A r)
        rw [j.commutes, IsScalarTower.algebraMap_apply R S (S ⊗[R] A)]
      · intro z
        change ψ (φ (1 ⊗ₜ[R] q (MvPolynomial.X z))) = j (q (MvPolynomial.X z))
        simp only [φ, Algebra.TensorProduct.productLeftAlgHom,
          Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        change ev (MvPolynomial.map (algebraMap R S) (MvPolynomial.X z)) = _
        simp [ev]
  refine ⟨AlgEquiv.ofAlgHom φ ψ hφψ hψφ, ?_⟩
  intro s a
  rfl

/-- Identity and composite coefficient changes preserve the same roots.
Source: DAG proof step 3 (blueprint: lem-sfb-root-tower-profinite-base-change).

Proof: the identity fixes every coefficient and variable. For a composite both maps
carry coefficients by g composed with f and preserve all root labels. The quotient
generation uniqueness from step 1 proves their equality. The pure-tensor formula
then gives the usual tensor associativity and unit coherence of the algebra isomorphisms. -/
theorem fullRootBaseMap_identity_composition
    {J R S V : Type u} [Fintype J] [CommRing R] [CommRing S] [CommRing V]
    (p : ℕ) (t : J → R) (f : R →+* S) (g : S →+* V) :
    fullRootBaseMap p t (RingHom.id R) = RingHom.id _ ∧
    fullRootBaseMap p t (g.comp f) =
      (fullRootBaseMap p (fun i ↦ f (t i)) g).comp (fullRootBaseMap p t f) := by
  constructor
  · symm
    apply (fullRootFamilyMap_normalization p t t (RingHom.id R) (fun _ ↦ rfl)).2.2
    · intro a; rfl
    · intro n i; rfl
  · symm
    apply (fullRootFamilyMap_normalization p t (fun i ↦ g (f (t i)))
      (g.comp f) (fun _ ↦ rfl)).2.2
    · intro a
      simp only [RingHom.comp_apply, fullRootBaseMap]
      rw [(fullRootFamilyMap_normalization p t (fun i ↦ f (t i)) f (fun _ ↦ rfl)).1,
        (fullRootFamilyMap_normalization p (fun i ↦ f (t i))
          (fun i ↦ g (f (t i))) g (fun _ ↦ rfl)).1]
    · intro n i
      simp only [RingHom.comp_apply, fullRootBaseMap]
      rw [(fullRootFamilyMap_normalization p t (fun i ↦ f (t i)) f (fun _ ↦ rfl)).2.1,
        (fullRootFamilyMap_normalization p (fun i ↦ f (t i))
          (fun i ↦ g (f (t i))) g (fun _ ↦ rfl)).2.1]

/-- Unit normalization of the canonical tensor comparison.
Source: DAG proof step 3 (blueprint: lem-sfb-root-tower-profinite-base-change).

Proof: the identity coefficient-change map fixes coefficients and every labelled root,
so it is the identity by quotient generation. Substitute this in the pure-tensor
formula. Multiplication by the coefficient is the ordinary scalar action. -/
theorem fullRoot_baseChange_unit {J R : Type u} [Fintype J] [CommRing R]
    (p : ℕ) (t : J → R)
    (e : R ⊗[R] FullParameterRootAlgebra p t ≃ₐ[R] FullParameterRootAlgebra p t)
    (he : ∀ (r : R) (a : FullParameterRootAlgebra p t),
      e (r ⊗ₜ[R] a) = algebraMap R _ r * fullRootBaseMap p t (RingHom.id R) a) :
    ∀ (r : R) (a : FullParameterRootAlgebra p t), e (r ⊗ₜ[R] a) = r • a := by
  intro r a
  rw [he, (fullRootBaseMap_identity_composition p t (RingHom.id R) (RingHom.id R)).1]
  exact (Algebra.smul_def r a).symm

/-- Composite normalization under the usual tensor reassociation.
Source: DAG proof step 3 (blueprint: lem-sfb-root-tower-profinite-base-change).

Proof: the two coefficient changes compose on coefficients and roots. Apply the three
pure-tensor formulas. Coefficient change sends s to g(s); multiplicativity then makes
both sides v*g(s) times the image of a. Pure tensors generate the iterated tensor
product, so this is exactly coherence with tensor associativity, including its unit cases. -/
theorem fullRoot_baseChange_composition
    {J R S V : Type u} [Fintype J] [CommRing R] [CommRing S] [CommRing V]
    [Algebra R S] [Algebra S V] [Algebra R V] [IsScalarTower R S V]
    (p : ℕ) (t : J → R)
    (e₁ : S ⊗[R] FullParameterRootAlgebra p t ≃ₐ[S]
      FullParameterRootAlgebra p (fun i ↦ algebraMap R S (t i)))
    (e₂ : V ⊗[S] FullParameterRootAlgebra p (fun i ↦ algebraMap R S (t i)) ≃ₐ[V]
      FullParameterRootAlgebra p (fun i ↦ algebraMap S V (algebraMap R S (t i))))
    (e₃ : V ⊗[R] FullParameterRootAlgebra p t ≃ₐ[V]
      FullParameterRootAlgebra p (fun i ↦ algebraMap S V (algebraMap R S (t i))))
    (h₁ : ∀ (s : S) (a : FullParameterRootAlgebra p t),
      e₁ (s ⊗ₜ[R] a) = algebraMap S _ s * fullRootBaseMap p t (algebraMap R S) a)
    (h₂ : ∀ (v : V)
      (b : FullParameterRootAlgebra p (fun i ↦ algebraMap R S (t i))),
      e₂ (v ⊗ₜ[S] b) = algebraMap V _ v *
        fullRootBaseMap p (fun i ↦ algebraMap R S (t i)) (algebraMap S V) b)
    (h₃ : ∀ (v : V) (a : FullParameterRootAlgebra p t),
      e₃ (v ⊗ₜ[R] a) = algebraMap V _ v *
        fullRootBaseMap p t ((algebraMap S V).comp (algebraMap R S)) a) :
    ∀ (v : V) (s : S) (a : FullParameterRootAlgebra p t),
      e₂ (v ⊗ₜ[S] e₁ (s ⊗ₜ[R] a)) = e₃ ((v * algebraMap S V s) ⊗ₜ[R] a) := by
  intro v s a
  rw [h₁, h₂, h₃, map_mul]
  have hc := (fullRootFamilyMap_normalization p
    (fun i ↦ algebraMap R S (t i))
    (fun i ↦ algebraMap S V (algebraMap R S (t i)))
    (algebraMap S V) (fun _ ↦ rfl)).1 s
  change fullRootBaseMap p (fun i ↦ algebraMap R S (t i)) (algebraMap S V)
    (algebraMap S _ s) = _ at hc
  rw [hc, (fullRootBaseMap_identity_composition p t
    (algebraMap R S) (algebraMap S V)).2]
  simp only [RingHom.comp_apply, map_mul, mul_assoc]

/-- Scheme base change with both projections fixed, for the actual root spectra.
Source: DAG proof step 4, Stacks 01I4
(blueprint: lem-sfb-root-tower-profinite-base-change).

Proof: apply Spec to the algebra isomorphism of step 2 and the affine fibre-product
formula. Its two projections are the coefficient-change and structural maps by
their coefficient and root formulas. These equations uniquely determine the comparison,
so step 3 supplies compatibility with identity and composite base changes. -/
theorem fullRoot_schemeBaseChange
    {J R S : Type u} [Fintype J] [CommRing R] [CommRing S]
    (p : ℕ) (hp : p.Prime) (t : J → R) (f : R →+* S) :
    ∃ e : Spec (.of (FullParameterRootAlgebra p (fun i ↦ f (t i)))) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R (FullParameterRootAlgebra p t))))
        (Spec.map (CommRingCat.ofHom f)),
      e.hom ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (fullRootBaseMap p t f)) ∧
      e.hom ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom
        (algebraMap S (FullParameterRootAlgebra p (fun i ↦ f (t i))))) := by
  let : Algebra R S := f.toAlgebra
  obtain ⟨e, he⟩ := fullRoot_baseChange p hp t (S := S)
  have h : IsPushout (CommRingCat.ofHom f)
      (CommRingCat.ofHom (algebraMap R (FullParameterRootAlgebra p t)))
      (CommRingCat.ofHom (algebraMap S
        (FullParameterRootAlgebra p (fun i ↦ f (t i)))))
      (CommRingCat.ofHom (fullRootBaseMap p t f)) := by
    refine (CommRingCat.isPushout_tensorProduct R S
      (FullParameterRootAlgebra p t)).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toRingEquiv.toCommRingCatIso
      (by rfl) (by rfl) ?_ ?_
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro s
      change e (s ⊗ₜ[R] 1) = algebraMap S _ s
      rw [he, map_one, mul_one]
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      change e (1 ⊗ₜ[R] a) = fullRootBaseMap p t f a
      rw [he, map_one, one_mul]
      rfl
  have h' := isPullback_SpecMap_of_isPushout _ _ _ _ h.flip
  exact ⟨h'.isoPullback, h'.isoPullback_hom_fst, h'.isoPullback_hom_snd⟩

/-- Each indicated principal open commutes with ring base change as a scheme.
Source: DAG proof step 4, Stacks 01I4 and the basic-open pullback formula
(blueprint: lem-sfb-root-tower-profinite-base-change).

Proof: put h=product(t i) over I. The root comparison carries h to product(f(t i)).
The inverse image of D(h) is therefore this basic open. Restrict the scheme isomorphism
of step 4, with its structure sheaf, and use the pullback universal property. The
projection equations below fix the restriction uniquely, including h=1 and zero rings. -/
theorem fullRoot_openBaseChange
    {J R S : Type u} [Fintype J] [CommRing R] [CommRing S]
    (p : ℕ) (hp : p.Prime) (t : J → R) (f : R →+* S) (I : Finset J) :
    ∃ e : (Scheme.Opens.toScheme (X := Spec (.of _))
          (PrimeSpectrum.basicOpen
        (algebraMap S (FullParameterRootAlgebra p (fun i ↦ f (t i)))
          (∏ i ∈ I, f (t i))) : (Spec (.of _)).Opens)) ≅
      pullback ((Scheme.Opens.ι (X := Spec (.of _))
          (PrimeSpectrum.basicOpen
          (algebraMap R (FullParameterRootAlgebra p t) (∏ i ∈ I, t i)) : (Spec (.of _)).Opens)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (FullParameterRootAlgebra p t))))
        (Spec.map (CommRingCat.ofHom f)),
      e.hom ≫ pullback.fst _ _ ≫ (Scheme.Opens.ι (X := Spec (.of _))
          (PrimeSpectrum.basicOpen
          (algebraMap R (FullParameterRootAlgebra p t) (∏ i ∈ I, t i)) : (Spec (.of _)).Opens)) =
        (Scheme.Opens.ι (X := Spec (.of _))
          (PrimeSpectrum.basicOpen
          (algebraMap S (FullParameterRootAlgebra p (fun i ↦ f (t i)))
            (∏ i ∈ I, f (t i)))
            : (Spec (.of _)).Opens)) ≫ Spec.map (CommRingCat.ofHom (fullRootBaseMap p t f)) ∧
      e.hom ≫ pullback.snd _ _ = (Scheme.Opens.ι (X := Spec (.of _))
          (PrimeSpectrum.basicOpen
          (algebraMap S (FullParameterRootAlgebra p (fun i ↦ f (t i)))
            (∏ i ∈ I, f (t i))) : (Spec (.of _)).Opens)) ≫ Spec.map (CommRingCat.ofHom
          (algebraMap S (FullParameterRootAlgebra p (fun i ↦ f (t i))))) := by
  obtain ⟨e, he₁, he₂⟩ := fullRoot_schemeBaseChange p hp t f
  let m := Spec.map (CommRingCat.ofHom (fullRootBaseMap p t f))
  let n := Spec.map (CommRingCat.ofHom
    (algebraMap S (FullParameterRootAlgebra p (fun i ↦ f (t i)))))
  let r := Spec.map (CommRingCat.ofHom (algebraMap R (FullParameterRootAlgebra p t)))
  let g := Spec.map (CommRingCat.ofHom f)
  have hpb : IsPullback m n r g := by
    apply IsPullback.of_iso_pullback _ e he₁ he₂
    exact ⟨by rw [← he₁, ← he₂, Category.assoc, Category.assoc, pullback.condition]⟩
  let U : (Spec (.of (FullParameterRootAlgebra p t))).Opens :=
    PrimeSpectrum.basicOpen (algebraMap R _ (∏ i ∈ I, t i))
  have ho : m ⁻¹ᵁ U = (PrimeSpectrum.basicOpen
      (algebraMap S (FullParameterRootAlgebra p (fun i ↦ f (t i)))
        (∏ i ∈ I, f (t i))) : (Spec (.of _)).Opens) := by
    change Spec.map _ ⁻¹ᵁ PrimeSpectrum.basicOpen _ = _
    rw [SpecMap_preimage_basicOpen]
    congr 1
    change fullRootBaseMap p t f (algebraMap R _ _) = _
    dsimp only [fullRootBaseMap]
    rw [(fullRootFamilyMap_normalization p t (fun i ↦ f (t i)) f (fun _ ↦ rfl)).1]
    simp only [map_prod]
  let d := (Spec (.of (FullParameterRootAlgebra p (fun i ↦ f (t i))))).isoOfEq ho.symm
  have h := (isPullback_morphismRestrict m U).paste_vert hpb
  refine ⟨d ≪≫ h.isoPullback, ?_, ?_⟩
  · change (d.hom ≫ h.isoPullback.hom) ≫ pullback.fst _ _ ≫ U.ι = _
    rw [Category.assoc, h.isoPullback_hom_fst_assoc, morphismRestrict_ι]
    rw [← Category.assoc, Scheme.isoOfEq_hom_ι]
  · change (d.hom ≫ h.isoPullback.hom) ≫ pullback.snd _ _ = _
    rw [Category.assoc, h.isoPullback_hom_snd, ← Category.assoc,
      Scheme.isoOfEq_hom_ι]

/-- The actual coefficient ring R_P. Source: DAG proof step 5, Stacks 01I4 and 097D
(blueprint: lem-sfb-root-tower-profinite-base-change). -/
abbrev rootTestRing (R : Type u) [CommRing R] (P : Profinite.{u}) :=
  R ⊗[ℤ] LocallyConstant P ℤ

/-- Ring and profinite parameter maps on R_P, by tensoring f and pullback of functions.
Source: DAG proof steps 5 and 7 (blueprint: lem-sfb-root-tower-profinite-base-change). -/
def rootTestRingMap {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {P P' : Profinite.{u}} (a : P' ⟶ P) : rootTestRing R P →+* rootTestRing S P' :=
  (Algebra.TensorProduct.map f.toIntAlgHom
    (LocallyConstant.comapRingHom a.hom.hom).toIntAlgHom).toRingHom

/-- The tensor map on parameters preserves the coefficient inclusion.
Source: DAG proof step 7 (blueprint: lem-sfb-root-tower-profinite-base-change).

Proof: tensor maps carry r tensor 1 to f(r) tensor 1, since function pullback preserves 1. -/
theorem rootTestRingMap_coeff {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {P P' : Profinite.{u}} (a : P' ⟶ P) (r : R) :
    rootTestRingMap f a (algebraMap R (rootTestRing R P) r) =
      algebraMap S (rootTestRing S P') (f r) := by
  simp [rootTestRingMap, Algebra.TensorProduct.algebraMap_apply]

/-- Canonical mixed ring/parameter map of root towers, on their quotient presentations.
Source: DAG proof step 7 (blueprint: lem-sfb-root-tower-profinite-base-change). -/
def fullRootTestMap {J R S : Type u} [Fintype J] [CommRing R] [CommRing S]
    (p : ℕ) (t : J → R) (f : R →+* S) {P P' : Profinite.{u}} (a : P' ⟶ P) :
    FullParameterRootAlgebra p (fun i ↦ algebraMap R (rootTestRing R P) (t i)) →+*
      FullParameterRootAlgebra p (fun i ↦ algebraMap S (rootTestRing S P') (f (t i))) :=
  fullRootFamilyMap p (fun i ↦ algebraMap R (rootTestRing R P) (t i))
    (fun i ↦ algebraMap S (rootTestRing S P') (f (t i))) (rootTestRingMap f a)
    (fun i ↦ rootTestRingMap_coeff f a (t i))

private theorem testScheme_map {P P' : Profinite.{u}} (a : P' ⟶ P) :
    profiniteToScheme.map a =
      Spec.map (CommRingCat.ofHom (LocallyConstant.comapRingHom a.hom.hom)) := rfl

private theorem test_hom_ext {W X : Scheme.{u}} {P : Profinite.{u}}
    {f g : W ⟶ profiniteProduct X P}
    (h₁ : f ≫ pullback.fst (toSpecZ (profiniteToScheme.obj P)) (toSpecZ X) =
      g ≫ pullback.fst (toSpecZ (profiniteToScheme.obj P)) (toSpecZ X))
    (h₂ : f ≫ profiniteProductBase X P = g ≫ profiniteProductBase X P) : f = g := by
  apply pullback.hom_ext
  · exact h₁
  · exact h₂

private theorem testMap_fst {X Y : Scheme.{u}} (f : X ⟶ Y)
    {P P' : Profinite.{u}} (a : P' ⟶ P) :
    profiniteProductMap f a ≫ pullback.fst
      (toSpecZ (profiniteToScheme.obj P)) (toSpecZ Y) =
      pullback.fst (toSpecZ (profiniteToScheme.obj P')) (toSpecZ X) ≫
        profiniteToScheme.map a := by
  dsimp only [profiniteProductMap, pullback.map]
  erw [pullback.lift_fst]
  rfl

private theorem testMap_snd {X Y : Scheme.{u}} (f : X ⟶ Y)
    {P P' : Profinite.{u}} (a : P' ⟶ P) :
    profiniteProductMap f a ≫ profiniteProductBase Y P =
      profiniteProductBase X P' ≫ f := by
  dsimp only [profiniteProductMap, pullback.map]
  erw [pullback.lift_snd]
  rfl

private theorem testMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {P Q V : Profinite.{u}} (a : P ⟶ Q) (b : Q ⟶ V) :
    profiniteProductMap f a ≫ profiniteProductMap g b =
      profiniteProductMap (f ≫ g) (a ≫ b) := by
  apply test_hom_ext
  · rw [Category.assoc, testMap_fst g b, ← Category.assoc,
      testMap_fst f a, testMap_fst (f ≫ g) (a ≫ b), Category.assoc,
      profiniteToScheme.map_comp]
  · rw [Category.assoc, testMap_snd g b, ← Category.assoc,
      testMap_snd f a, testMap_snd (f ≫ g) (a ≫ b), Category.assoc]

private theorem rootTestRing_square (R : Type u) [CommRing R] (P : Profinite.{u}) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        LocallyConstant P ℤ →ₐ[ℤ] rootTestRing R P).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R (rootTestRing R P))))
      (toSpecZ (profiniteToScheme.obj P)) (toSpecZ (Spec (.of R))) := by
  let f : CommRingCat.of (ULift.{u} ℤ) ⟶ CommRingCat.of R :=
    CommRingCat.ofHom ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom)
  let g : CommRingCat.of (ULift.{u} ℤ) ⟶ CommRingCat.of (LocallyConstant P ℤ) :=
    CommRingCat.ofHom ((Int.castRingHom _).comp ULift.ringEquiv.toRingHom)
  let c : PushoutCocone f g := PushoutCocone.mk
    (CommRingCat.ofHom (algebraMap R (rootTestRing R P)))
    (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
      LocallyConstant P ℤ →ₐ[ℤ] rootTestRing R P).toRingHom)
    (by ext z; simp [f, g])
  have hc : IsColimit c := by
    refine PushoutCocone.IsColimit.mk _ (fun s ↦ CommRingCat.ofHom
      (Algebra.TensorProduct.productMap s.inl.hom.toIntAlgHom
        s.inr.hom.toIntAlgHom).toRingHom) ?_ ?_ ?_
    · intro s
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      change s.inl.hom r * s.inr.hom 1 = s.inl.hom r
      simp
    · intro s
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro l
      change s.inl.hom 1 * s.inr.hom l = s.inr.hom l
      simp
    · intro s m h₁ h₂
      apply CommRingCat.hom_ext
      apply Algebra.TensorProduct.ringHom_ext
      · apply RingHom.ext
        intro r
        simpa using congr($(h₁).hom r)
      · apply RingHom.ext
        intro l
        simpa using congr($(h₂).hom l)
  have h := isPullback_SpecMap_of_isPushout _ _ _ _ (IsPushout.of_isColimit hc).flip
  convert h using 1 <;> first | rfl | exact specULiftZIsTerminal.hom_ext _ _

/-- Profinite charts are the affine pro-etale spectra of R_P, naturally in both inputs.
Source: DAG proof steps 5 and 7, Stacks 01I4, 097D, 094U, 01SH
(blueprint: lem-sfb-root-tower-profinite-base-change).

Proof: use the affine tensor fibre-product formula, commuting the two tensor factors.
Normalize by both projections. Weak etaleness follows by base change of Spec LC(P,Z)
over Spec Z, and the map is affine since both spectra are affine. Pullback of functions
and ring maps give the tensor map on every pure tensor; uniqueness proves naturality. -/
theorem fullRoot_profiniteCharts :
    ∃ e : ∀ (R : Type u) [CommRing R] (P : Profinite.{u}),
        profiniteProduct (Spec (.of R)) P ≅ Spec (.of (rootTestRing R P)),
      (∀ (R : Type u) [CommRing R] (P : Profinite.{u}),
        (e R P).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R (rootTestRing R P))) =
          profiniteProductBase (Spec (.of R)) P ∧
        (e R P).hom ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight :
            LocallyConstant P ℤ →ₐ[ℤ] rootTestRing R P).toRingHom) =
          pullback.fst _ _ ∧
        IsAffineHom (profiniteProductBase (Spec (.of R)) P) ∧
        WeaklyEtale (profiniteProductBase (Spec (.of R)) P)) ∧
      (∀ (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S)
        (P P' : Profinite.{u}) (a : P' ⟶ P),
        profiniteProductMap (Spec.map (CommRingCat.ofHom f)) a ≫ (e R P).hom =
          (e S P').hom ≫ Spec.map (CommRingCat.ofHom (rootTestRingMap f a))) := by
  let e := fun (R : Type u) [CommRing R] (P : Profinite.{u}) ↦
    (rootTestRing_square R P).isoPullback.symm
  have he₁ (R : Type u) [CommRing R] (P : Profinite.{u}) :
      (e R P).hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap R (rootTestRing R P))) = profiniteProductBase (Spec (.of R)) P := by
    dsimp only [e, Iso.symm_hom]
    exact (rootTestRing_square R P).isoPullback_inv_snd
  have he₂ (R : Type u) [CommRing R] (P : Profinite.{u}) :
      (e R P).hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight :
          LocallyConstant P ℤ →ₐ[ℤ] rootTestRing R P).toRingHom) = pullback.fst _ _ := by
    dsimp only [e, Iso.symm_hom]
    exact (rootTestRing_square R P).isoPullback_inv_fst
  refine ⟨e, ?_, ?_⟩
  · intro R _ P
    refine ⟨he₁ R P, he₂ R P, ?_, ?_⟩
    · change IsAffineHom (pullback.snd (toSpecZ (profiniteToScheme.obj P)) _)
      have : IsAffine (profiniteToScheme.obj P) := inferInstanceAs
        (IsAffine (Spec (.of (LocallyConstant P ℤ))))
      infer_instance
    · change WeaklyEtale (pullback.snd _ _)
      infer_instance
  · intro R S _ _ f P P' a
    apply (cancel_mono (e R P).inv).mp
    apply test_hom_ext
    · simp only [Category.assoc]
      change profiniteProductMap (Spec.map (CommRingCat.ofHom f)) a ≫
          (e R P).hom ≫ (e R P).inv ≫ pullback.fst _ _ = _
      rw [Iso.hom_inv_id_assoc]
      rw [testMap_fst (Spec.map (CommRingCat.ofHom f)) a]
      change _ = (e S P').hom ≫ Spec.map _ ≫
        (rootTestRing_square R P).isoPullback.hom ≫ pullback.fst _ _
      rw [(rootTestRing_square R P).isoPullback_hom_fst]
      calc
        _ = ((e S P').hom ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight :
            LocallyConstant P' ℤ →ₐ[ℤ] rootTestRing S P').toRingHom)) ≫
              profiniteToScheme.map a := by rw [he₂]
        _ = _ := by
          rw [testScheme_map, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
          apply congrArg (fun k ↦ (e S P').hom ≫ Spec.map k)
          apply CommRingCat.hom_ext
          apply RingHom.ext
          intro l
          simp [rootTestRingMap]
    · simp only [Category.assoc]
      change profiniteProductMap (Spec.map (CommRingCat.ofHom f)) a ≫
          (e R P).hom ≫ (e R P).inv ≫ profiniteProductBase _ P = _
      rw [Iso.hom_inv_id_assoc]
      rw [testMap_snd (Spec.map (CommRingCat.ofHom f)) a]
      change _ = (e S P').hom ≫ Spec.map _ ≫
        (rootTestRing_square R P).isoPullback.hom ≫ pullback.snd _ _
      rw [(rootTestRing_square R P).isoPullback_hom_snd]
      calc
        _ = ((e S P').hom ≫ Spec.map (CommRingCat.ofHom
          (algebraMap S (rootTestRing S P')))) ≫ Spec.map (CommRingCat.ofHom f) := by
          rw [he₁]
        _ = _ := by
          rw [Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
          apply congrArg (fun k ↦ (e S P').hom ≫ Spec.map k)
          apply CommRingCat.hom_ext
          apply RingHom.ext
          exact rootTestRingMap_coeff f a

private theorem fullRoot_testSquare {J R : Type u} [Fintype J] [CommRing R]
    (p : ℕ) (hp : p.Prime) (t : J → R) (P : Profinite.{u}) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap (rootTestRing R P)
        (FullParameterRootAlgebra p (fun i ↦ algebraMap R (rootTestRing R P) (t i))))) ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          LocallyConstant P ℤ →ₐ[ℤ] rootTestRing R P).toRingHom))
      (Spec.map (CommRingCat.ofHom
        (fullRootBaseMap p t (algebraMap R (rootTestRing R P)))))
      (toSpecZ (profiniteToScheme.obj P))
      (toSpecZ (Spec (.of (FullParameterRootAlgebra p t)))) := by
  obtain ⟨e, he₁, he₂⟩ := fullRoot_schemeBaseChange p hp t
    (algebraMap R (rootTestRing R P))
  have h := IsPullback.of_iso_pullback
    ⟨by rw [← he₁, ← he₂, Category.assoc, Category.assoc, pullback.condition]⟩
    e he₁ he₂
  have h' := (h.paste_vert (rootTestRing_square R P).flip).flip
  simpa only [comp_toSpecZ] using h'

/-- Root-tower profinite comparisons, including all punctures and mixed naturality.
Source: DAG proof steps 2, 4, 5 and 7, Stacks 01I4 and 097D
(blueprint: lem-sfb-root-tower-profinite-base-change).

Proof: for A=A_p(R,t), identify (R tensor LC(P,Z)) tensor_R A with LC(P,Z) tensor A
by (r tensor l) tensor a mapping to l tensor ra, with inverse l tensor a mapping to
(1 tensor l) tensor a. Compose the ring base-change comparison with the affine
profinite-chart comparison. Its two projections are the root-preserving map and
the LC inclusion. Restrict to each inverse-image principal open to get the displayed
scheme isomorphism d. For mixed maps, both composites have the same root labels,
coefficients and LC functions, so they agree by tensor and quotient uniqueness.
Restriction preserves these identities and commutes with the original projections. -/
theorem fullRoot_profiniteBaseChange {J : Type u} [Fintype J] (p : ℕ) (hp : p.Prime) :
    ∃ e : ∀ (R : Type u) [CommRing R] (t : J → R) (P : Profinite.{u}),
        Spec (.of (FullParameterRootAlgebra p
          (fun i ↦ algebraMap R (rootTestRing R P) (t i)))) ≅
          profiniteProduct (Spec (.of (FullParameterRootAlgebra p t))) P,
      (∀ (R : Type u) [CommRing R] (t : J → R) (P : Profinite.{u}),
        (e R t P).hom ≫ profiniteProductBase _ P =
          Spec.map (CommRingCat.ofHom (fullRootBaseMap p t
            (algebraMap R (rootTestRing R P)))) ∧
        (e R t P).hom ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom (algebraMap (rootTestRing R P)
            (FullParameterRootAlgebra p
              (fun i ↦ algebraMap R (rootTestRing R P) (t i))))) ≫
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
            LocallyConstant P ℤ →ₐ[ℤ] rootTestRing R P).toRingHom) ∧
        (∀ I : Finset J, ∃ d :
            (Scheme.Opens.toScheme (X := Spec (.of _))
          (PrimeSpectrum.basicOpen
              (algebraMap (rootTestRing R P) (FullParameterRootAlgebra p
                (fun i ↦ algebraMap R (rootTestRing R P) (t i)))
                (∏ i ∈ I, algebraMap R (rootTestRing R P) (t i))) : (Spec (.of _)).Opens)) ≅
            ((profiniteProductBase (Spec (.of (FullParameterRootAlgebra p t))) P) ⁻¹ᵁ
              (PrimeSpectrum.basicOpen
                (algebraMap R (FullParameterRootAlgebra p t) (∏ i ∈ I, t i))
                : (Spec (.of _)).Opens)).toScheme,
          d.hom ≫ ((profiniteProductBase (Spec (.of (FullParameterRootAlgebra p t))) P) ⁻¹ᵁ
              (PrimeSpectrum.basicOpen
                (algebraMap R (FullParameterRootAlgebra p t) (∏ i ∈ I, t i))
                : (Spec (.of _)).Opens)).ι =
            (Scheme.Opens.ι (X := Spec (.of _))
          (PrimeSpectrum.basicOpen
              (algebraMap (rootTestRing R P) (FullParameterRootAlgebra p
                (fun i ↦ algebraMap R (rootTestRing R P) (t i)))
                (∏ i ∈ I, algebraMap R (rootTestRing R P) (t i)))
                : (Spec (.of _)).Opens)) ≫ (e R t P).hom)) ∧
      (∀ (R S : Type u) [CommRing R] [CommRing S] (t : J → R) (f : R →+* S)
        (P P' : Profinite.{u}) (a : P' ⟶ P),
        Spec.map (CommRingCat.ofHom (fullRootTestMap p t f a)) ≫ (e R t P).hom =
          (e S (fun i ↦ f (t i)) P').hom ≫
            profiniteProductMap (Spec.map (CommRingCat.ofHom (fullRootBaseMap p t f))) a) := by
  let e := fun (R : Type u) [CommRing R] (t : J → R) (P : Profinite.{u}) ↦
    (fullRoot_testSquare p hp t P).isoPullback
  have he₁ (R : Type u) [CommRing R] (t : J → R) (P : Profinite.{u}) :
      (e R t P).hom ≫ profiniteProductBase _ P = Spec.map (CommRingCat.ofHom
        (fullRootBaseMap p t (algebraMap R (rootTestRing R P)))) :=
    (fullRoot_testSquare p hp t P).isoPullback_hom_snd
  have he₂ (R : Type u) [CommRing R] (t : J → R) (P : Profinite.{u}) :
      (e R t P).hom ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (algebraMap (rootTestRing R P)
          (FullParameterRootAlgebra p (fun i ↦ algebraMap R (rootTestRing R P) (t i))))) ≫
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
            LocallyConstant P ℤ →ₐ[ℤ] rootTestRing R P).toRingHom) :=
    (fullRoot_testSquare p hp t P).isoPullback_hom_fst
  refine ⟨e, ?_, ?_⟩
  · intro R _ t P
    refine ⟨he₁ R t P, he₂ R t P, ?_⟩
    intro I
    let U : (Spec (.of (FullParameterRootAlgebra p t))).Opens :=
      PrimeSpectrum.basicOpen (algebraMap R _ (∏ i ∈ I, t i))
    let V := profiniteProductBase (Spec (.of (FullParameterRootAlgebra p t))) P ⁻¹ᵁ U
    have ho : (e R t P).hom ⁻¹ᵁ V =
        (PrimeSpectrum.basicOpen (algebraMap (rootTestRing R P)
          (FullParameterRootAlgebra p (fun i ↦ algebraMap R (rootTestRing R P) (t i)))
          (∏ i ∈ I, algebraMap R (rootTestRing R P) (t i))) :
          (Spec (.of (FullParameterRootAlgebra p
            (fun i ↦ algebraMap R (rootTestRing R P) (t i))))).Opens) := by
      change ((e R t P).hom ≫ profiniteProductBase _ P) ⁻¹ᵁ U = _
      rw [he₁]
      change Spec.map _ ⁻¹ᵁ PrimeSpectrum.basicOpen _ = _
      rw [SpecMap_preimage_basicOpen]
      congr 1
      change fullRootFamilyMap p t _ (algebraMap R (rootTestRing R P))
        (fun _ ↦ rfl) (algebraMap R _ _) = _
      rw [(fullRootFamilyMap_normalization p t _
        (algebraMap R (rootTestRing R P)) (fun _ ↦ rfl)).1]
      simp only [map_prod]
    let d := (Spec (.of (FullParameterRootAlgebra p
      (fun i ↦ algebraMap R (rootTestRing R P) (t i))))).isoOfEq ho.symm ≪≫
        (e R t P).hom.preimageIso V
    refine ⟨d, ?_⟩
    dsimp only [d, Iso.trans_hom]
    rw [Category.assoc, Scheme.Hom.preimageIso_hom_ι, ← Category.assoc,
      Scheme.isoOfEq_hom_ι]
  · intro R S _ _ t f P P' a
    have hc := (fullRootFamilyMap_normalization p
      (fun i ↦ algebraMap R (rootTestRing R P) (t i))
      (fun i ↦ algebraMap S (rootTestRing S P') (f (t i)))
      (rootTestRingMap f a) (fun i ↦ rootTestRingMap_coeff f a (t i))).1
    apply test_hom_ext
    · simp only [Category.assoc]
      erw [he₂, testMap_fst]
      simp only [← Category.assoc]
      erw [he₂ S (fun i ↦ f (t i)) P']
      rw [testScheme_map]
      simp only [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro l
      change fullRootTestMap p t f a
        (algebraMap (rootTestRing R P) _
          (Algebra.TensorProduct.includeRight l)) =
        algebraMap (rootTestRing S P') _
          (Algebra.TensorProduct.includeRight (LocallyConstant.comapRingHom a.hom.hom l))
      dsimp only [fullRootTestMap]
      rw [hc]
      congr 1
      simp [rootTestRingMap]
    · change _ ≫ (e R t P).hom ≫ profiniteProductBase _ P =
        (e S (fun i ↦ f (t i)) P').hom ≫ _ ≫ profiniteProductBase _ P
      rw [he₁, testMap_snd, ← Category.assoc, he₁, ← Spec.map_comp,
        ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply fullRoot_hom_ext p t
      · intro r
        change fullRootTestMap p t f a
          (fullRootBaseMap p t (algebraMap R (rootTestRing R P)) (algebraMap R _ r)) =
          fullRootBaseMap p (fun i ↦ f (t i)) (algebraMap S (rootTestRing S P'))
            (fullRootBaseMap p t f (algebraMap R _ r))
        dsimp only [fullRootBaseMap, fullRootTestMap]
        rw [(fullRootFamilyMap_normalization p t _ _ (fun _ ↦ rfl)).1, hc,
          (fullRootFamilyMap_normalization p t _ f (fun _ ↦ rfl)).1,
          (fullRootFamilyMap_normalization p (fun i ↦ f (t i)) _ _ (fun _ ↦ rfl)).1,
          rootTestRingMap_coeff]
      · intro n i
        change fullRootTestMap p t f a
          (fullRootBaseMap p t (algebraMap R (rootTestRing R P))
            (fullParameterRoot p t n i)) =
          fullRootBaseMap p (fun i ↦ f (t i)) (algebraMap S (rootTestRing S P'))
            (fullRootBaseMap p t f (fullParameterRoot p t n i))
        dsimp only [fullRootBaseMap, fullRootTestMap]
        rw [(fullRootFamilyMap_normalization p t _ _ (fun _ ↦ rfl)).2.1,
          (fullRootFamilyMap_normalization p _ _ (rootTestRingMap f a)
            (fun i ↦ rootTestRingMap_coeff f a (t i))).2.1,
          (fullRootFamilyMap_normalization p t _ f (fun _ ↦ rfl)).2.1,
          (fullRootFamilyMap_normalization p (fun i ↦ f (t i)) _ _ (fun _ ↦ rfl)).2.1]

private theorem testProduct_square (X : Scheme.{u}) (P Q : Profinite.{u}) :
    IsPullback
      (profiniteProductMap (𝟙 X) (prod.fst : P ⨯ Q ⟶ P))
      (profiniteProductMap (𝟙 X) (prod.snd : P ⨯ Q ⟶ Q))
      (profiniteProductBase X P) (profiniteProductBase X Q) := by
  let F := (profiniteToProEt ⋙ Scheme.ProEt.forget specZ) ⋙ Over.pullback (toSpecZ X)
  have : PreservesFiniteLimits F := by dsimp only [F]; infer_instance
  have h := Over.isPullback_of_binaryFan_isLimit _
    (isLimitOfHasBinaryProductOfPreservesLimit F P Q)
  have hm {P P' : Profinite.{u}} (a : P' ⟶ P) :
      profiniteProductMap (𝟙 X) a = (F.map a).left := by
    apply test_hom_ext
    · rw [testMap_fst (𝟙 X) a]
      change _ = pullback.lift _ _ _ ≫ pullback.fst _ _
      erw [pullback.lift_fst]
      rfl
    · rw [testMap_snd, Category.comp_id]
      change _ = pullback.lift _ _ _ ≫ pullback.snd _ _
      erw [pullback.lift_snd]
      rfl
  change IsPullback _ _ (profiniteProductBase X P) (profiniteProductBase X Q) at h
  rw [hm, hm]
  exact h

private theorem testIterated_square (X : Scheme.{u}) (P Q : Profinite.{u}) :
    IsPullback (profiniteProductBase (profiniteProduct X P) Q)
      (profiniteProductMap (profiniteProductBase X P) (𝟙 Q))
      (profiniteProductBase X P) (profiniteProductBase X Q) := by
  apply IsPullback.flip
  apply IsPullback.of_right (h₁₂ := pullback.fst
    (toSpecZ (profiniteToScheme.obj Q)) (toSpecZ X))
    (h₂₂ := toSpecZ X) ?_ (testMap_snd _ _) (IsPullback.of_hasPullback _ _)
  rw [testMap_fst, profiniteToScheme.map_id, Category.comp_id, comp_toSpecZ]
  exact IsPullback.of_hasPullback _ _

/-- Iterated profinite tests are the test by the product, with all projections and naturality.
Source: DAG proof steps 6 and 7, finite-limit preservation of profiniteToProEt
(blueprint: lem-sfb-root-tower-profinite-base-change).

Proof: finite-limit preservation identifies u(P times Q) with the product in the
pro-etale site. The scheme fibre product is also an object of that site: its structure
map is weakly etale by base change and composition, and the scheme is affine and bounded.
Fullness of site morphisms gives its scheme universal property. The unique product
isomorphism, followed by fibre-product reassociation, gives the comparison over X.
Each normalization is its stated projection. For any f,a,b both composites have the
same three projections, proving naturality. Empty profinite parameters give empty
schemes; the same universal properties include them without a nonemptiness assumption. -/
theorem fullRoot_profiniteProducts :
    ∃ e : ∀ (X : Scheme.{u}) [IsAffine X] (P Q : Profinite.{u}),
        profiniteProduct (profiniteProduct X P) Q ≅ profiniteProduct X (P ⨯ Q),
      (∀ (X : Scheme.{u}) [IsAffine X] (P Q : Profinite.{u}),
        (e X P Q).hom ≫ profiniteProductMap (𝟙 X) (prod.fst : P ⨯ Q ⟶ P) =
          profiniteProductBase (profiniteProduct X P) Q ∧
        (e X P Q).hom ≫ profiniteProductMap (𝟙 X) (prod.snd : P ⨯ Q ⟶ Q) =
          profiniteProductMap (profiniteProductBase X P) (𝟙 Q)) ∧
      (∀ (X X' : Scheme.{u}) [IsAffine X] [IsAffine X'] (f : X' ⟶ X)
        (P P' Q Q' : Profinite.{u}) (a : P' ⟶ P) (b : Q' ⟶ Q),
        profiniteProductMap (profiniteProductMap f a) b ≫ (e X P Q).hom =
          (e X' P' Q').hom ≫ profiniteProductMap f (prod.map a b)) := by
  let e := fun (X : Scheme.{u}) (P Q : Profinite.{u}) ↦
    (testIterated_square X P Q).isoIsPullback _ _ (testProduct_square X P Q)
  have he₁ (X : Scheme.{u}) (P Q : Profinite.{u}) :
      (e X P Q).hom ≫ profiniteProductMap (𝟙 X) (prod.fst : P ⨯ Q ⟶ P) =
        profiniteProductBase (profiniteProduct X P) Q :=
    (testIterated_square X P Q).isoIsPullback_hom_fst _ _ (testProduct_square X P Q)
  have he₂ (X : Scheme.{u}) (P Q : Profinite.{u}) :
      (e X P Q).hom ≫ profiniteProductMap (𝟙 X) (prod.snd : P ⨯ Q ⟶ Q) =
        profiniteProductMap (profiniteProductBase X P) (𝟙 Q) :=
    (testIterated_square X P Q).isoIsPullback_hom_snd _ _ (testProduct_square X P Q)
  refine ⟨fun X _ P Q ↦ e X P Q, fun X _ P Q ↦ ⟨he₁ X P Q, he₂ X P Q⟩, ?_⟩
  intro X X' _ _ f P P' Q Q' a b
  apply (testProduct_square X P Q).hom_ext
  · change (_ ≫ (e X P Q).hom) ≫ _ = ((e X' P' Q').hom ≫ _) ≫ _
    rw [Category.assoc, he₁, testMap_snd]
    rw [Category.assoc, testMap_comp f (𝟙 X) (prod.map a b) prod.fst,
      Category.comp_id, prod.map_fst]
    have hc := testMap_comp (𝟙 X') f (prod.fst : P' ⨯ Q' ⟶ P') a
    rw [Category.id_comp] at hc
    rw [← hc, ← Category.assoc, he₁]
  · change (_ ≫ (e X P Q).hom) ≫ _ = ((e X' P' Q').hom ≫ _) ≫ _
    rw [Category.assoc, he₂]
    rw [Category.assoc, testMap_comp f (𝟙 X) (prod.map a b) prod.snd,
      Category.comp_id, prod.map_snd]
    have hc := testMap_comp (𝟙 X') f (prod.snd : P' ⨯ Q' ⟶ Q') b
    rw [Category.id_comp] at hc
    rw [← hc, ← Category.assoc, he₂]
    rw [testMap_comp (profiniteProductMap f a) (profiniteProductBase X P) b (𝟙 Q),
      testMap_comp (profiniteProductBase X' P') f (𝟙 Q') b,
      Category.comp_id, Category.id_comp, testMap_snd]

end AlgebraicGeometry.ProEtale
