/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.Unramified.LocalStructure
public import WeilConjectures.AlgebraicGeometry.SchemeFrobenius

/-!
# Fixed points of a Frobenius twisted by an endomorphism

Let `k` be a finite field with `q` elements, `f : X ⟶ Spec k` separated, quasi-compact and
locally of finite type, `g : X ⟶ X` an endomorphism over `k` and `M ≥ 1`. The endomorphism
`Ψ = g ≫ Fr^{(q^M)}` has the differential of the Frobenius, which is zero, so its fixed-point
scheme `Fix(Ψ) = X ×_{X ×_k X} X` is unramified over `k`, hence finite over `k`. In particular,
for every field `K` over `k`, only finitely many `K`-points `x` of `X` satisfy `x ≫ Ψ = x`
(`AlgebraicGeometry.Scheme.Hom.finite_fixedPoints_comp_absoluteFrobenius`).

That `Fix(Ψ)` is formally unramified over `k` is checked on points
(`AlgebraicGeometry.FormallyUnramified.of_hom_ext`): for a ring `R` of characteristic `p` and a
square-zero ideal `I ⊆ R`, the `q^M`-power map of `R` factors through `R / I`, so two
`R`-points of `Fix(Ψ)` which agree modulo `I` agree.

## Main statements

- `AlgebraicGeometry.LocallyQuasiFinite.of_formallyUnramified`: a formally unramified morphism
  locally of finite type is locally quasi-finite.
- `AlgebraicGeometry.Scheme.Hom.finite_fixedPoints_comp_absoluteFrobenius`: finiteness of the
  fixed points of `g ≫ Fr^{(q^M)}`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A formally unramified morphism locally of finite type is locally quasi-finite: on affine
opens, a formally unramified algebra of finite type is quasi-finite. -/
instance (priority := low) LocallyQuasiFinite.of_formallyUnramified {X Y : Scheme.{u}}
    (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f] : LocallyQuasiFinite f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have h₁ := f.formallyUnramified_appLE U.2 V.2 e
  have h₂ := HasRingHomProperty.appLE @LocallyOfFiniteType f ‹_› U V e
  algebraize [(f.appLE U V e).hom]
  exact RingHom.quasiFinite_algebraMap.mpr inferInstance

/-- In a ring `R` with `p = 0`, the `p ^ n`-power map, `n ≥ 1`, factors through every surjection
`φ : R ⟶ S` with square-zero kernel. -/
lemma exists_comp_eq_iterateFrobeniusOfPrime {R S : CommRingCat.{u}} {p : ℕ} (hp : p.Prime)
    (hR : (p : R) = 0) (φ : R ⟶ S) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ.hom ^ 2 = ⊥) {n : ℕ} (hn : n ≠ 0) :
    ∃ ψ : S ⟶ R, φ ≫ ψ = CommRingCat.ofHom (iterateFrobeniusOfPrime R hp hR n) := by
  have hle : RingHom.ker φ.hom ≤ RingHom.ker (iterateFrobeniusOfPrime R hp hR n) := by
    intro r hr
    have hr2 : r ^ 2 = 0 := by
      have : r ^ 2 ∈ RingHom.ker φ.hom ^ 2 := Ideal.pow_mem_pow hr 2
      rwa [hker, Ideal.mem_bot] at this
    have h2 : 2 ≤ p ^ n :=
      (hp.two_le.trans (Nat.le_self_pow hn p))
    rw [RingHom.mem_ker, iterateFrobeniusOfPrime_apply]
    exact pow_eq_zero_of_le h2 hr2
  refine ⟨CommRingCat.ofHom (RingHom.liftOfRightInverse φ.hom (Function.surjInv hφ)
    (Function.rightInverse_surjInv hφ) ⟨_, hle⟩), ?_⟩
  ext r
  exact congrArg (fun g : R →+* R ↦ g r) (RingHom.liftOfRightInverse_comp φ.hom _ _ ⟨_, hle⟩)

namespace Scheme.Hom

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The absolute `q ^ M`-power Frobenius of a scheme over a finite field with `q` elements is a
Frobenius for the exponent `q ^ M`. -/
lemma isFrobenius_absoluteFrobenius [Finite k] (M : ℕ) :
    (f.absoluteFrobenius M).IsFrobenius (Nat.card k ^ M) := by
  have h := X.isFrobenius_iterateFrobenius FiniteField.ringChar_prime
    f.natCast_ringChar_eq_zero (Nat.log (ringChar k) (Nat.card k) * M)
  rwa [pow_mul, FiniteField.ringChar_pow_log_card] at h

section FixedPoints

variable (Ψ : X ⟶ X) (hΨ : Ψ ≫ f = f)

/-- The graph `(𝟙, Ψ) : X ⟶ X ×_k X` of an endomorphism `Ψ` of `X` over `k`. -/
noncomputable def graphOver : X ⟶ pullback f f :=
  pullback.lift (𝟙 X) Ψ (by simp [hΨ])

/-- The fixed-point scheme `Fix(Ψ) = X ×_{X ×_k X} X` of an endomorphism `Ψ` of `X` over `k`:
the pullback of the diagonal of `f` along the graph of `Ψ`. -/
noncomputable def fixedPointScheme : Scheme.{u} :=
  pullback (pullback.diagonal f) (graphOver f Ψ hΨ)

/-- The inclusion `Fix(Ψ) ⟶ X`. -/
noncomputable def fixedPointSchemeι : fixedPointScheme f Ψ hΨ ⟶ X :=
  pullback.snd _ _

@[reassoc]
lemma fixedPointSchemeι_comp : fixedPointSchemeι f Ψ hΨ ≫ Ψ = fixedPointSchemeι f Ψ hΨ := by
  have h := pullback.condition (f := pullback.diagonal f) (g := graphOver f Ψ hΨ)
  have h₁ := congrArg (· ≫ pullback.fst f f) h
  have h₂ := congrArg (· ≫ pullback.snd f f) h
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, graphOver,
    pullback.lift_fst, pullback.lift_snd, Category.comp_id] at h₁ h₂
  exact (h₂.symm.trans h₁).trans rfl

/-- A morphism `t : T ⟶ X` fixed by `Ψ` factors through `Fix(Ψ)`. -/
noncomputable def fixedPointSchemeLift {T : Scheme.{u}} (t : T ⟶ X) (ht : t ≫ Ψ = t) :
    T ⟶ fixedPointScheme f Ψ hΨ :=
  pullback.lift t t (by ext <;> simp [graphOver, ht])

@[reassoc (attr := simp)]
lemma fixedPointSchemeLift_ι {T : Scheme.{u}} (t : T ⟶ X) (ht : t ≫ Ψ = t) :
    fixedPointSchemeLift f Ψ hΨ t ht ≫ fixedPointSchemeι f Ψ hΨ = t :=
  pullback.lift_snd _ _ _

instance : Mono (fixedPointSchemeι f Ψ hΨ) := by
  unfold fixedPointSchemeι fixedPointScheme
  infer_instance

instance [IsSeparated f] : IsClosedImmersion (fixedPointSchemeι f Ψ hΨ) := by
  unfold fixedPointSchemeι fixedPointScheme
  infer_instance

end FixedPoints

section TwistedFrobenius

variable [Finite k] (g : X ⟶ X) (hg : g ≫ f = f) {M : ℕ}

include hg

lemma comp_absoluteFrobenius_comp : (g ≫ f.absoluteFrobenius M) ≫ f = f := by
  rw [Category.assoc, absoluteFrobenius_comp, hg]

/-- The fixed-point scheme of `g ≫ Fr^{(q^M)}`, `M ≥ 1`, is formally unramified over `k`. -/
lemma formallyUnramified_fixedPointScheme_comp_absoluteFrobenius (hM : M ≠ 0) :
    FormallyUnramified
      (fixedPointSchemeι f _ (comp_absoluteFrobenius_comp f g hg (M := M)) ≫ f) := by
  set Ψ := g ≫ f.absoluteFrobenius M
  set ι := fixedPointSchemeι f Ψ (comp_absoluteFrobenius_comp f g hg (M := M))
  refine FormallyUnramified.of_hom_ext _ fun R S φ hφ hker g₁ g₂ h₁ h₂ ↦ ?_
  rw [← cancel_mono ι]
  set p := ringChar k
  have hp : p.Prime := FiniteField.ringChar_prime
  have hR' : (p : Γ(Spec R, ⊤)) = 0 := (g₁ ≫ ι ≫ f).natCast_ringChar_eq_zero
  have hR : (p : R) = 0 := by
    rw [← map_natCast (Scheme.ΓSpecIso R).hom.hom, hR', map_zero]
  have hlog : Nat.log p (Nat.card k) ≠ 0 := by
    intro h0
    have := FiniteField.ringChar_pow_log_card (k := k)
    rw [h0, pow_zero] at this
    exact (Finite.one_lt_card (α := k)).ne' this.symm
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_iterateFrobeniusOfPrime hp hR φ hφ hker
    (Nat.mul_ne_zero hlog hM)
  have hfix (t : Spec R ⟶ X) (ht : t ≫ Ψ = t) :
      t = Spec.map ψ ≫ Spec.map φ ≫ t ≫ g := by
    have hF := f.isFrobenius_absoluteFrobenius M (t ≫ g)
      (CommRingCat.ofHom (iterateFrobeniusOfPrime R hp hR (Nat.log p (Nat.card k) * M)))
      (fun r ↦ by
        rw [CommRingCat.hom_ofHom, iterateFrobeniusOfPrime_apply, pow_mul,
          FiniteField.ringChar_pow_log_card])
    rw [← Spec.map_comp_assoc, hψ, ← hF, Category.assoc]
    exact ht.symm
  have e₁ := fixedPointSchemeι_comp f Ψ (comp_absoluteFrobenius_comp f g hg (M := M))
  rw [hfix (g₁ ≫ ι) (by rw [Category.assoc, e₁]), hfix (g₂ ≫ ι) (by rw [Category.assoc, e₁]),
    Category.assoc, Category.assoc, reassoc_of% h₁]


/-- **Finiteness of the fixed points of a twisted Frobenius**: for a separated scheme `X` of
finite type over a finite field `k` with `q` elements, an endomorphism `g` of `X` over `k`,
`M ≥ 1` and a field `K` with a morphism `s : Spec K ⟶ Spec k`, there are only finitely many
`K`-points `x` of `X` over `s` fixed by `g ≫ Fr^{(q^M)}`: they factor through the fixed-point
scheme, which is unramified, hence finite, over `k`. -/
theorem finite_fixedPoints_comp_absoluteFrobenius [IsSeparated f] [QuasiCompact f]
    [LocallyOfFiniteType f] (hM : M ≠ 0) (K : Type u) [Field K]
    (s : Spec (.of K) ⟶ Spec (.of k)) :
    Finite {x : Spec (.of K) ⟶ X // x ≫ f = s ∧ x ≫ g ≫ f.absoluteFrobenius M = x} := by
  set Ψ := g ≫ f.absoluteFrobenius M
  have hΨ := comp_absoluteFrobenius_comp f g hg (M := M)
  set E := fixedPointScheme f Ψ hΨ
  set h : E ⟶ Spec (.of k) := fixedPointSchemeι f Ψ hΨ ≫ f
  have := formallyUnramified_fixedPointScheme_comp_absoluteFrobenius f g hg hM
  have : IsLocallyArtinian (Spec (.of k)) :=
    Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  have : IsFinite h := IsFinite.of_locallyQuasiFinite h
  have : IsAffine E := isAffine_of_isAffineHom h
  let := h.appTop.hom.toAlgebra
  let : Algebra Γ(Spec (.of k), ⊤) K :=
    (s.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom.toAlgebra
  have : Module.Finite Γ(Spec (.of k), ⊤) Γ(E, ⊤) := h.finite_appTop
  have hlift (x : {x : Spec (.of K) ⟶ X // x ≫ f = s ∧ x ≫ Ψ = x}) :
      fixedPointSchemeLift f Ψ hΨ x.1 x.2.2 ≫ h = s := by
    simp only [h, fixedPointSchemeLift_ι_assoc, x.2.1]
  let F (x : {x : Spec (.of K) ⟶ X // x ≫ f = s ∧ x ≫ Ψ = x}) :
      Γ(E, ⊤) →ₐ[Γ(Spec (.of k), ⊤)] K :=
    { toRingHom := ((fixedPointSchemeLift f Ψ hΨ x.1 x.2.2).appTop ≫
        (Scheme.ΓSpecIso (.of K)).hom).hom
      commutes' := fun r ↦ by
        have e := congrArg (fun t ↦ (t.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom r) (hlift x)
        simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at e
        exact e }
  refine Finite.of_injective F fun x y hxy ↦ Subtype.ext ?_
  have e : (fixedPointSchemeLift f Ψ hΨ x.1 x.2.2).appTop =
      (fixedPointSchemeLift f Ψ hΨ y.1 y.2.2).appTop := by
    rw [← cancel_mono (Scheme.ΓSpecIso (.of K)).hom]
    exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom hxy)
  have := congrArg (· ≫ fixedPointSchemeι f Ψ hΨ) (ext_of_isAffine e)
  simpa using this
end TwistedFrobenius

end Scheme.Hom

end AlgebraicGeometry
