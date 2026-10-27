module

public import Sheaf.AlgebraicGeometry.SchemeGroupoidLaws
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeNormCharts
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.TensorProduct.Finite
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteFlatNorm
import Mathlib.RingTheory.Ideal.Operations

/-!
# Separating geometric objects by a source norm

Source: Stacks Project, Groupoids, Tag 03BL (`lemma-points`), finite source fibre,
prime avoidance and the two determinant gaps; Divisors, Tag 0BD2, local norm charts
(blueprint: lem-a1-affine-groupoid-norm-prime-separation).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

private theorem point_eq_of_ker_le {k E : Type*} [Field k] [CommRing E] [Algebra k E]
    (f g : E →ₐ[k] k) (h : RingHom.ker f.toRingHom ≤ RingHom.ker g.toRingHom) : f = g := by
  ext x
  have hx : x - algebraMap k E (f x) ∈ RingHom.ker f.toRingHom := by
    simp [RingHom.mem_ker]
  have := h hx
  change g (x - algebraMap k E (f x)) = 0 at this
  have hx : g x - f x = 0 := by simpa using this
  exact (sub_eq_zero.mp hx).symm

private theorem finite_prime_data {k E : Type*} [Field k] [IsAlgClosed k]
    [CommRing E] [Algebra k E] [Module.Finite k E] (P : PrimeSpectrum E) :
    P.asIdeal.IsMaximal ∧ Function.Bijective (algebraMap k P.asIdeal.ResidueField) ∧
      ∃ psi : E →ₐ[k] k, RingHom.ker psi.toRingHom = P.asIdeal := by
  have : IsArtinianRing E := IsArtinianRing.of_finite k E
  have : P.asIdeal.IsMaximal := inferInstance
  have : Module.Finite k P.asIdeal.ResidueField := Module.Finite.trans E _
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)
    (K := P.asIdeal.ResidueField)
  let q : E →ₐ[k] P.asIdeal.ResidueField := IsScalarTower.toAlgHom k E _
  let z := (AlgEquiv.ofBijective (Algebra.ofId k P.asIdeal.ResidueField) hb).symm
  refine ⟨inferInstance, hb, z.toAlgHom.comp q, ?_⟩
  ext x
  change z (algebraMap E P.asIdeal.ResidueField x) = 0 ↔ x ∈ P.asIdeal
  rw [EmbeddingLike.map_eq_zero_iff]
  exact Ideal.algebraMap_residueField_eq_zero

private theorem prime_over_point {k A B : Type*} [Field k] [IsAlgClosed k]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (sigma : A →ₐ[k] B) (hfin : sigma.toRingHom.Finite) (alpha : A →ₐ[k] k)
    (Q : PrimeSpectrum B)
    (hQ : Q.asIdeal.comap sigma.toRingHom = RingHom.ker alpha.toRingHom) :
    ∃ beta : B →ₐ[k] k, beta.comp sigma = alpha ∧
      RingHom.ker beta.toRingHom = Q.asIdeal := by
  let : Algebra A B := sigma.toRingHom.toAlgebra
  have : Module.Finite A B := hfin
  let : Algebra A k := alpha.toRingHom.toAlgebra
  have hscalar (a : A) : algebraMap A (B ⧸ Q.asIdeal) a =
      algebraMap k (B ⧸ Q.asIdeal) (alpha a) := by
    change Ideal.Quotient.mk Q.asIdeal (sigma a) =
      Ideal.Quotient.mk Q.asIdeal (algebraMap k B (alpha a))
    rw [Ideal.Quotient.eq]
    have h : a - algebraMap k A (alpha a) ∈ RingHom.ker alpha.toRingHom := by
      simp [RingHom.mem_ker]
    rw [← hQ] at h
    change sigma (a - algebraMap k A (alpha a)) ∈ Q.asIdeal at h
    simpa only [map_sub, AlgHom.commutes] using h
  have : IsScalarTower A k (B ⧸ Q.asIdeal) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext hscalar)
  have : Module.Finite k (B ⧸ Q.asIdeal) :=
    Module.Finite.of_restrictScalars_finite A k _
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)
    (K := B ⧸ Q.asIdeal)
  let z := (AlgEquiv.ofBijective (Algebra.ofId k (B ⧸ Q.asIdeal)) hb).symm
  let beta := z.toAlgHom.comp (Ideal.Quotient.mkₐ k Q.asIdeal)
  refine ⟨beta, ?_, ?_⟩
  · ext a
    change z (algebraMap A (B ⧸ Q.asIdeal) a) = alpha a
    rw [hscalar]
    exact z.commutes _
  · ext b
    simp [beta, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]


private theorem affine_norm_charts {A B : CommRingCat.{u}} (s : Spec B ⟶ Spec A)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s] (a : B) :
    ∃ g : A,
      (∀ x : Spec A, ∃ V : (Spec A).Opens, x ∈ V ∧ IsAffineOpen V ∧
        (letI := (s.app V).hom.toAlgebra
         Module.Free Γ(Spec A, V) Γ(Spec B, s ⁻¹ᵁ V) ∧
         Module.Finite Γ(Spec A, V) Γ(Spec B, s ⁻¹ᵁ V) ∧
         (Spec A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
             ((Scheme.ΓSpecIso A).inv g) =
           Algebra.norm Γ(Spec A, V)
             ((Spec B).presheaf.map (homOfLE (le_top : s ⁻¹ᵁ V ≤ ⊤)).op
               ((Scheme.ΓSpecIso B).inv a)))) ∧
      ∀ x : Spec A, g ∉ x.asIdeal ↔ ∀ y : Spec B, s y = x → a ∉ y.asIdeal := by
  let aTop := (Scheme.ΓSpecIso B).inv a
  let a' := (Spec B).presheaf.map
    (homOfLE (le_top : s ⁻¹ᵁ ⊤ ≤ ⊤)).op aTop
  obtain ⟨gTop, hg⟩ := exists_finiteLocallyFree_norm_charts s ⊤ a'
  let g := (Scheme.ΓSpecIso A).hom gTop
  have hgcharts (x : Spec A) : ∃ V : (Spec A).Opens, x ∈ V ∧ IsAffineOpen V ∧
      (letI := (s.app V).hom.toAlgebra
       Module.Free Γ(Spec A, V) Γ(Spec B, s ⁻¹ᵁ V) ∧
       Module.Finite Γ(Spec A, V) Γ(Spec B, s ⁻¹ᵁ V) ∧
       (Spec A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op gTop =
         Algebra.norm Γ(Spec A, V)
           ((Spec B).presheaf.map (homOfLE (le_top : s ⁻¹ᵁ V ≤ ⊤)).op aTop)) := by
    obtain ⟨V, hV, hx, haff, hfree, hfinite, heq⟩ := hg x trivial
    refine ⟨V, hx, haff, hfree, hfinite, ?_⟩
    have ha' : a' = aTop := by
      change (Spec B).presheaf.map (𝟙 _) aTop = aTop
      simp
    rw [ha'] at heq
    exact heq
  refine ⟨g, ?_, ?_⟩
  · simpa only [g, Iso.hom_inv_id_apply] using hgcharts
  · intro x
    obtain ⟨V, hx, hV, hfree, hfinite, heq⟩ := hgcharts x
    have hres : x ∈ (Spec A).basicOpen
        ((Spec A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op gTop) ↔
        x ∈ (Spec A).basicOpen gTop := by
      rw [Scheme.basicOpen_res]
      exact and_iff_right hx
    have hcrit := mem_basicOpen_normAt_of_free s hV hfree
      ((Spec B).presheaf.map (homOfLE (le_top : s ⁻¹ᵁ V ≤ ⊤)).op aTop) hx
    change (x ∈ (Spec A).basicOpen
      (letI := (s.app V).hom.toAlgebra; Algebra.norm Γ(Spec A, V) _) ↔ _) at hcrit
    rw [← heq, hres] at hcrit
    rw [basicOpen_eq_of_affine'] at hcrit
    change (g ∉ x.asIdeal ↔ _) at hcrit
    refine hcrit.trans ?_
    simp only [Scheme.basicOpen_res, aTop, basicOpen_eq_of_affine]
    constructor
    · intro h y hy
      exact (h y hy).2
    · intro h y hy
      exact ⟨by change s y ∈ V; rw [hy]; exact hx, h y hy⟩

/-- The source fibre has finitely many geometric points, and a target function separating
those points from another object has a source norm separating the two objects.

Source: Stacks Project, Groupoids, Tag 03BL, finite source-fibre and separating-norm
paragraph; Divisors, Tag 0BD2
(blueprint: lem-a1-affine-groupoid-norm-prime-separation).

The two ring-map equations express that `s` and `t` are k-morphisms. The groupoid laws
then imply that identity, inverse and composition are k-morphisms as well. The fibre is
written `k ⊗[A] B`, the commuted form of `B ⊗[A] k`. Its two A-actions are precisely
`alpha₁` and `s`-sharp, installed by `letI`. The equivalence of its prime spectrum with
source-fibre arrows is required to respect the unique k-point with that prime kernel,
including its evaluation on every `1 ⊗ b`. The residue-field
map is the structural map followed by `Scheme.Spec.residueFieldIso.inv`, so bijectivity asserts
that the scheme residue field is canonically k. The identity witness is explicitly the
composite of `alpha₁` with `e`-sharp. The section `g` is specified by its actual local
multiplication determinants, with no global freeness assumption.

Proof:
1. Finiteness of s makes B a finite A-module. Tensor a finite generating set with k to
   obtain a finite spanning set of the fibre. The affine tensor-product pullback formula
   identifies its spectrum with the scheme source fibre, which is finite. This uses
   def-pc-finite-locally-free, def-weil-finite-integral-morphism,
   lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-finite-morphism-permanence,
   and lem-weil-pbc-finite-closed-map-finite-fibres.
2. For each prime P of the fibre the quotient is a finite-dimensional domain over k,
   hence a field by lem-weil-pbc-finite-dimensional-domain-is-field. Thus P is maximal.
   The structural map from the algebraically closed field k to this finite extension is
   bijective by lem-pc-finite-extension-alg-closed. Its unique inverse gives the unique
   k-point with kernel P. Tensor universality identifies these points with beta satisfying
   beta sigma = alpha₁. The identity alpha₁ e-sharp is one such beta.
3. If no target beta tau is alpha₀, choose for each beta an element distinguishing the
   two maps and subtract its alpha₀-value. This lies in ker alpha₀ but not ker(beta tau).
   These kernels are maximal because k-algebra maps to k are surjective. Apply
   lem-weil-pbc-prime-avoidance to obtain f vanishing at alpha₀ and at none of the targets.
4. Apply lem-pd-finite-locally-free-norm-charts to tau(f) over the whole object scheme.
   On a chart about ker alpha₁, primes over that point are exactly the fibre points of
   step 2, and tau(f) is nonzero at all of them. By
   lem-pd-finite-free-norm-prime-criterion the chart determinant is nonzero at alpha₁.
5. On a chart about ker alpha₀, its identity arrow lies over alpha₀ and evaluates tau(f)
   to alpha₀(f) = 0. The same norm-prime criterion gives alpha₀(g) = 0. The two charts
   can have different ranks. This argument uses neither reducedness nor equality on
   invariant functions, and permits repeated targets and nontrivial stabilizers. -/
theorem affineGroupoid_norm_prime_separation
    (k : Type v) [Field k] [IsAlgClosed k]
    (A B : CommRingCat.{u}) [Algebra k A] [Algebra k B]
    (s t : Spec B ⟶ Spec A) (e : Spec A ⟶ Spec B) (i : Spec B ⟶ Spec B)
    (c : pullback s t ⟶ Spec B) (hG : Scheme.IsGroupoid s t e i c)
    [s.IsFiniteLocallyFree] [t.IsFiniteLocallyFree]
    (hs : (Spec.preimage s).hom.comp (algebraMap k A) = algebraMap k B)
    (ht : (Spec.preimage t).hom.comp (algebraMap k A) = algebraMap k B)
    (alpha₁ : A →ₐ[k] k) :
    letI := (Spec.preimage s).hom.toAlgebra
    letI := alpha₁.toRingHom.toAlgebra
    FiniteDimensional k (k ⊗[A] B) ∧
    (∀ P : PrimeSpectrum (k ⊗[A] B), P.asIdeal.IsMaximal ∧
      Function.Bijective
        ((Scheme.Spec.residueFieldIso (CommRingCat.of (k ⊗[A] B)) P).inv.hom.comp
          ((algebraMap (k ⊗[A] B) P.asIdeal.ResidueField).comp
            (algebraMap k (k ⊗[A] B))))) ∧
    (∃ φ : PrimeSpectrum (k ⊗[A] B) ≃
      {beta : B →ₐ[k] k //
        beta.toRingHom.comp (Spec.preimage s).hom = alpha₁.toRingHom},
      ∀ P : PrimeSpectrum (k ⊗[A] B), ∃! psi : (k ⊗[A] B) →ₐ[k] k,
        RingHom.ker psi.toRingHom = P.asIdeal ∧
        ∀ b : B, psi (1 ⊗ₜ[A] b) = (φ P).val b) ∧
    Finite {beta : B →ₐ[k] k //
      beta.toRingHom.comp (Spec.preimage s).hom = alpha₁.toRingHom} ∧
    (∃ beta : B →ₐ[k] k,
      beta.toRingHom.comp (Spec.preimage s).hom = alpha₁.toRingHom ∧
      beta.toRingHom = alpha₁.toRingHom.comp (Spec.preimage e).hom) ∧
    ∀ alpha₀ : A →ₐ[k] k,
      (∀ beta : B →ₐ[k] k,
        beta.toRingHom.comp (Spec.preimage s).hom = alpha₁.toRingHom →
        beta.toRingHom.comp (Spec.preimage t).hom ≠ alpha₀.toRingHom) →
      ∃ f g : A,
        alpha₀ f = 0 ∧
        (∀ beta : B →ₐ[k] k,
          beta.toRingHom.comp (Spec.preimage s).hom = alpha₁.toRingHom →
          beta ((Spec.preimage t).hom f) ≠ 0) ∧
        (∀ x : Spec A, ∃ V : (Spec A).Opens, x ∈ V ∧ IsAffineOpen V ∧
          (letI := (s.app V).hom.toAlgebra
           Module.Free Γ(Spec A, V) Γ(Spec B, s ⁻¹ᵁ V) ∧
           Module.Finite Γ(Spec A, V) Γ(Spec B, s ⁻¹ᵁ V) ∧
           (Spec A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
               ((Scheme.ΓSpecIso A).inv g) =
             Algebra.norm Γ(Spec A, V)
               ((Spec B).presheaf.map (homOfLE (le_top : s ⁻¹ᵁ V ≤ ⊤)).op
                 ((Scheme.ΓSpecIso B).inv ((Spec.preimage t).hom f))))) ∧
        alpha₀ g = 0 ∧ alpha₁ g ≠ 0 := by
  classical
  let sigma : A →ₐ[k] B := ⟨(Spec.preimage s).hom, RingHom.congr_fun hs⟩
  let tau : A →ₐ[k] B := ⟨(Spec.preimage t).hom, RingHom.congr_fun ht⟩
  have hfin : sigma.toRingHom.Finite := by
    apply (IsFinite.SpecMap_iff (Spec.preimage s)).mp
    simpa using (inferInstance : IsFinite s)
  have hid : (Spec.preimage e).hom.comp sigma.toRingHom = RingHom.id A := by
    have h := congrArg (fun f ↦ (Spec.preimage f).hom) hG.source_id
    rw [Spec.preimage_comp, Spec.preimage_id] at h
    exact h
  have htid : (Spec.preimage e).hom.comp tau.toRingHom = RingHom.id A := by
    have h := congrArg (fun f ↦ (Spec.preimage f).hom) hG.target_id
    rw [Spec.preimage_comp, Spec.preimage_id] at h
    exact h
  let epsilon : B →ₐ[k] A :=
    ⟨(Spec.preimage e).hom, fun r ↦ by
      rw [← RingHom.congr_fun hs r]
      exact RingHom.congr_fun hid (algebraMap k A r)⟩
  have hepsilon : epsilon.comp sigma = AlgHom.id k A := AlgHom.ext (RingHom.congr_fun hid)
  have htepsilon : epsilon.comp tau = AlgHom.id k A := AlgHom.ext (RingHom.congr_fun htid)
  let := sigma.toRingHom.toAlgebra
  let := alpha₁.toRingHom.toAlgebra
  have : Module.Finite A B := hfin
  have : FiniteDimensional k (k ⊗[A] B) := inferInstance
  let E := k ⊗[A] B
  have : IsArtinianRing E := IsArtinianRing.of_finite k E
  have hcomm (a : A) : (Algebra.TensorProduct.includeRight : B →ₐ[A] E) (sigma a) =
      algebraMap k E (alpha₁ a) := by
    exact (RingHom.congr_fun
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := A) (A := k) (B := B))
      a).symm
  let rho : B →ₐ[k] E :=
    { (Algebra.TensorProduct.includeRight : B →ₐ[A] E).toRingHom with
      commutes' r := by
        change (Algebra.TensorProduct.includeRight : B →ₐ[A] E) (algebraMap k B r) = _
        rw [← sigma.commutes r, hcomm, alpha₁.commutes]
        rfl }
  let T := {beta : B →ₐ[k] k // beta.toRingHom.comp sigma.toRingHom = alpha₁.toRingHom}
  let res : (E →ₐ[k] k) → T := fun psi ↦
    ⟨psi.comp rho, RingHom.ext fun a ↦ by
      change psi (rho (sigma a)) = alpha₁ a
      rw [show rho (sigma a) = algebraMap k E (alpha₁ a) from hcomm a]
      exact psi.commutes _⟩
  have hres : Function.Bijective res := by
    constructor
    · intro psi chi h
      apply Algebra.TensorProduct.ext (Subsingleton.elim _ _)
      ext b
      exact congrArg (fun z : T ↦ z.val b) h
    · intro beta
      let bA : B →ₐ[A] k :=
        ⟨beta.val.toRingHom, RingHom.congr_fun beta.property⟩
      refine ⟨(AlgHom.liftEquiv A k B k) bA, ?_⟩
      apply Subtype.ext
      ext b
      change ((AlgHom.liftEquiv A k B k) bA) (1 ⊗ₜ[A] b) = beta.val b
      simp [bA]
  let kerPoint : (E →ₐ[k] k) → PrimeSpectrum E :=
    fun psi ↦ ⟨RingHom.ker psi.toRingHom, RingHom.ker_isPrime _⟩
  have hker : Function.Bijective kerPoint := by
    constructor
    · intro psi chi h
      apply point_eq_of_ker_le psi chi
      exact le_of_eq (congrArg PrimeSpectrum.asIdeal h)
    · intro P
      obtain ⟨psi, hpsi⟩ := (finite_prime_data (k := k) P).2.2
      exact ⟨psi, PrimeSpectrum.ext hpsi⟩
  let pointEquiv := (Equiv.ofBijective kerPoint hker).symm
  let phi := pointEquiv.trans (Equiv.ofBijective res hres)
  have hphi : ∀ P : PrimeSpectrum E, ∃! psi : E →ₐ[k] k,
      RingHom.ker psi.toRingHom = P.asIdeal ∧
      ∀ b : B, psi (1 ⊗ₜ[A] b) = (phi P).val b := by
    intro P
    refine ⟨pointEquiv P, ⟨?_, fun _ ↦ rfl⟩, ?_⟩
    · exact congrArg PrimeSpectrum.asIdeal ((Equiv.ofBijective kerPoint hker).apply_symm_apply P)
    · intro psi hpsi
      apply point_eq_of_ker_le psi (pointEquiv P)
      rw [hpsi.1]
      exact le_of_eq (congrArg PrimeSpectrum.asIdeal
        ((Equiv.ofBijective kerPoint hker).apply_symm_apply P)).symm
  have : Finite T := Finite.of_equiv (PrimeSpectrum E) phi
  refine ⟨inferInstance, ?_, ⟨phi, hphi⟩, inferInstance, ?_, ?_⟩
  · intro P
    obtain ⟨hmax, hb, -⟩ := finite_prime_data (k := k) P
    refine ⟨hmax, ?_⟩
    exact (ConcreteCategory.bijective_of_isIso
      (Scheme.Spec.residueFieldIso (CommRingCat.of E) P).inv).comp hb
  · refine ⟨alpha₁.comp epsilon, ?_, rfl⟩
    exact RingHom.ext fun a ↦ congrArg alpha₁ (RingHom.congr_fun hid a)
  · intro alpha₀ hnone
    let betaId : T := ⟨alpha₁.comp epsilon,
      RingHom.ext fun a ↦ congrArg alpha₁ (RingHom.congr_fun hid a)⟩
    let := Fintype.ofFinite T
    let J : T → Ideal A := fun beta ↦ RingHom.ker (beta.val.comp tau).toRingHom
    have havoid : ¬ ((RingHom.ker alpha₀.toRingHom : Set A) ⊆
        ⋃ beta ∈ (↑(Finset.univ : Finset T) : Set T), (J beta : Set A)) := by
      intro h
      obtain ⟨beta, -, hle⟩ := (Ideal.subset_union_prime betaId betaId
        (fun beta _ _ _ ↦ RingHom.ker_isPrime (beta.val.comp tau).toRingHom)).mp h
      have heq := point_eq_of_ker_le alpha₀ (beta.val.comp tau) hle
      exact hnone beta.val beta.property (congrArg AlgHom.toRingHom heq.symm)
    obtain ⟨f, hf₀, hf⟩ := Set.not_subset.mp havoid
    have hfβ (beta : B →ₐ[k] k)
        (hb : beta.toRingHom.comp sigma.toRingHom = alpha₁.toRingHom) : beta (tau f) ≠ 0 := by
      intro hz
      apply hf
      exact Set.mem_iUnion₂.mpr ⟨⟨beta, hb⟩, Finset.mem_univ _, hz⟩
    obtain ⟨g, hcharts, hg⟩ := affine_norm_charts s (tau f)
    refine ⟨f, g, hf₀, hfβ, hcharts, ?_, ?_⟩
    · let x₀ : Spec A := ⟨RingHom.ker alpha₀.toRingHom, RingHom.ker_isPrime _⟩
      let b₀ := alpha₀.comp epsilon
      let y₀ : Spec B := ⟨RingHom.ker b₀.toRingHom, RingHom.ker_isPrime _⟩
      have hsy : s y₀ = x₀ := by
        rw [← Spec.map_preimage s, Spec.map_apply]
        apply PrimeSpectrum.ext
        ext a
        change alpha₀ (epsilon (sigma a)) = 0 ↔ alpha₀ a = 0
        rw [show epsilon (sigma a) = a from DFunLike.congr_fun hepsilon a]
      have hzero : tau f ∈ y₀.asIdeal := by
        change alpha₀ (epsilon (tau f)) = 0
        rw [show epsilon (tau f) = f from DFunLike.congr_fun htepsilon f]
        exact hf₀
      by_contra hn
      exact (hg x₀).mp hn y₀ hsy hzero
    · let x₁ : Spec A := ⟨RingHom.ker alpha₁.toRingHom, RingHom.ker_isPrime _⟩
      apply (hg x₁).mpr
      intro y hy
      have hy' : y.asIdeal.comap sigma.toRingHom = RingHom.ker alpha₁.toRingHom := by
        rw [← Spec.map_preimage s, Spec.map_apply] at hy
        exact congrArg PrimeSpectrum.asIdeal hy
      obtain ⟨beta, hb, hker⟩ := prime_over_point sigma hfin alpha₁ y hy'
      rw [← hker]
      exact hfβ beta (congrArg AlgHom.toRingHom hb)

end AlgebraicGeometry
