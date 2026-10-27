module

public import Sheaf.RepresentationTheory.TopologicalHomogeneousCochainCoordinates
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Finite-coset averaging on jointly continuous homogeneous cochains

Source: the arithmetic expansion of direct-images paragraph (3),
`sec-six-functors-basics/sk-thm-sf-ctf-stability`, finite-coset transfer steps 1--9.
(blueprint: lem-sfb-finite-coset-homogeneous-averaging).

We use `JointContinuousCochainCoordinates` for the abstract vector-space complexes:
its injective evaluations have exactly the jointly continuous equivariant functions
as image, its differential is alternating omission, and its negative terms are zero.
The auxiliary inhomogeneous complex in that interface plays no role here. All results
hold for every realization of that interface, so no function-space topology is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u v w w' t r

open CategoryTheory CategoryTheory.Limits

namespace ContinuousCohomology

variable {G : Type v} [Group G]

/-- The canonical H-coordinate of x in the unique decomposition x = h s for a
right transversal S. This is actual subgroup-valued data from Mathlib's coset
representative, independent of all coefficient spaces.
Source: arithmetic transfer expansion of direct-images (3), step 3.
(blueprint: lem-sfb-finite-coset-homogeneous-averaging). -/
noncomputable def finiteCosetRetraction (H : Subgroup G) (S : Finset G)
    (hS : Subgroup.IsComplement (H : Set G) (S : Set G)) (x : G) : H :=
  ⟨x * (hS.toRightFun x : G)⁻¹, hS.mul_inv_toRightFun_mem x⟩

/-- The map a_s(x) = s⁻¹ r(sx), with the subgroup included into G.
Source: arithmetic transfer expansion of direct-images (3), step 4.
(blueprint: lem-sfb-finite-coset-homogeneous-averaging). -/
noncomputable def finiteCosetArgument (H : Subgroup G) (S : Finset G)
    (hS : Subgroup.IsComplement (H : Set G) (S : Set G)) (s x : G) : G :=
  s⁻¹ * (finiteCosetRetraction H S hS (s * x) : G)

/-- A compact group has a finite right transversal for every open subgroup, normalized
at the identity, of cardinality the subgroup index.
Source: arithmetic transfer expansion of direct-images (3), step 2.
(blueprint: lem-sfb-finite-coset-homogeneous-averaging).

Proof: right translates of the open subgroup form an open cover. Compactness gives
finitely many cosets covering G. Intersecting cosets coincide, so remove repetitions
and choose representatives, choosing 1 for H. Inversion identifies right and left
cosets, giving cardinality [G:H]. -/
theorem exists_finiteRightTransversal [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    ∃ S : Finset G, 1 ∈ S ∧ S.card = H.index ∧
      Subgroup.IsComplement (H : Set G) (S : Set G) := by
  classical
  have : Finite (G ⧸ H) := H.quotient_finite_of_isOpen hH
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨S, hS, h1⟩ := H.exists_isComplement_right 1
  refine ⟨hS.finite_right.toFinset, by simpa using h1, ?_, ?_⟩
  · simpa only [← Set.ncard_eq_toFinset_card] using hS.ncard_right
  · simpa using hS

private theorem coset_rep_eq (H : Subgroup G) (S : Finset G)
    (hS : Subgroup.IsComplement (H : Set G) (S : Set G)) (x : G) (s : S)
    (hx : x * (s : G)⁻¹ ∈ H) : hS.toRightFun x = s := by
  exact (Subgroup.isComplement_iff_existsUnique_mul_inv_mem.mp hS x).unique
    (hS.mul_inv_toRightFun_mem x) hx

private theorem coset_retraction_eq (H : Subgroup G) (S : Finset G)
    (hS : Subgroup.IsComplement (H : Set G) (S : Set G)) (x : G) (s : S)
    (hx : x * (s : G)⁻¹ ∈ H) :
    (finiteCosetRetraction H S hS x : G) = x * (s : G)⁻¹ := by
  simp only [finiteCosetRetraction, coset_rep_eq H S hS x s hx]

private theorem coset_retraction_mul (H : Subgroup G) (S : Finset G)
    (hS : Subgroup.IsComplement (H : Set G) (S : Set G)) (h : H) (x : G) :
    finiteCosetRetraction H S hS ((h : G) * x) = h * finiteCosetRetraction H S hS x := by
  apply Subtype.ext
  rw [coset_retraction_eq H S hS _ (hS.toRightFun x)
    (by simpa only [mul_assoc] using H.mul_mem h.property (hS.mul_inv_toRightFun_mem x))]
  simp [finiteCosetRetraction, mul_assoc]

private theorem coset_retraction_continuous [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) (hH : IsOpen (H : Set G)) (S : Finset G)
    (hS : Subgroup.IsComplement (H : Set G) (S : Set G)) :
    Continuous (finiteCosetRetraction H S hS) := by
  apply continuous_induced_rng.mpr
  apply continuous_iff_continuousAt.mpr
  intro x
  let s := hS.toRightFun x
  have ho : IsOpen {y : G | y * (s : G)⁻¹ ∈ H} :=
    hH.preimage (continuous_id.mul continuous_const)
  have hn := ho.mem_nhds (hS.mul_inv_toRightFun_mem x)
  apply (continuous_id.mul continuous_const :
    Continuous (fun y : G ↦ y * (s : G)⁻¹)).continuousAt.congr_of_eventuallyEq
  filter_upwards [hn] with y hy
  exact coset_retraction_eq H S hS y s hy

/-- For any normalized finite right transversal, the retraction is uniquely determined,
continuous, H-equivariant, and the identity on H. The continuous maps a_s obey the
specified permutation identity under every left translation of their argument.
Source: arithmetic transfer expansion of direct-images (3), steps 3--4.
(blueprint: lem-sfb-finite-coset-homogeneous-averaging).

Proof: on the open coset Hs the retraction is x ↦ xs⁻¹. For an open U in H its
inverse image is the union of Us, hence open. Uniqueness of x = hs proves uniqueness
of r, r(hx) = hr(x), and r|H = id. Right multiplication by a permutes right cosets,
with inverse right multiplication by a⁻¹. If u represents Hsa, write sa = h_s u.
Then r(sax) = h_s r(ux), and s⁻¹ h_s = a u⁻¹ gives a_s(ax) = a a_u(x).
Continuity of a_s follows by translations, continuity of r, and the inclusion of H. -/
theorem finiteCosetRetraction_properties [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) (hH : IsOpen (H : Set G)) (S : Finset G)
    (hS : Subgroup.IsComplement (H : Set G) (S : Set G)) (h1 : 1 ∈ S) :
    Continuous (finiteCosetRetraction H S hS) ∧
    (∀ x : G, x = (finiteCosetRetraction H S hS x : G) * (hS.toRightFun x : G)) ∧
    (∀ r' : G → H, (∀ x : G, ∃ s : S, x = (r' x : G) * (s : G)) →
      r' = finiteCosetRetraction H S hS) ∧
    (∀ (h : H) (x : G),
      finiteCosetRetraction H S hS ((h : G) * x) = h * finiteCosetRetraction H S hS x) ∧
    (∀ h : H, finiteCosetRetraction H S hS h = h) ∧
    (∀ s : S, Continuous (finiteCosetArgument H S hS s)) ∧
    (∀ a : G, ∃ π : Equiv.Perm S,
      (∀ s : S, (s : G) * a * (π s : G)⁻¹ ∈ H) ∧
      ∀ (s : S) (x : G),
        finiteCosetArgument H S hS s (a * x) = a * finiteCosetArgument H S hS (π s) x) := by
  classical
  have hmul := coset_retraction_mul H S hS
  have hcont := coset_retraction_continuous H hH S hS
  refine ⟨hcont, ?_, ?_, hmul, ?_, ?_, ?_⟩
  · intro x
    simp [finiteCosetRetraction]
  · intro r' hr
    funext x
    obtain ⟨s, hs⟩ := hr x
    apply Subtype.ext
    rw [coset_retraction_eq H S hS x s (by rw [hs]; simp)]
    exact eq_mul_inv_iff_mul_eq.mpr hs.symm
  · intro h
    apply Subtype.ext
    simpa using coset_retraction_eq H S hS h ⟨1, h1⟩ (by simp)
  · intro s
    exact continuous_const.mul
      (continuous_subtype_val.comp (hcont.comp (continuous_const.mul continuous_id)))
  · intro a
    let p : S → S := fun s ↦ hS.toRightFun ((s : G) * a)
    have hp (s : S) : (s : G) * a * (p s : G)⁻¹ ∈ H :=
      hS.mul_inv_toRightFun_mem _
    have hinj : Function.Injective p := by
      intro s t hst
      have hm := H.mul_mem (hp s) (H.inv_mem (hp t))
      have hmem : (s : G) * (t : G)⁻¹ ∈ H := by
        simpa [hst, mul_assoc] using hm
      have hs := coset_rep_eq H S hS (s : G) s (by simp)
      have ht := coset_rep_eq H S hS (s : G) t hmem
      exact hs.symm.trans ht
    let π : Equiv.Perm S := Equiv.ofBijective p
      ⟨hinj, (Finite.injective_iff_surjective).mp hinj⟩
    refine ⟨π, hp, ?_⟩
    intro s x
    let h : H := ⟨(s : G) * a * (π s : G)⁻¹, hp s⟩
    have he : (s : G) * (a * x) = (h : G) * ((π s : G) * x) := by
      simp [h, mul_assoc]
    simp only [finiteCosetArgument, he, hmul, Subgroup.coe_mul]
    simp [h, mul_assoc]

private theorem lift_homogeneous_map
    (E : Type u) [Field E] [TopologicalSpace E] [IsTopologicalDivisionRing E]
    (J : Type v) [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
    (V : Type w) [AddCommGroup V] [Module E V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul E V]
    (ρ : J →* V ≃ₗ[E] V)
    [HasDerivedCategory.{r} (ModuleCat.{t} E)]
    (A B C : CochainComplex (ModuleCat.{t} E) ℤ)
    (D : JointContinuousCochainCoordinates E J V ρ B C)
    (hneg : ∀ i : ℤ, i < 0 → IsZero (A.X i))
    (φ : ∀ n : ℕ, A.X (n : ℤ) →ₗ[E] ((Fin (n + 1) → J) → V))
    (hφ : ∀ n f, ∃ b, D.bEval n b = φ n f)
    (hδ : ∀ (n : ℕ) (f : A.X (n : ℤ)) (x : Fin (n + 2) → J),
      (∑ i : Fin (n + 2), (-1 : E) ^ i.val • φ n f (x ∘ i.succAbove)) =
        φ (n + 1) ((A.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom f) x) :
    ∃ T : A ⟶ B, ∀ (n : ℕ) (f : A.X (n : ℤ)) (x : Fin (n + 1) → J),
      D.bEval n ((T.f (n : ℤ)).hom f) x = φ n f x := by
  classical
  let l (n : ℕ) : A.X (n : ℤ) →ₗ[E] B.X (n : ℤ) :=
    { toFun := fun f ↦ Classical.choose (hφ n f)
      map_add' := by
        intro f g
        apply D.bInjective n
        rw [(D.bEval n).map_add, Classical.choose_spec (hφ n (f + g)),
          Classical.choose_spec (hφ n f), Classical.choose_spec (hφ n g), (φ n).map_add]
      map_smul' := by
        intro a f
        apply D.bInjective n
        rw [(D.bEval n).map_smul, Classical.choose_spec (hφ n (a • f)),
          Classical.choose_spec (hφ n f), (φ n).map_smul]
        rfl }
  have hl (n : ℕ) (f : A.X (n : ℤ)) : D.bEval n (l n f) = φ n f :=
    Classical.choose_spec (hφ n f)
  let T : A ⟶ B :=
    { f := fun i ↦ match i with
        | .ofNat n => ModuleCat.ofHom (l n)
        | .negSucc _ => 0
      comm' := by
        intro i j hij
        have he : i + 1 = j := hij
        subst j
        cases i with
        | ofNat n =>
          change ModuleCat.ofHom (l n) ≫ B.d (n : ℤ) ((n + 1 : ℕ) : ℤ) =
            A.d (n : ℤ) ((n + 1 : ℕ) : ℤ) ≫ ModuleCat.ofHom (l (n + 1))
          ext f
          apply D.bInjective (n + 1)
          ext x
          change D.bEval (n + 1) ((B.d _ _).hom (l n f)) x =
            D.bEval (n + 1) (l (n + 1) ((A.d _ _).hom f)) x
          rw [hl, D.delta]
          simp only [hl]
          exact hδ n f x
        | negSucc n =>
          exact (hneg _ (by omega)).eq_of_src _ _ }
  exact ⟨T, fun n f x ↦ congrFun (hl n f) x⟩

private theorem homogeneous_naturality
    (E : Type u) [Field E] [TopologicalSpace E] [IsTopologicalDivisionRing E]
    (J : Type v) [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
    (V : Type w) [AddCommGroup V] [Module E V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul E V]
    (ρ : J →* V ≃ₗ[E] V)
    (K : Type v) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (W : Type w') [AddCommGroup W] [Module E W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul E W]
    (σ : K →* W ≃ₗ[E] W)
    [HasDerivedCategory.{r} (ModuleCat.{t} E)]
    (B C BK CK : CochainComplex (ModuleCat.{t} E) ℤ)
    (D : JointContinuousCochainCoordinates E J V ρ B C)
    (DK : JointContinuousCochainCoordinates E K W σ BK CK)
    (h : K →* J) (hh : Continuous h) (b : V →ₗ[E] W) (hb : Continuous b)
    (heq : ∀ a z, b (ρ (h a) z) = σ a (b z)) :
    ∃ T : B ⟶ BK, ∀ (n : ℕ) (f : B.X (n : ℤ)) (x : Fin (n + 1) → K),
      DK.bEval n ((T.f (n : ℤ)).hom f) x = b (D.bEval n f (h ∘ x)) := by
  let φ (n : ℕ) : B.X (n : ℤ) →ₗ[E] ((Fin (n + 1) → K) → W) :=
    { toFun := fun f x ↦ b (D.bEval n f (h ∘ x))
      map_add' := by intro f g; ext x; simp
      map_smul' := by intro a f; ext x; simp }
  apply lift_homogeneous_map E K W σ B BK CK DK D.bNegative φ
  · intro n f
    apply (DK.bRange n _).mpr
    obtain ⟨hc, he⟩ := (D.bRange n _).mp ⟨f, rfl⟩
    refine ⟨hb.comp (hc.comp (continuous_pi (fun i ↦ hh.comp (continuous_apply i)))), ?_⟩
    intro a x
    change b (D.bEval n f (h ∘ (fun i ↦ a * x i))) = _
    have ht : h ∘ (fun i ↦ a * x i) = fun i ↦ h a * (h ∘ x) i := by
      funext i
      exact h.map_mul a (x i)
    rw [ht, he, heq]
    rfl
  · intro n f x
    change (∑ i : Fin (n + 2), (-1 : E) ^ i.val • b (D.bEval n f _)) =
      b (D.bEval (n + 1) ((B.d _ _).hom f) _)
    rw [D.delta, map_sum]
    simp only [map_smul]
    rfl

private theorem finite_average_map
    (E : Type u) [Field E] [TopologicalSpace E] [IsTopologicalDivisionRing E]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) (hH : IsOpen (H : Set G)) (S : Finset G)
    (hS : Subgroup.IsComplement (H : Set G) (S : Set G)) (h1 : 1 ∈ S)
    (V : Type w) [AddCommGroup V] [Module E V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul E V]
    (ρ : G →* V ≃ₗ[E] V) (hρ : Continuous (fun p : G × V ↦ ρ p.1 p.2))
    [HasDerivedCategory.{r} (ModuleCat.{t} E)]
    (B C BH CH : CochainComplex (ModuleCat.{t} E) ℤ)
    (D : JointContinuousCochainCoordinates E G V ρ B C)
    (DH : JointContinuousCochainCoordinates E H V (ρ.comp H.subtype) BH CH) :
    ∃ T : BH ⟶ B, ∀ (n : ℕ) (f : BH.X (n : ℤ)) (x : Fin (n + 1) → G),
      D.bEval n ((T.f (n : ℤ)).hom f) x =
        ∑ s ∈ S, ρ s⁻¹ (DH.bEval n f (fun i ↦ finiteCosetRetraction H S hS (s * x i))) := by
  classical
  let φ (n : ℕ) : BH.X (n : ℤ) →ₗ[E] ((Fin (n + 1) → G) → V) :=
    { toFun := fun f x ↦
        ∑ s ∈ S, ρ s⁻¹ (DH.bEval n f (fun i ↦ finiteCosetRetraction H S hS (s * x i)))
      map_add' := by
        intro f g
        ext x
        simp [map_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a f
        ext x
        simp [map_smul, Finset.smul_sum] }
  apply lift_homogeneous_map E G V ρ BH B C D DH.bNegative φ
  · intro n f
    apply (D.bRange n _).mpr
    obtain ⟨hc, he⟩ := (DH.bRange n _).mp ⟨f, rfl⟩
    refine ⟨?_, ?_⟩
    · apply continuous_finsetSum S
      intro s hs
      apply hρ.comp (f := fun x : Fin (n + 1) → G ↦ (s⁻¹, DH.bEval n f
        (fun i ↦ finiteCosetRetraction H S hS (s * x i))))
      apply continuous_const.prodMk
      apply hc.comp
      apply continuous_pi
      intro i
      exact (coset_retraction_continuous H hH S hS).comp
        (continuous_const.mul (continuous_apply i))
    · intro a x
      obtain ⟨π, hp, _⟩ := (finiteCosetRetraction_properties H hH S hS h1).2.2.2.2.2.2 a
      have heq (s : S) :
          ρ (s : G)⁻¹ (DH.bEval n f
            (fun i ↦ finiteCosetRetraction H S hS ((s : G) * (a * x i)))) =
          ρ a (ρ (π s : G)⁻¹ (DH.bEval n f
            (fun i ↦ finiteCosetRetraction H S hS ((π s : G) * x i)))) := by
        let h : H := ⟨(s : G) * a * (π s : G)⁻¹, hp s⟩
        have ht : (fun i ↦ finiteCosetRetraction H S hS ((s : G) * (a * x i))) =
            (fun i ↦ h * finiteCosetRetraction H S hS ((π s : G) * x i)) := by
          funext i
          rw [← coset_retraction_mul]
          congr 1
          simp [h, mul_assoc]
        rw [ht, he]
        change (ρ (s : G)⁻¹ * ρ (h : G)) _ = (ρ a * ρ (π s : G)⁻¹) _
        rw [← map_mul, ← map_mul]
        congr 2
        simp [h, mul_assoc]
      change (∑ s ∈ S, _) = ρ a (∑ s ∈ S, _)
      rw [← Finset.sum_coe_sort S, ← Finset.sum_coe_sort S]
      simp_rw [heq]
      rw [← map_sum]
      exact congrArg (ρ a) (Equiv.sum_comp π (fun s : S ↦
        ρ (s : G)⁻¹ (DH.bEval n f
          (fun i ↦ finiteCosetRetraction H S hS ((s : G) * x i)))))
  · intro n f x
    change (∑ i : Fin (n + 2), (-1 : E) ^ i.val • ∑ s ∈ S, _) = ∑ s ∈ S, _
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    rw [DH.delta]
    simp only [map_sum, map_smul]
    rfl

/-- Finite-coset averaging gives an E-linear cochain map, with the prescribed restriction
composite and simultaneous coefficient naturality for the same S and r. Evaluation
formulas specify every map uniquely, including the zero maps in negative degrees.
Source: arithmetic transfer expansion of direct-images (3), steps 1 and 5--9.
(blueprint: lem-sfb-finite-coset-homogeneous-averaging).

Proof: (1) Pointwise linear operations preserve continuity and equivariance. Coordinate
deletion is continuous and equivariant. Each pair of deletions in delta squared occurs
with opposite signs, so these are complexes, extended by zero in negative degrees.
(5) For each s, coordinatewise r(sx) is continuous; compose with f and the continuous
linear action of s⁻¹. Finite sums remain jointly continuous and depend E-linearly on f.
(6) Reindex the sum by the permutation pi_a from step 4. H-equivariance of f and
sa = h_s pi_a(s) give s⁻¹ f(r(sax_i)) = a pi_a(s)⁻¹ f(r(pi_a(s)x_i)). Thus T f is
G-equivariant. The evaluation image condition gives its unique cochain value.
(7) Expand delta T as the finite double sum over omissions and representatives.
Interchange sums; the linear action commutes with signed sums, giving delta T = T delta.
Negative-degree identities are zero. (8) Restriction is continuous, linear and commutes
with deletion. G-equivariance of F changes each summand s⁻¹ F(r(sx_i)) into F(a_s(x_i)),
giving exactly T R. (9) Postcomposition by a continuous equivariant linear b preserves
the evaluation images and commutes with deletion. Linearity moves b through the finite
sum and equivariance moves it through s⁻¹. Hence b_* T_V = T_W b_*, for all coefficients
and b with the same S and r. No division, limits, normality or separation is used. -/
theorem exists_finiteCosetHomogeneousAveraging
    (E : Type u) [Field E] [TopologicalSpace E] [IsTopologicalDivisionRing E]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (H : Subgroup G) (_hH : IsOpen (H : Set G)) (S : Finset G)
    (hS : Subgroup.IsComplement (H : Set G) (S : Set G)) (_h1 : 1 ∈ S)
    (V : Type w) [AddCommGroup V] [Module E V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul E V]
    (ρ : G →* V ≃ₗ[E] V) (_hρ : Continuous (fun p : G × V ↦ ρ p.1 p.2))
    [HasDerivedCategory.{r} (ModuleCat.{t} E)]
    (B C BH CH : CochainComplex (ModuleCat.{t} E) ℤ)
    (D : JointContinuousCochainCoordinates E G V ρ B C)
    (DH : JointContinuousCochainCoordinates E H V (ρ.comp H.subtype) BH CH) :
    ∃ (T : BH ⟶ B) (R : B ⟶ BH),
      (∀ (n : ℕ) (f : BH.X (n : ℤ)) (x : Fin (n + 1) → G),
        D.bEval n ((T.f (n : ℤ)).hom f) x =
          ∑ s ∈ S, ρ s⁻¹ (DH.bEval n f (fun i ↦ finiteCosetRetraction H S hS (s * x i)))) ∧
      (∀ (n : ℕ) (F : B.X (n : ℤ)) (x : Fin (n + 1) → H),
        DH.bEval n ((R.f (n : ℤ)).hom F) x = D.bEval n F (fun i ↦ (x i : G))) ∧
      (∀ (n : ℕ) (F : B.X (n : ℤ)) (x : Fin (n + 1) → G),
        D.bEval n (((R ≫ T).f (n : ℤ)).hom F) x =
          ∑ s ∈ S, D.bEval n F (fun i ↦ finiteCosetArgument H S hS s (x i))) ∧
      ∀ (W : Type w') [AddCommGroup W] [Module E W] [TopologicalSpace W]
        [IsTopologicalAddGroup W] [ContinuousSMul E W]
        (σ : G →* W ≃ₗ[E] W), Continuous (fun p : G × W ↦ σ p.1 p.2) →
        ∀ (BW CW BHW CHW : CochainComplex (ModuleCat.{t} E) ℤ)
          (DW : JointContinuousCochainCoordinates E G W σ BW CW)
          (DHW : JointContinuousCochainCoordinates E H W (σ.comp H.subtype) BHW CHW),
        ∃ TW : BHW ⟶ BW,
          (∀ (n : ℕ) (f : BHW.X (n : ℤ)) (x : Fin (n + 1) → G),
            DW.bEval n ((TW.f (n : ℤ)).hom f) x =
              ∑ s ∈ S, σ s⁻¹
                (DHW.bEval n f (fun i ↦ finiteCosetRetraction H S hS (s * x i)))) ∧
          ∀ b : V →ₗ[E] W, Continuous b →
            (∀ (a : G) (z : V), b (ρ a z) = σ a (b z)) →
            ∃ (bG : B ⟶ BW) (bH : BH ⟶ BHW),
              (∀ (n : ℕ) (F : B.X (n : ℤ)) (x : Fin (n + 1) → G),
                DW.bEval n ((bG.f (n : ℤ)).hom F) x = b (D.bEval n F x)) ∧
              (∀ (n : ℕ) (f : BH.X (n : ℤ)) (x : Fin (n + 1) → H),
                DHW.bEval n ((bH.f (n : ℤ)).hom f) x = b (DH.bEval n f x)) ∧
              bH ≫ TW = T ≫ bG := by
  classical
  obtain ⟨T, hT⟩ := finite_average_map E H _hH S hS _h1 V ρ _hρ B C BH CH D DH
  obtain ⟨R, hR⟩ := homogeneous_naturality
    E G V ρ H V (ρ.comp H.subtype) B C BH CH D DH H.subtype
    continuous_subtype_val (LinearMap.id) continuous_id (fun _ _ ↦ rfl)
  refine ⟨T, R, hT, ?_, ?_, ?_⟩
  · exact hR
  · intro n F x
    change D.bEval n ((T.f (n : ℤ)).hom ((R.f (n : ℤ)).hom F)) x = _
    rw [hT]
    apply Finset.sum_congr rfl
    intro s hs
    rw [hR]
    exact ((D.bRange n _).mp ⟨F, rfl⟩).2 s⁻¹
      (fun i ↦ (finiteCosetRetraction H S hS (s * x i) : G)) |>.symm
  · intro W _ _ _ _ _ σ hσ BW CW BHW CHW DW DHW
    obtain ⟨TW, hTW⟩ := finite_average_map E H _hH S hS _h1 W σ hσ
      BW CW BHW CHW DW DHW
    refine ⟨TW, hTW, ?_⟩
    intro b hb heq
    obtain ⟨bG, hbG⟩ := homogeneous_naturality
      E G V ρ G W σ B C BW CW D DW (MonoidHom.id G) continuous_id b hb heq
    obtain ⟨bH, hbH⟩ := homogeneous_naturality
      E H V (ρ.comp H.subtype) H W (σ.comp H.subtype) BH CH BHW CHW DH DHW
      (MonoidHom.id H) continuous_id b hb (fun a z ↦ heq a z)
    refine ⟨bG, bH, ?_, ?_, ?_⟩
    · exact hbG
    · exact hbH
    · apply HomologicalComplex.hom_ext
      intro i
      cases i with
      | ofNat n =>
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro f
        apply DW.bInjective n
        ext x
        change DW.bEval n ((TW.f (n : ℤ)).hom ((bH.f (n : ℤ)).hom f)) x =
          DW.bEval n ((bG.f (n : ℤ)).hom ((T.f (n : ℤ)).hom f)) x
        rw [hTW, hbG, hT, map_sum]
        apply Finset.sum_congr rfl
        intro s hs
        rw [hbH, heq]
        rfl
      | negSucc n =>
        exact (DH.bNegative _ (by omega)).eq_of_src _ _

end ContinuousCohomology
