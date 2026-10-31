/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ContinuousMapCondensedRingSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Separation.DisjointCover
import Mathlib.Topology.Algebra.IsOpenUnits

/-! # Continuous right inverses over profinite spaces

Source: Hemo–Richarz–Scholbach, Example 3.1 (the section-ring setting only);
Stacks Project, Tags 07DQ and 08ZZ; the agent-written finite-matrix argument in the DAG
(blueprint: lem-pur-profinite-matrix-splitting).

The three coefficient specializations specify their topologies explicitly. Their
conclusions express the section-ring matrix identity by evaluation at every point.
The final statement uses the existing finite-subextension-valued section subring.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Profinite

/-- A pointwise surjective finite matrix of continuous functions has a continuous right inverse.
Source: Hemo–Richarz–Scholbach, Example 3.1 (setting); agent argument, Stacks 07DQ and 08ZZ
(blueprint: lem-pur-profinite-matrix-splitting).

Proof: If S is empty or n is zero use the unique empty-function or empty-column matrix.
At each s, lift the standard basis vectors through A(s), giving a constant matrix D_s
with A(s) D_s = 1. Set M_s(t) = A(t) D_s. Its determinant is continuous and equals 1 at s.
The open unit locus therefore gives a neighborhood U_s on which its determinant is a unit.
On U_s set B_s = D_s det(M_s)^{-1} adj(M_s). Continuity of inversion on the unit locus
and the determinant and adjugate formulas give continuous entries. The adjugate identity
of lem-weil-pbc-matrix-adjugate-identity gives A(t) B_s(t) = 1 there.
By lem-weil-pbc-profinite-clopen-basis choose clopen V_s inside U_s. Compactness gives
finitely many V_s covering S. Successively subtract earlier V_s to make a disjoint clopen
partition. Glue the corresponding B_s on this partition. The entries are continuous
because each piece is open. The pointwise identities give equality in C(S,T).
When m = 0 < n and S is nonempty, surjectivity contradicts nontriviality of the local ring.
-/
theorem continuousMap_matrix_exists_right_inverse
    (S : Type u) [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [TotallyDisconnectedSpace S] (T : Type v) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] [IsLocalRing T]
    (hunits : IsOpen {x : T | IsUnit x})
    (hinv : ContinuousOn (Ring.inverse : T → T) {x : T | IsUnit x})
    (m n : ℕ) (A : Matrix (Fin n) (Fin m) C(S, T))
    (hsurj : ∀ s : S, Function.Surjective (Matrix.of (fun i j ↦ A i j s)).mulVec) :
    ∃ B : Matrix (Fin m) (Fin n) C(S, T), A * B = 1 := by
  classical
  let a : S → Matrix (Fin n) (Fin m) T := fun s ↦ Matrix.of (fun i j ↦ A i j s)
  have hc : Continuous a := continuous_matrix fun i j ↦ (A i j).continuous
  choose D hD using fun s ↦ Matrix.mulVec_surjective_iff_exists_right_inverse.mp (hsurj s)
  let M : S → S → Matrix (Fin n) (Fin n) T := fun s t ↦ a t * D s
  have hM (s : S) : Continuous (M s) := hc.matrix_mul continuous_const
  let U : S → TopologicalSpace.Opens S := fun s ↦
    ⟨{t | IsUnit (M s t).det}, hunits.preimage (hM s).matrix_det⟩
  have hsU (s : S) : s ∈ U s := by
    change IsUnit (a s * D s).det
    rw [show a s * D s = 1 from hD s, Matrix.det_one]
    exact isUnit_one
  have hcover : TopologicalSpace.IsOpenCover U :=
    TopologicalSpace.IsOpenCover.of_sets _ (by
      ext s
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      exact ⟨s, hsU s⟩)
  obtain ⟨r, W, hW, hcov, hdisj⟩ :=
    hcover.exists_finite_nonempty_disjoint_clopen_cover
  choose q hq using fun i ↦ (hW i).2
  have hex (s : S) : ∃ i, s ∈ W i := Set.mem_iUnion.mp (hcov (Set.mem_univ s))
  choose g hg using hex
  have hg_eq (s : S) (i : Fin r) (hi : s ∈ W i) : g s = i := by
    apply hdisj.eq
    simpa only [← TopologicalSpace.Clopens.coe_disjoint, Set.not_disjoint_iff] using
      (show ∃ x ∈ (W (g s) : Set S), x ∈ (W i : Set S) from ⟨s, hg s, hi⟩)
  let b : S → S → Matrix (Fin m) (Fin n) T := fun s t ↦ D s * (M s t)⁻¹
  have hb (s t : S) (ht : t ∈ U s) : ContinuousAt (b s) t := by
    have hi : ContinuousAt (Ring.inverse : T → T) (M s t).det :=
      hinv.continuousAt (hunits.mem_nhds ht)
    have hm_inv : ContinuousAt (fun z ↦ (M s z)⁻¹) t :=
      (continuousAt_matrix_inv (M s t) hi).comp (hM s).continuousAt
    exact ((continuous_const (y := D s)).matrix_mul
      (continuous_id (X := Matrix (Fin n) (Fin n) T))).continuousAt.comp hm_inv
  let f : S → Matrix (Fin m) (Fin n) T := fun t ↦ b (q (g t)) t
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (hb (q (g t)) t (hq (g t) (hg t))).congr_of_eventuallyEq
    filter_upwards [(W (g t)).isOpen.mem_nhds (hg t)] with z hz
    dsimp [f]
    rw [hg_eq z (g t) hz]
  refine ⟨fun i j ↦ ⟨fun s ↦ f s i j, hf.matrix_elem i j⟩, ?_⟩
  have hprod (s : S) : a s * f s = 1 := by
    change a s * (D (q (g s)) * (M (q (g s)) s)⁻¹) = 1
    rw [← Matrix.mul_assoc]
    exact Matrix.mul_nonsing_inv _ (hq (g s) (hg s))
  ext i j s
  have h := congrArg (fun N : Matrix (Fin n) (Fin n) T ↦ N i j) (hprod s)
  by_cases hij : i = j
  · subst j
    simpa [a, Matrix.mul_apply, Matrix.one_apply, Finset.sum_apply] using h
  · simpa [a, Matrix.mul_apply, Matrix.one_apply, Finset.sum_apply, hij] using h

/-- The splitting assertion for the discrete positive-level coefficient quotient.
Source: Hemo–Richarz–Scholbach, Example 3.1; the coefficient cases in the DAG proof
(blueprint: lem-pur-profinite-matrix-splitting).

Proof: lem-weil-l-adic-extension-integers-dvr identifies the uniformizer ideal with
the maximal ideal. Its positive powers lie in that proper ideal, making the quotient
nonzero. A nontrivial quotient of a local ring is local.
In the discrete topology all ring operations and inversion are continuous and the units
are open. Apply the general splitting argument: choose pointwise constant right inverses,
correct them on determinant-unit neighborhoods by the adjugate identity, refine a finite
subcover to a disjoint clopen partition and glue. Evaluation gives the displayed identity.
Empty S and n = 0 use the unique matrices; m = 0 < n on nonempty S is impossible.
-/
theorem coefficientQuotient_matrix_exists_right_inverse
    (S : Type u) [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [TotallyDisconnectedSpace S] (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type v) [Field F] [Algebra (Padic ℓ) F] [FiniteDimensional (Padic ℓ) F]
    (a : ℕ) (ha : 1 ≤ a) (m n : ℕ)
    (A : Matrix (Fin n) (Fin m)
      (@ContinuousMap S (Padic.coefficientExtensionRing ℓ F a) _ ⊥))
    (hsurj : ∀ s : S, Function.Surjective (Matrix.of (fun i j ↦ A i j s)).mulVec) :
    ∃ B : Matrix (Fin m) (Fin n)
      (@ContinuousMap S (Padic.coefficientExtensionRing ℓ F a) _ ⊥),
      ∀ s : S, Matrix.of (fun i j ↦ A i j s) * Matrix.of (fun i j ↦ B i j s) = 1 := by
  let : TopologicalSpace (Padic.coefficientExtensionRing ℓ F a) := ⊥
  let : DiscreteTopology (Padic.coefficientExtensionRing ℓ F a) :=
    discreteTopology_bot _
  have hO := (Padic.extension_integers_dvr ℓ F
      (Padic.coefficientExtensionAbsoluteValue ℓ F)
      (spectralNorm_extends (K := Padic ℓ) (L := F))).choose_spec.choose_spec
  let : IsLocalRing (Padic.coefficientExtensionIntegers ℓ F) :=
    hO.2.2.2.1
  have hm : (Padic.coefficientExtensionMaximalIdeal ℓ F).IsMaximal := by
    unfold Padic.coefficientExtensionMaximalIdeal Padic.coefficientExtensionIntegers
    exact hO.2.2.2.2.1
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer ℓ F} :
      Set (Padic.coefficientExtensionIntegers ℓ F)) =
      Padic.coefficientExtensionMaximalIdeal ℓ F := by
    unfold Padic.coefficientExtensionUniformizer Padic.coefficientExtensionMaximalIdeal
      Padic.coefficientExtensionIntegers
    exact hO.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hle : Padic.coefficientExtensionIdeal ℓ F a ≤
      Padic.coefficientExtensionMaximalIdeal ℓ F := by
    unfold Padic.coefficientExtensionIdeal
    rw [hgen]
    exact Ideal.pow_le_self (Nat.ne_of_gt ha)
  let : Nontrivial (Padic.coefficientExtensionRing ℓ F a) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top hm.ne_top hle)
  let : IsLocalRing (Padic.coefficientExtensionRing ℓ F a) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ F a))
      Ideal.Quotient.mk_surjective
  have hu : IsOpen {x : Padic.coefficientExtensionRing ℓ F a | IsUnit x} := isOpen_discrete _
  have hi : ContinuousOn (Ring.inverse : Padic.coefficientExtensionRing ℓ F a → _)
      {x : Padic.coefficientExtensionRing ℓ F a | IsUnit x} :=
    continuous_of_discreteTopology.continuousOn
  obtain ⟨B, hB⟩ := continuousMap_matrix_exists_right_inverse (S := S)
    (T := Padic.coefficientExtensionRing ℓ F a)
    (hunits := hu) (hinv := hi) m n A hsurj
  refine ⟨B, ?_⟩
  intro s
  ext i j
  have hh := congrArg (fun M : Matrix (Fin n) (Fin n)
      C(S, Padic.coefficientExtensionRing ℓ F a) => M i j) hB
  have hh_s := ContinuousMap.congr_fun hh s
  by_cases hij : i = j
  · subst j
    simpa [Matrix.mul_apply, Matrix.of_apply, ContinuousMap.mul_apply,
      Finset.sum_apply] using hh_s
  · simpa [Matrix.mul_apply, Matrix.of_apply, ContinuousMap.mul_apply, hij] using hh_s

/-- The splitting assertion for the valuation ring with its uniformizer-adic topology.
Source: Hemo–Richarz–Scholbach, Example 3.1; the coefficient cases in the DAG proof
(blueprint: lem-pur-profinite-matrix-splitting).

Proof: By lem-weil-l-adic-extension-integers-dvr the coefficient ring is local and its
uniformizer generates the maximal ideal. Hence the ideal defining the adic topology lies
in the Jacobson radical of zero. Mathlib's IsOpenUnits.of_isAdic makes the units an open
subspace, and Units.continuous_coe_inv transfers through that open embedding to continuity
of Ring.inverse at units. Apply the general splitting construction: constant pointwise
splittings, adjugate correction on unit neighborhoods, a finite disjoint clopen refinement,
and entrywise gluing. Evaluation gives the identity. No comparison with the valuation
topology is needed. Empty spaces and zero matrix dimensions are included.
-/
theorem coefficientIntegers_matrix_exists_right_inverse
    (S : Type u) [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [TotallyDisconnectedSpace S] (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type v) [Field F] [Algebra (Padic ℓ) F] [FiniteDimensional (Padic ℓ) F]
    (m n : ℕ)
    (A : Matrix (Fin n) (Fin m)
      (@ContinuousMap S (Padic.coefficientExtensionIntegers ℓ F) _
        (Padic.coefficientExtensionIdeal ℓ F 1).adicTopology))
    (hsurj : ∀ s : S, Function.Surjective (Matrix.of (fun i j ↦ A i j s)).mulVec) :
    ∃ B : Matrix (Fin m) (Fin n)
      (@ContinuousMap S (Padic.coefficientExtensionIntegers ℓ F) _
        (Padic.coefficientExtensionIdeal ℓ F 1).adicTopology),
      ∀ s : S, Matrix.of (fun i j ↦ A i j s) * Matrix.of (fun i j ↦ B i j s) = 1 := by
  let R := Padic.coefficientExtensionIntegers ℓ F
  let I : Ideal R := Padic.coefficientExtensionIdeal ℓ F 1
  let : TopologicalSpace R := I.adicTopology
  let : IsTopologicalRing R := I.ringFilterBasis.isTopologicalRing
  have hO := (Padic.extension_integers_dvr ℓ F
    (Padic.coefficientExtensionAbsoluteValue ℓ F)
    (spectralNorm_extends (K := Padic ℓ) (L := F))).choose_spec.choose_spec
  let : IsLocalRing R := hO.2.2.2.1
  have hgen : I = Padic.coefficientExtensionMaximalIdeal ℓ F := by
    dsimp [I, Padic.coefficientExtensionIdeal]
    rw [pow_one]
    exact hO.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hm : Padic.coefficientExtensionMaximalIdeal ℓ F = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal hO.2.2.2.2.1
  let : IsOpenUnits R := IsOpenUnits.of_isAdic rfl
    (hgen.trans hm ▸ IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
  have hu : IsOpen {x : R | IsUnit x} := by
    change IsOpen (Set.range (Units.val : Rˣ → R))
    exact (IsOpenUnits.isOpenEmbedding_unitsVal (M := R)).isOpen_range
  have hi : ContinuousOn (Ring.inverse : R → R) {x : R | IsUnit x} := by
    intro x hx
    have hc : Continuous (fun u : Rˣ ↦ Ring.inverse (u : R)) := by
      simpa only [Ring.inverse_unit] using (Units.continuous_coe_inv (M := R))
    have ht := (IsOpenUnits.isOpenEmbedding_unitsVal (M := R)).continuousAt_iff
      (g := (Ring.inverse : R → R)) (x := hx.unit) |>.mp hc.continuousAt
    simpa only [IsUnit.unit_spec] using ht.continuousWithinAt
  obtain ⟨B, hB⟩ := continuousMap_matrix_exists_right_inverse (S := S) (T := R)
    hu hi m n A hsurj
  refine ⟨B, ?_⟩
  intro s
  let e : C(S, R) →+* R :=
    { toFun := fun f ↦ f s
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }
  change A.map e * B.map e = 1
  rw [← Matrix.map_mul, hB]
  exact Matrix.map_one e (map_zero e) (map_one e)

set_option linter.style.haveILetI false in
/-- The splitting assertion for a finite extension with its extending absolute-value topology.
Source: Hemo–Richarz–Scholbach, Example 3.1; the coefficient cases in the DAG proof
(blueprint: lem-pur-profinite-matrix-splitting).

Proof: lem-weil-l-adic-extension-absolute-value identifies the recorded spectral absolute
value with the unique extending value. Its topology makes F a topological field. Its
unit set is the open complement of zero and inversion is continuous there, by
|y^{-1}-x^{-1}| = |y-x|/(|x||y|) and |y| = |x| for y sufficiently close to nonzero x.
Thus the general argument applies: lift basis vectors pointwise, use the adjugate to
correct the constant splittings on determinant-unit neighborhoods, and glue over a
finite disjoint clopen partition. Evaluation gives the claimed identity. The empty space
and zero dimensions are handled as in the general assertion.
-/
theorem coefficientField_matrix_exists_right_inverse
    (S : Type u) [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [TotallyDisconnectedSpace S] (ℓ : ℕ) [Fact ℓ.Prime]
    (F : Type v) [Field F] [Algebra (Padic ℓ) F] [FiniteDimensional (Padic ℓ) F]
    (m n : ℕ)
    (A : Matrix (Fin n) (Fin m)
      (@ContinuousMap S F _
        (@UniformSpace.toTopologicalSpace F
          (Padic.coefficientExtensionAbsoluteValue ℓ F).toNormedField.toUniformSpace)))
    (hsurj : ∀ s : S, Function.Surjective (Matrix.of (fun i j ↦ A i j s)).mulVec) :
    ∃ B : Matrix (Fin m) (Fin n)
      (@ContinuousMap S F _
        (@UniformSpace.toTopologicalSpace F
          (Padic.coefficientExtensionAbsoluteValue ℓ F).toNormedField.toUniformSpace)),
      ∀ s : S, Matrix.of (fun i j ↦ A i j s) * Matrix.of (fun i j ↦ B i j s) = 1 := by
  letI : NormedField F :=
    (Padic.coefficientExtensionAbsoluteValue ℓ F).toNormedField
  have hu : IsOpen {x : F | IsUnit x} := by
    rw [show {x : F | IsUnit x} = ({0} : Set F)ᶜ by
      ext x
      simp [isUnit_iff_ne_zero]]
    exact isClosed_singleton.isOpen_compl
  have hi : ContinuousOn (Ring.inverse : F → F) {x : F | IsUnit x} := by
    intro x hx
    exact (NormedRing.inverse_continuousAt hx.unit).continuousWithinAt
  obtain ⟨B, hB⟩ := continuousMap_matrix_exists_right_inverse (S := S) (T := F)
    (hunits := hu) (hinv := hi) m n A hsurj
  refine ⟨B, ?_⟩
  intro s
  ext i j
  have hh := congrArg (fun M : Matrix (Fin n) (Fin n) C(S, F) => M i j) hB
  have hh_s := ContinuousMap.congr_fun hh s
  by_cases hij : i = j
  · subst j
    simpa [Matrix.mul_apply, Matrix.of_apply, ContinuousMap.mul_apply] using hh_s
  · simpa [Matrix.mul_apply, Matrix.of_apply, ContinuousMap.mul_apply, hij] using hh_s

/-- The splitting stays in the specified finite-subextension-valued coefficient subring.
Source: Hemo–Richarz–Scholbach, Example 3.1 (setting); the agent finite-subextension
argument in the DAG proof (blueprint: lem-pur-profinite-matrix-splitting).

Proof: Take the supremum K of the finitely many finite fields containing the entries
of A. Mathlib's finiteDimensional_iSup_of_finite makes K finite over the base field.
The entries of A are continuous as K-valued maps in its subtype topology. Choose a
K-linear retraction p of K into the algebraic closure. For y in K^n, surjectivity over
the algebraic closure supplies x with A(s)x=y. Since the coefficients lie in K,
A(s)p(x)=p(A(s)x)=y. Thus the evaluated matrix is already surjective over K. Apply the
general splitting theorem in the topological field K. Include the resulting continuous
K-valued entries into the algebraic closure: their values all lie in the same finite
field K, so they belong to the specified finite-subextension-valued section subring.
Evaluation transfers the right-inverse identity. Empty families use the bottom field.
-/
theorem finiteIntermediateFieldValued_matrix_exists_right_inverse
    (S : Type u) [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [TotallyDisconnectedSpace S] (ℓ : ℕ) [Fact ℓ.Prime] (m n : ℕ)
    (A : Matrix (Fin n) (Fin m) (PadicAlgCl.finiteIntermediateFieldValued ℓ S))
    (hsurj : ∀ s : S,
      Function.Surjective (Matrix.of (fun i j ↦ (A i j).val s)).mulVec) :
    ∃ B : Matrix (Fin m) (Fin n) (PadicAlgCl.finiteIntermediateFieldValued ℓ S),
      A * B = 1 := by
  classical
  choose E hdim hE using fun i j ↦ (A i j).property
  let K : IntermediateField (Padic ℓ) (PadicAlgCl ℓ) :=
    ⨆ p : Fin n × Fin m, E p.1 p.2
  let (p : Fin n × Fin m) : FiniteDimensional (Padic ℓ) (E p.1 p.2) := hdim p.1 p.2
  have hK : FiniteDimensional (Padic ℓ) K :=
    IntermediateField.finiteDimensional_iSup_of_finite
  have hmem (i : Fin n) (j : Fin m) (s : S) : (A i j).val s ∈ K :=
    (le_iSup (fun p : Fin n × Fin m ↦ E p.1 p.2) (i, j)) (hE i j s)
  let A' : Matrix (Fin n) (Fin m) C(S, K) := fun i j ↦
    ⟨fun s ↦ ⟨(A i j).val s, hmem i j s⟩, (A i j).val.continuous.subtype_mk _⟩
  obtain ⟨p, hp⟩ := (Algebra.linearMap K (PadicAlgCl ℓ)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap K (PadicAlgCl ℓ)).injective)
  have hp' (x : K) : p (x : PadicAlgCl ℓ) = x :=
    DFunLike.congr_fun hp x
  have hsurj' (s : S) :
      Function.Surjective (Matrix.of (fun i j ↦ A' i j s)).mulVec := by
    intro y
    obtain ⟨x, hx⟩ := hsurj s (fun i ↦ (y i : PadicAlgCl ℓ))
    refine ⟨fun j ↦ p (x j), ?_⟩
    funext i
    have hh := congrArg p (congrFun hx i)
    change ∑ j, A' i j s * p (x j) = y i
    calc
      ∑ j, A' i j s * p (x j) =
          p (∑ j, (A i j).val s * x j) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        exact (p.map_smul (A' i j s) (x j)).symm
      _ = y i := by simpa only [Matrix.mulVec, dotProduct, Matrix.of_apply, hp'] using hh
  have hu : IsOpen {x : K | IsUnit x} := by
    rw [show {x : K | IsUnit x} = ({0} : Set K)ᶜ by
      ext x
      simp [isUnit_iff_ne_zero]]
    exact isClosed_singleton.isOpen_compl
  have hi : ContinuousOn (Ring.inverse : K → K) {x : K | IsUnit x} := by
    intro x hx
    simpa only [Ring.inverse_eq_inv'] using
      (continuousAt_inv₀ (isUnit_iff_ne_zero.mp hx)).continuousWithinAt
  obtain ⟨B', hB'⟩ := continuousMap_matrix_exists_right_inverse S K hu hi m n A' hsurj'
  let B : Matrix (Fin m) (Fin n) (PadicAlgCl.finiteIntermediateFieldValued ℓ S) :=
    fun i j ↦ ⟨⟨fun s ↦ (B' i j s : PadicAlgCl ℓ),
      continuous_subtype_val.comp (B' i j).continuous⟩,
      K, hK, fun s ↦ (B' i j s).property⟩
  refine ⟨B, ?_⟩
  ext i j s
  have hh := congrArg (fun N : Matrix (Fin n) (Fin n) C(S, K) ↦ N i j) hB'
  have hs := congrArg (fun f : C(S, K) ↦ (f s : PadicAlgCl ℓ)) hh
  by_cases hij : i = j
  · subst j
    simpa [B, A', Matrix.mul_apply, Matrix.one_apply] using hs
  · simpa [B, A', Matrix.mul_apply, Matrix.one_apply, hij] using hs

end Profinite
