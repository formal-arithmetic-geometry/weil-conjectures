/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import WeilConjectures.RingTheory.Kaehler.Trace

/-!
# Base change of the trace of differentials

Let `k → R → B` be ring maps with `B` finite free over `R`, `D : R → R` a `k`-derivation, and
`k → k'` a ring map. Then `B' = k' ⊗[k] B` is a finite free algebra over `R' = k' ⊗[k] R`
(`Algebra.TensorProduct.baseChangeBasis`), `D` extends to a `k'`-derivation `D'` of `R'`
(`Derivation.baseChange`), and the trace derivation of `B'` restricts to that of `B`
(`Algebra.traceDeriv_baseChange`). If `k → k'` has a `k`-linear retraction (e.g. `k` is a field),
duality for the trace of differentials descends from `B'` to `B`
(`KaehlerDifferential.bijective_liftKaehlerDifferential_traceDerivation_of_baseChange`).
-/

@[expose] public section

open TensorProduct

namespace Algebra.TensorProduct

variable (k k' R B : Type*) [CommRing k] [CommRing k'] [Algebra k k'] [CommRing R] [Algebra k R]
  [CommRing B] [Algebra R B] [Algebra k B] [IsScalarTower k R B]

/-- The `k' ⊗[k] R`-algebra structure on `k' ⊗[k] B` for an `R`-algebra `B`. -/
noncomputable abbrev baseChangeAlgebra : Algebra (k' ⊗[k] R) (k' ⊗[k] B) :=
  (map (AlgHom.id k' k') (IsScalarTower.toAlgHom k R B)).toRingHom.toAlgebra

attribute [local instance] baseChangeAlgebra

variable {k k' R B} in
lemma baseChangeAlgebra_algebraMap_tmul (x : k') (r : R) :
    algebraMap (k' ⊗[k] R) (k' ⊗[k] B) (x ⊗ₜ r) = x ⊗ₜ algebraMap R B r := rfl

variable {k k' R B} in
lemma baseChangeAlgebra_smul_tmul (x x' : k') (r : R) (b : B) :
    (x ⊗ₜ[k] r) • (x' ⊗ₜ[k] b) = (x * x') ⊗ₜ (r • b) := by
  rw [Algebra.smul_def, baseChangeAlgebra_algebraMap_tmul, tmul_mul_tmul, Algebra.smul_def]

lemma baseChangeAlgebra_isScalarTower : IsScalarTower k' (k' ⊗[k] R) (k' ⊗[k] B) :=
  .of_algebraMap_eq fun x ↦ by
    rw [RingHom.algebraMap_toAlgebra]
    simp [Algebra.TensorProduct.algebraMap_apply]

attribute [local instance] baseChangeAlgebra_isScalarTower

variable {k k' R B} {ι : Type*} [DecidableEq ι] (b : Module.Basis ι R B)

/-- Auxiliary `k'`-linear version of `Algebra.TensorProduct.baseChangeRepr`. -/
noncomputable def baseChangeReprAux : (k' ⊗[k] B) ≃ₗ[k'] (ι →₀ k' ⊗[k] R) :=
  (LinearEquiv.baseChange k k' B (ι →₀ R) (b.repr.restrictScalars k)).trans
    (finsuppRight k k' k' R ι)

lemma baseChangeReprAux_tmul (x : k') (y : B) (i : ι) :
    baseChangeReprAux (k' := k') b (x ⊗ₜ[k] y) i = x ⊗ₜ[k] b.repr y i := by
  simp [baseChangeReprAux, finsuppRight_apply_tmul_apply]

lemma baseChangeReprAux_smul (r : k' ⊗[k] R) (y : k' ⊗[k] B) :
    baseChangeReprAux b (r • y) = r • baseChangeReprAux b y := by
  induction r with
  | zero => simp
  | add r r' hr hr' => simp only [add_smul, map_add, hr, hr']
  | tmul x r =>
    induction y with
    | zero => simp
    | add y y' hy hy' => simp only [smul_add, map_add, hy, hy']
    | tmul x' c =>
      ext i
      rw [baseChangeAlgebra_smul_tmul, baseChangeReprAux_tmul, Finsupp.smul_apply,
        baseChangeReprAux_tmul, smul_eq_mul, tmul_mul_tmul, map_smul, Finsupp.smul_apply,
        smul_eq_mul]

/-- The coordinates of `k' ⊗[k] B` over `k' ⊗[k] R` in the base change of a basis of `B`. -/
noncomputable def baseChangeRepr : (k' ⊗[k] B) ≃ₗ[k' ⊗[k] R] (ι →₀ k' ⊗[k] R) where
  __ := baseChangeReprAux b
  map_smul' := baseChangeReprAux_smul b

lemma baseChangeRepr_tmul (x : k') (y : B) (i : ι) :
    baseChangeRepr b (x ⊗ₜ[k] y) i = x ⊗ₜ[k] b.repr y i :=
  baseChangeReprAux_tmul b x y i

/-- The basis `1 ⊗ bᵢ` of `k' ⊗[k] B` over `k' ⊗[k] R`. -/
noncomputable def baseChangeBasis : Module.Basis ι (k' ⊗[k] R) (k' ⊗[k] B) :=
  .ofRepr (baseChangeRepr b)

lemma baseChangeBasis_repr_tmul (x : k') (y : B) (i : ι) :
    (baseChangeBasis (k' := k') b).repr (x ⊗ₜ[k] y) i = x ⊗ₜ[k] b.repr y i :=
  baseChangeRepr_tmul b x y i

lemma baseChangeBasis_apply (i : ι) : baseChangeBasis (k' := k') b i = 1 ⊗ₜ[k] b i := by
  classical
  refine (baseChangeBasis (k' := k') b).repr.injective (Finsupp.ext fun j ↦ ?_)
  rw [baseChangeBasis_repr_tmul, Module.Basis.repr_self, Module.Basis.repr_self,
    Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> simp [Algebra.TensorProduct.one_def]

omit [DecidableEq ι] in
lemma free_baseChange [Module.Free R B] : Module.Free (k' ⊗[k] R) (k' ⊗[k] B) :=
  haveI := Classical.decEq (Module.Free.ChooseBasisIndex R B)
  .of_basis (baseChangeBasis (Module.Free.chooseBasis R B))

omit [DecidableEq ι] in
lemma finite_baseChange [Module.Free R B] [Module.Finite R B] :
    Module.Finite (k' ⊗[k] R) (k' ⊗[k] B) :=
  haveI := Classical.decEq (Module.Free.ChooseBasisIndex R B)
  .of_basis (baseChangeBasis (Module.Free.chooseBasis R B))

end Algebra.TensorProduct

namespace Derivation

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] (k' : Type*) [CommRing k']
  [Algebra k k'] (D : Derivation k R R)

/-- The base change `k' ⊗[k] R → k' ⊗[k] R` of a `k`-derivation of `R`. -/
noncomputable def baseChange : Derivation k' (k' ⊗[k] R) (k' ⊗[k] R) :=
  Derivation.mk' ((D : R →ₗ[k] R).baseChange k') fun a c ↦ by
    induction a with
    | zero => simp
    | add a a' ha ha' => simp only [add_mul, map_add, ha, ha', add_smul, smul_add]; abel
    | tmul x r =>
      induction c with
      | zero => simp
      | add c c' hc hc' => simp only [mul_add, map_add, hc, hc', smul_add, add_smul]; abel
      | tmul x' r' =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.baseChange_tmul,
          Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul, tmul_add, mul_comm x x']

@[simp]
lemma baseChange_tmul (x : k') (r : R) : D.baseChange k' (x ⊗ₜ r) = x ⊗ₜ D r := rfl

end Derivation

namespace Algebra

open TensorProduct Matrix

attribute [local instance] TensorProduct.baseChangeAlgebra TensorProduct.baseChangeAlgebra_isScalarTower

variable {k R B : Type*} [CommRing k] [CommRing R] [Algebra k R] [CommRing B] [Algebra R B]
  [Algebra k B] [IsScalarTower k R B] (k' : Type*) [CommRing k'] [Algebra k k']
  (D : Derivation k R R)

lemma leftMulMatrix_baseChangeBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R B) (a : B) :
    leftMulMatrix (TensorProduct.baseChangeBasis (k' := k') b) (1 ⊗ₜ[k] a) =
      (leftMulMatrix b a).map (TensorProduct.includeRight (R := k) (A := k')) := by
  ext i j
  rw [leftMulMatrix_eq_repr_mul, TensorProduct.baseChangeBasis_apply, tmul_mul_tmul, mul_one,
    TensorProduct.baseChangeBasis_repr_tmul, Matrix.map_apply, leftMulMatrix_eq_repr_mul,
    TensorProduct.includeRight_apply]

lemma traceDerivForm_map_includeRight {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n R)
    (Y : Matrix n m R) :
    traceDerivForm (D.baseChange k') (X.map (TensorProduct.includeRight (R := k) (A := k')))
      (Y.map TensorProduct.includeRight) = 1 ⊗ₜ traceDerivForm D X Y := by
  simp [traceDerivForm, tmul_sum, Algebra.TensorProduct.tmul_mul_tmul]

variable [Module.Free R B] [Module.Finite R B]

attribute [local instance] TensorProduct.free_baseChange TensorProduct.finite_baseChange

/-- The trace derivation of `k' ⊗[k] B` restricts to that of `B`. -/
lemma traceDeriv_baseChange (a c : B) :
    traceDeriv (D.baseChange k') ((1 : k') ⊗ₜ[k] a) (1 ⊗ₜ c) = 1 ⊗ₜ traceDeriv D a c := by
  classical
  set b := Module.Free.chooseBasis R B
  rw [traceDeriv_eq _ (TensorProduct.baseChangeBasis (k' := k') b), traceDerivAux,
    leftMulMatrix_baseChangeBasis, leftMulMatrix_baseChangeBasis,
    traceDerivForm_map_includeRight]
  rfl

end Algebra
