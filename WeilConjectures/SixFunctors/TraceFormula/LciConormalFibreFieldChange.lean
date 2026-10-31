/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Ideal.CotangentBaseChange
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import all WeilConjectures.RingTheory.StrictHenselizationCotangentDimension

/-!
# Conormal fibres after a field extension

Source: Stacks Project, Algebra, Tag 00SI (lemma-lci-field-change-local),
proof lines 36215--36259 (blueprint: lem-trf-lci-conormal-fibre-field-change).

## Main definitions

* `AlgebraicGeometry.lciBaseChangePresentationMap`: the base-changed presentation
  `K[x_1, …, x_n] → K ⊗_k C`, `x_i ↦ 1 ⊗ π(x_i)`.
* `AlgebraicGeometry.lciConormalFibre`: the conormal fibre `κ(q) ⊗_{P_q} (I/I²)_q`.
* `AlgebraicGeometry.lciScalarExtension`, `AlgebraicGeometry.lciScalarExtensionTmul`:
  extension of scalars along a ring map of residue fields and its pure tensors.

## Main statements

* `AlgebraicGeometry.lciConormalFibreFieldChange`: the coefficient-extension map induces an
  isomorphism of conormal fibres after extending scalars, and both have the same finite
  dimension.
-/

@[expose] public noncomputable section

universe u v w a b c

open scoped TensorProduct
open MvPolynomial

namespace AlgebraicGeometry

/-- The base change `π_K : K[x_1, …, x_n] → K ⊗_k C` of a polynomial presentation
`π : k[x_1, …, x_n] → C`, the `K`-algebra map with `x_i ↦ 1 ⊗ π(x_i)`; with coefficient
extension `γ` it identifies `C_K = K ⊗_k C` with `P_K / I_K`.

Source: Stacks Project, Algebra, Tag 00SI (lemma-lci-field-change-local), first proof
paragraph; base change of presentations, Tag 05G3
(blueprint: lem-trf-lci-conormal-fibre-field-change). -/
noncomputable def lciBaseChangePresentationMap
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (C : Type w) [CommRing C] [Algebra k C] (n : ℕ)
    (π : MvPolynomial (Fin n) k →ₐ[k] C) :
    MvPolynomial (Fin n) K →ₐ[K] K ⊗[k] C :=
  MvPolynomial.aeval (fun i : Fin n ↦
    (1 : K) ⊗ₜ[k] π (MvPolynomial.X i))

/-- The conormal fibre `κ(q) ⊗_{P_q} (I/I²)_q` of an ideal `I` of a commutative ring `P` at a
prime `q` (for `I ⊆ q` this is `(I/I²)_q ⊗_{C_q} κ(q)` with `C = P/I`).

Source: Stacks Project, Algebra, Tag 00SI (lemma-lci-field-change-local), the displayed
conormal-fibre identity in the proof
(blueprint: lem-trf-lci-conormal-fibre-field-change). -/
noncomputable abbrev lciConormalFibre
    {P : Type a} [CommRing P] (q I : Ideal P) [q.IsPrime] : Type a :=
  q.ResidueField ⊗[Localization q.primeCompl]
    LocalizedModule q.primeCompl I.Cotangent

/-- Extension of scalars `L ⊗_F M` of an `F`-module `M` along a ring map `σ : F → L`
(the factor `⊗_{κ(q)} κ(q_K)` of the statement).

Source: Stacks Project, Algebra, Tag 00SI (lemma-lci-field-change-local), the displayed
conormal-fibre identity in the proof
(blueprint: lem-trf-lci-conormal-fibre-field-change). -/
noncomputable abbrev lciScalarExtension
    (F : Type a) (L : Type b) [CommSemiring F] [CommSemiring L] (σ : F →+* L)
    (M : Type c) [AddCommMonoid M] [Module F M] : Type _ :=
  @TensorProduct F _ L M _ _ σ.toAlgebra.toModule inferInstance

/-- The `L`-module structure of the scalar extension `L ⊗_F M` along `σ : F → L`.

Source: Stacks Project, Algebra, Tag 00SI (lemma-lci-field-change-local), the displayed
conormal-fibre identity in the proof
(blueprint: lem-trf-lci-conormal-fibre-field-change). -/
noncomputable instance lciScalarExtensionModule
    (F : Type a) (L : Type b) [CommSemiring F] [CommSemiring L] (σ : F →+* L)
    (M : Type c) [AddCommMonoid M] [Module F M] :
    Module L (lciScalarExtension F L σ M) := by
  letI : Algebra F L := σ.toAlgebra
  exact TensorProduct.leftModule

/-- The pure tensor `a ⊗ m` in the scalar extension `L ⊗_F M` along `σ : F → L`.

Source: Stacks Project, Algebra, Tag 00SI (lemma-lci-field-change-local), the displayed
conormal-fibre identity in the proof
(blueprint: lem-trf-lci-conormal-fibre-field-change). -/
def lciScalarExtensionTmul
    (F : Type a) (L : Type b) [CommSemiring F] [CommSemiring L] (σ : F →+* L)
    (M : Type c) [AddCommMonoid M] [Module F M] (a : L) (m : M) :
    lciScalarExtension F L σ M :=
  @TensorProduct.tmul F _ L M _ _ σ.toAlgebra.toModule inferInstance a m

private noncomputable def lci_fibre_cancel
    {P : Type*} [CommRing P] (q : Ideal P) [q.IsPrime]
    (M : Type*) [AddCommGroup M] [Module P M] :
    q.ResidueField ⊗[Localization q.primeCompl] LocalizedModule q.primeCompl M
      ≃ₗ[q.ResidueField] q.ResidueField ⊗[P] M :=
  (LinearEquiv.baseChange (Localization q.primeCompl) q.ResidueField _ _
    (LocalizedModule.equivTensorProduct q.primeCompl M)).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange P
        (Localization q.primeCompl) q.ResidueField q.ResidueField M)

private theorem lci_fibre_cancel_tmul
    {P : Type*} [CommRing P] (q : Ideal P) [q.IsPrime]
    (M : Type*) [AddCommGroup M] [Module P M] (a : q.ResidueField) (m : M) :
    lci_fibre_cancel q M
      (a ⊗ₜ (LocalizedModule.mkLinearMap q.primeCompl M m)) = a ⊗ₜ[P] m := by
  simp [lci_fibre_cancel, LocalizedModule.mkLinearMap_apply,
    LocalizedModule.equivTensorProduct_apply_mk, Localization.mk_one_eq_algebraMap]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Conormal fibres of a finite type polynomial presentation commute with extension of
coefficients from `k` to `K`: the coefficient-extension map induces an isomorphism
`κ(q_K) ⊗_{κ(q)} (κ(q) ⊗ (I/I²)_q) ≃ κ(q_K) ⊗ (I_K/I_K²)_{q_K}` sending the class of each
relation `f ∈ I` to the class of its coefficientwise image, and the two fibres have the same
finite dimension.  The localizations and residue fields are taken in the polynomial rings at
`q'` and `q_K'`; since `I ⊆ q'` and `I_K ⊆ q_K'` these are those of `C` at `q` and of `C_K`
at `q_K`.

Source: Stacks Project, Algebra, Tag 00SI (lemma-lci-field-change-local), proof lines
36215--36259; Tag 00SJ (blueprint: lem-trf-lci-conormal-fibre-field-change).

Proof (the node's steps).
1. Put `M = I/I²`, `N = I_K/I_K²`, `γ : P → P_K` coefficient extension.  Presentation base
   change (lem-weil-pbc-presentation-base-change) for the identity presentation gives
   `P ⊗_k K ≃ P_K`, `p ⊗ λ ↦ λ γ(p)`, inverse checked on variables and coefficients
   (def-weil-pbc-mv-polynomial-ring); `C_K = P_K/I_K` is compatible with `C → C_K` and `γ`.
2. `P → P ⊗_k K` is faithfully flat (lem-weil-pbc-field-extension-base-change-faithfully-flat),
   hence flat (def-weil-pbc-faithfully-flat-ring-map); so `γ` is flat.
3. Flat conormal base change (lem-weil-pbc-ideal-cotangent-flat-base-change-ring) gives
   `M ⊗_P P_K ≃ N`, `[f] ⊗ b ↦ b[γ f]`, which is `C_K`-linear; with
   `M ⊗_C C_K ≃ M ⊗_P P_K` (def-weil-pbc-module-tensor-product) this gives
   `Θ : M ⊗_C C_K ≃ N`, `Θ([f] ⊗ [b]) = b[γ f]`.
4. With `F = κ(q)`, `L = κ(q_K)`, the composite `C → C_K → L` kills `q` and inverts
   `C ∖ q`, giving the injective field map `F → L` (def-weil-pbc-localization-at-prime).
5. Explicit fractions give `M_q ⊗_{C_q} F ≃ M ⊗_C F` and `N_{q_K} ⊗ L ≃ N ⊗_{C_K} L`
   (def-weil-pbc-module-localization, def-weil-pbc-module-tensor-product).
6. Tensor balancing gives `(M ⊗_C F) ⊗_F L ≃ M ⊗_C L ≃ (M ⊗_C C_K) ⊗_{C_K} L`; composing
   with `Θ ⊗ L` and step 5 gives the asserted `L`-linear isomorphism, which sends
   `([f]/1 ⊗ 1) ⊗ λ` to `[γ f]/1 ⊗ λ`.
7. `P` is Noetherian (lem-weil-pbc-polynomial-ring-field-regular-ring,
   def-weil-pbc-noetherian-ring), so `I = (f_1, …, f_r)`; their classes span the fibre
   `V = M_q ⊗ F`, which is finite dimensional.
8. A basis `v_1, …, v_d` of `V` extends to a basis `v_i ⊗ 1` of `V ⊗_F L` (independence by
   the extended coordinate functionals, def-weil-pbc-module-tensor-product), including
   `d = 0`; with step 6 the two fibres have the same finite dimension.
-/
theorem lciConormalFibreFieldChange
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (C : Type w) [CommRing C] [Algebra k C]
    (n : ℕ) (π : MvPolynomial (Fin n) k →ₐ[k] C)
    (hπ : Function.Surjective π)
    (qK : Ideal (K ⊗[k] C)) [qK.IsPrime] :
    let γ : MvPolynomial (Fin n) k →+* MvPolynomial (Fin n) K :=
      MvPolynomial.map (algebraMap k K)
    let πK := lciBaseChangePresentationMap k K C n π
    let qPK := qK.comap πK.toRingHom
    let qP := qPK.comap γ
    let I := RingHom.ker π.toRingHom
    let IK := I.map γ
    let σ := Ideal.ResidueField.map qP qPK γ (by rfl)
    ∃ e :
        lciScalarExtension qP.ResidueField qPK.ResidueField σ
          (lciConormalFibre qP I) ≃ₗ[qPK.ResidueField]
          lciConormalFibre qPK IK,
      (∀ (f : MvPolynomial (Fin n) k) (hf : f ∈ I),
        e (lciScalarExtensionTmul qP.ResidueField qPK.ResidueField σ
          (lciConormalFibre qP I) (1 : qPK.ResidueField)
          (1 ⊗ₜ[Localization qP.primeCompl]
            (LocalizedModule.mkLinearMap qP.primeCompl I.Cotangent
              (I.toCotangent ⟨f, hf⟩)))) =
          (1 : qPK.ResidueField) ⊗ₜ[Localization qPK.primeCompl]
            (LocalizedModule.mkLinearMap qPK.primeCompl IK.Cotangent
              (IK.toCotangent ⟨γ f, Ideal.mem_map_of_mem γ hf⟩))) ∧
      FiniteDimensional qPK.ResidueField (lciConormalFibre qPK IK) ∧
      FiniteDimensional qP.ResidueField (lciConormalFibre qP I) ∧
      Module.finrank qPK.ResidueField (lciConormalFibre qPK IK) =
        Module.finrank qP.ResidueField (lciConormalFibre qP I) := by
  classical
  have _ := hπ
  let P := MvPolynomial (Fin n) k
  let Q := MvPolynomial (Fin n) K
  let γ : P →+* Q := MvPolynomial.map (algebraMap k K)
  let : Algebra P Q := γ.toAlgebra
  let qQ := qK.comap (lciBaseChangePresentationMap k K C n π).toRingHom
  let qP := qQ.comap γ
  let I := RingHom.ker π.toRingHom
  let J := I.map γ
  let F := qP.ResidueField
  let L := qQ.ResidueField
  let : Algebra P F := inferInstance
  let : Algebra Q L := inferInstance
  let σ : F →+* L := Ideal.ResidueField.map qP qQ γ rfl
  let aFL : Algebra F L := σ.toAlgebra
  let : Module F L := aFL.toModule
  let aPL : Algebra P L := ((algebraMap Q L).comp γ).toAlgebra
  let : Module P L := aPL.toModule
  have : IsScalarTower P Q L := IsScalarTower.of_algebraMap_eq' (R := P) (S := Q) (A := L) rfl
  have : SMulCommClass P L L := Algebra.to_smulCommClass
  have : IsScalarTower P L L := IsScalarTower.right
  have hPFL : IsScalarTower P F L :=
    IsScalarTower.of_algebraMap_eq' (R := P) (S := F) (A := L) <| by
      apply RingHom.ext
      intro r
      exact (Ideal.ResidueField.map_algebraMap qP qQ γ rfl r).symm
  let eP : Q ≃ₐ[P] P ⊗[k] K := AlgEquiv.ofRingEquiv
    (f := (MvPolynomial.algebraTensorAlgEquiv k K).symm.toRingEquiv.trans
      (Algebra.TensorProduct.comm k K P).toRingEquiv) (by
        intro p
        change (Algebra.TensorProduct.comm k K P)
          ((MvPolynomial.algebraTensorAlgEquiv k K).symm (γ p)) = p ⊗ₜ[k] 1
        rw [MvPolynomial.algebraTensorAlgEquiv_symm_map]
        rfl)
  have : Module.Flat P Q := Module.Flat.of_linearEquiv eP.toLinearEquiv
  have hIJ : I.map (algebraMap P Q) = J := rfl
  have hI : I ≤ J.comap (algebraMap P Q) := Ideal.map_le_iff_le_comap.mp hIJ.le
  let eC : Q ⊗[P] I.Cotangent ≃ₗ[Q] J.Cotangent :=
    LinearEquiv.ofBijective _ (Algebra.flat_cotangent_bijective I J hIJ hI)
  let e0 := lci_fibre_cancel qP I.Cotangent
  let e1 := lci_fibre_cancel qQ J.Cotangent
  let cF := TensorProduct.AlgebraTensorModule.cancelBaseChange P F L L I.Cotangent
  let e : L ⊗[F] lciConormalFibre qP I ≃ₗ[L] lciConormalFibre qQ J :=
    (LinearEquiv.baseChange F L _ _ e0).trans
      (cF.trans
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange P Q L L I.Cotangent).symm.trans
          ((LinearEquiv.baseChange Q L _ _ eC).trans e1.symm)))
  have hfinP : Module.Finite F (lciConormalFibre qP I) :=
    Module.Finite.equiv e0.symm
  have hfinQ : Module.Finite L (lciConormalFibre qQ J) :=
    Module.Finite.equiv e
  refine ⟨e, ?_, hfinQ, hfinP, ?_⟩
  · intro f hf
    change e ((1 : L) ⊗ₜ[F]
      ((1 : F) ⊗ₜ[Localization qP.primeCompl]
        (LocalizedModule.mkLinearMap qP.primeCompl I.Cotangent
          (I.toCotangent ⟨f, hf⟩)))) = _
    apply e1.injective
    dsimp only [e, LinearEquiv.trans_apply]
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.baseChange_tmul]
    dsimp only [e0, e1, cF]
    rw [lci_fibre_cancel_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
      one_smul, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      LinearEquiv.baseChange_tmul, lci_fibre_cancel_tmul]
    change (1 : L) ⊗ₜ[Q]
      ((LinearMap.liftBaseChange Q
        (Ideal.mapCotangent I J (Algebra.ofId P Q) hI))
          ((1 : Q) ⊗ₜ[P] I.toCotangent ⟨f, hf⟩)) = _
    rw [LinearMap.liftBaseChange_tmul, one_smul, Ideal.mapCotangent_toCotangent]
    rfl
  · exact e.finrank_eq.symm.trans (Module.finrank_baseChange (R := L) (S := F))

end AlgebraicGeometry
