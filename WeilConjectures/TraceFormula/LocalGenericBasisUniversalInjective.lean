/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import WeilConjectures.RingTheory.AffineGeometricallyIntegralProjective
import WeilConjectures.RingTheory.LocalUniversalInjectiveResidue
import WeilConjectures.RingTheory.UniversalInjectiveLocalization
import WeilConjectures.TraceFormula.LocalUIFlatCokernel

/-!
# Local generic-basis subtraction criterion

Source: Stacks Project, Tag 05I3, `lemma-induction-step`, implication (1)⇒(2).
(blueprint: lem-trf-local-generic-basis-universal-injective)
-/

@[expose] public section

set_option autoImplicit false

universe u v w z t

namespace RingHom
open scoped TensorProduct

private theorem small_adjoin_finset {k : Type u} {K : Type z} [Field k] [Field K]
    [Algebra k K] (s : Finset K) : Small.{u} (IntermediateField.adjoin k (s : Set K)) := by
  open Cardinal in
  have hs : lift.{u} #(s : Set K) ≤ ℵ₀ :=
    (lift_lt_aleph0.mpr (lt_aleph0_of_finite _)).le
  have hcard : lift.{u} #(IntermediateField.adjoin k (s : Set K)) ≤
      lift.{z} #(k ⊕ ℕ) := by
    simp only [mk_sum, lift_add, mk_nat, lift_lift, lift_aleph0]
    rw [add_eq_max' le_rfl]
    exact (IntermediateField.lift_cardinalMk_adjoin_le k (s : Set K)).trans
      (sup_le (sup_le le_sup_left (hs.trans le_sup_right)) le_sup_right)
  obtain ⟨f⟩ := Cardinal.lift_mk_le'.mp hcard
  exact small_of_injective f.injective

/-- The fibre domain condition transports from a universe containing the rings to an
arbitrary universe of residue-field extensions.

Source: Stacks Project, Algebra, Tag 05DX, `definition-geometrically-integral`; Tag 05I3,
`lemma-induction-step`, geometric-integrality hypothesis.
(blueprint: lem-trf-local-generic-basis-universal-injective)

Proof: Fix `p` and a residue-field extension `K`. Each finite family of elements of
`K ⊗[R] S` is represented using finitely many coefficients of `K`. The subfield generated
by these coefficients and the image of `κ(p)` is small in `max u v w`: its cardinality
is bounded by the maximum of the cardinality of `κ(p)` and that of the natural numbers.
Shrink this subfield, lift to `max u v w`, and transport the `R`-algebra structure and
residue-field map along the field equivalence. Apply `hgeom` to that field. Tensor
extension along its embedding into `K` is injective, since a field extension is faithfully
flat. Thus a product of two nonzero elements in `K ⊗[R] S` cannot vanish: choose the
subfield for both elements and use the domain property there. The same argument with
`1` shows nontriviality. Tensor associativity identifies this with extending the affine
fibre `p.asIdeal.Fiber S`; tensor symmetry accounts for either order of the factors.
This supplies the universe transport, including the identity extension and extensions
whose universe is smaller or larger than the universes of the rings.
-/
theorem geometricFibres_domain_baseChange
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hgeom : ∀ (p : PrimeSpectrum R) (K : Type (max u v w)) [Field K]
      [Algebra R K] (ι : p.asIdeal.ResidueField →+* K),
      algebraMap R K = ι.comp (algebraMap R p.asIdeal.ResidueField) →
      IsDomain (K ⊗[R] S))
    (p : PrimeSpectrum R) (K : Type z) [Field K] [Algebra R K]
    (ι : p.asIdeal.ResidueField →+* K)
    (hι : algebraMap R K = ι.comp (algebraMap R p.asIdeal.ResidueField)) :
    IsDomain (K ⊗[R] S) := by
  classical
  let k := p.asIdeal.ResidueField
  let : Algebra k K := ι.toAlgebra
  have : IsScalarTower R k K := IsScalarTower.of_algebraMap_eq' hι
  have hsmall (s : Finset K) : Small.{max u v w} (IntermediateField.adjoin k (s : Set K)) :=
    by
      have := small_adjoin_finset (k := k) s
      exact Small.mk' ((equivShrink _).trans (Equiv.ulift.{max u v w}).symm)
  have hdomain (s : Finset K) : IsDomain (IntermediateField.adjoin k (s : Set K) ⊗[R] S) := by
    let F := IntermediateField.adjoin k (s : Set K)
    have : Small.{max u v w} F := hsmall s
    let e := Shrink.algEquiv R F
    let i : k →+* Shrink.{max u v w} F :=
      (Shrink.algEquiv k F).symm.toRingHom.comp (algebraMap k F)
    have hi : algebraMap R (Shrink.{max u v w} F) =
        i.comp (algebraMap R k) := by
      apply RingHom.ext
      intro a
      change algebraMap R (Shrink.{max u v w} F) a =
        (Shrink.algEquiv k F).symm (algebraMap k F (algebraMap R k a))
      rw [← IsScalarTower.algebraMap_apply R k F]
      exact (e.symm.commutes a).symm
    have := hgeom p (Shrink.{max u v w} F) i hi
    exact (Algebra.TensorProduct.congr e.symm (AlgEquiv.refl : S ≃ₐ[R] S)).toMulEquiv.isDomain _
  have hinj (F : IntermediateField k K) :
      Function.Injective (F.val.toLinearMap.restrictScalars R |>.rTensor S) := by
    let f := F.val.toLinearMap
    obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr F.val.injective)
    have hgf : (g.restrictScalars R).comp (f.restrictScalars R) = LinearMap.id :=
      congrArg (LinearMap.restrictScalars R) hg
    have ht := congrArg (LinearMap.rTensor S) hgf
    rw [LinearMap.rTensor_comp, LinearMap.rTensor_id] at ht
    exact Function.LeftInverse.injective (fun x ↦ LinearMap.congr_fun ht x)
  have hlift (x y : K ⊗[R] S) :
      ∃ (s : Finset K) (x' y' : IntermediateField.adjoin k (s : Set K) ⊗[R] S),
        (Algebra.TensorProduct.map ((IntermediateField.adjoin k (s : Set K)).val.restrictScalars R)
          (AlgHom.id R S)) x' = x ∧
        (Algebra.TensorProduct.map ((IntermediateField.adjoin k (s : Set K)).val.restrictScalars R)
          (AlgHom.id R S)) y' = y := by
    obtain ⟨sx, hx⟩ := TensorProduct.exists_finset x
    obtain ⟨sy, hy⟩ := TensorProduct.exists_finset y
    let s := (sx ∪ sy).image Prod.fst
    let F := IntermediateField.adjoin k (s : Set K)
    have hmem (a : K × S) (ha : a ∈ sx ∪ sy) : a.1 ∈ F :=
      IntermediateField.subset_adjoin k (s : Set K) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    let x' : F ⊗[R] S := ∑ a ∈ sx.attach, (⟨a.val.1,
      hmem a.val (Finset.mem_union_left _ a.property)⟩ : F) ⊗ₜ[R] a.val.2
    let y' : F ⊗[R] S := ∑ a ∈ sy.attach, (⟨a.val.1,
      hmem a.val (Finset.mem_union_right _ a.property)⟩ : F) ⊗ₜ[R] a.val.2
    refine ⟨s, x', y', ?_, ?_⟩
    · simp only [x', map_sum, Algebra.TensorProduct.map_tmul]
      change (∑ a ∈ sx.attach, a.val.1 ⊗ₜ[R] a.val.2) = x
      rw [Finset.sum_attach sx (fun a : K × S ↦ a.1 ⊗ₜ[R] a.2)]
      exact hx.symm
    · simp only [y', map_sum, Algebra.TensorProduct.map_tmul]
      change (∑ a ∈ sy.attach, a.val.1 ⊗ₜ[R] a.val.2) = y
      rw [Finset.sum_attach sy (fun a : K × S ↦ a.1 ⊗ₜ[R] a.2)]
      exact hy.symm
  have hnontrivial : Nontrivial (K ⊗[R] S) := by
    let s : Finset K := ∅
    have := hdomain s
    exact Function.Injective.nontrivial (hinj (IntermediateField.adjoin k (s : Set K)))
  have : NoZeroDivisors (K ⊗[R] S) := ⟨by
    intro x y hxy
    obtain ⟨s, x', y', hx, hy⟩ := hlift x y
    let F := IntermediateField.adjoin k (s : Set K)
    let f := Algebra.TensorProduct.map (F.val.restrictScalars R) (AlgHom.id R S)
    have hf : Function.Injective f := hinj F
    have := hdomain s
    have hx' : f x' = x := hx
    have hy' : f y' = y := hy
    have h : x' * y' = 0 := hf (by simpa only [map_mul, hx', hy', map_zero] using hxy)
    exact (eq_zero_or_eq_zero_of_mul_eq_zero h).imp
      (fun h ↦ by rw [← hx, h, map_zero]) (fun h ↦ by rw [← hy, h, map_zero])⟩
  exact NoZeroDivisors.to_isDomain _

/-- The maximal ideal extension is prime under geometric integrality of the fibres.

Source: Stacks Project, Tag 05I3, `lemma-induction-step`, implication (1)⇒(2).
(blueprint: lem-trf-local-generic-basis-universal-injective)

Proof: use `geometricFibres_domain_baseChange` at the maximal ideal, with its residue
field and the identity residue-field extension. This yields that the closed fibre is a
domain in its own universe. Since `R` is local, this fibre is canonically isomorphic to
`S` modulo the extended maximal ideal. A quotient is a nonzero domain exactly when its
ideal is prime. This is the derived canonical structure used
by the main statement; no prime ideal is assumed separately.
-/
theorem maximalIdeal_map_isPrime_of_geometricFibres
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R]
    (hgeom : ∀ (p : PrimeSpectrum R) (K : Type (max u v w)) [Field K]
      [Algebra R K] (ι : p.asIdeal.ResidueField →+* K),
      algebraMap R K = ι.comp (algebraMap R p.asIdeal.ResidueField) →
      IsDomain (K ⊗[R] S)) :
    Ideal.IsPrime (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) := by
  let m := IsLocalRing.maximalIdeal R
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  let e : (R ⧸ m) ≃ₐ[R] m.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ m) m.ResidueField)
      m.bijective_algebraMap_quotient_residueField
  have hd : IsDomain ((R ⧸ m) ⊗[R] S) :=
    geometricFibres_domain_baseChange hgeom ⟨m, inferInstance⟩ (R ⧸ m)
      e.symm.toRingHom (by ext x; exact (e.symm.commutes x).symm)
  exact (Ideal.Quotient.isDomain_iff_prime _).mp
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor S m).toMulEquiv.isDomain _)

private theorem projective_of_fibres
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hflat : RingHom.Flat (algebraMap R S))
    (hfp : RingHom.FinitePresentation (algebraMap R S))
    (hgeom : ∀ (p : PrimeSpectrum R) (K : Type (max u v w)) [Field K]
      [Algebra R K] (ι : p.asIdeal.ResidueField →+* K),
      algebraMap R K = ι.comp (algebraMap R p.asIdeal.ResidueField) →
      IsDomain (K ⊗[R] S)) : Module.Projective R S := by
  have : Algebra.FinitePresentation R S := (finitePresentation_algebraMap).mp hfp
  apply Algebra.projective_of_geometricallyIntegral_fibres.{u, v, w} R S hflat
  intro p K _ _ i hi
  let e := (AlgebraicGeometry.Scheme.Spec.residueFieldIso (.of R) p).commRingCatIsoToRingEquiv
  have he : e.symm.toRingHom.comp (algebraMap R p.asIdeal.ResidueField) =
      (CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Scheme.ΓSpecIso (.of R)).inv
        ((AlgebraicGeometry.Spec (.of R)).Γevaluation p)).hom := by
    exact congrArg (fun f : CommRingCat.of R ⟶ _ ↦ f.hom)
      (AlgebraicGeometry.Scheme.Spec.algebraMap_residueFieldIso_inv (.of R) p)
  have hd := geometricFibres_domain_baseChange hgeom p K (i.comp e.symm.toRingHom)
    (by rw [RingHom.comp_assoc, he]; exact hi)
  exact (Algebra.TensorProduct.comm R S K).toMulEquiv.isDomain _

private theorem residue_injective_of_generic
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] (p q : Ideal S) [p.IsPrime] [q.IsPrime]
    (hp : p = (IsLocalRing.maximalIdeal R).map (algebraMap R S)) (hpq : p ≤ q)
    (r : ℕ) {N : Type t} [AddCommGroup N] [Module S N] [Module R N]
    [IsScalarTower R S N] (α : (Fin r → S) →ₗ[S] N)
    (hα : Function.Bijective (α.lTensor p.ResidueField)) :
    Function.Injective
      ((((LocalizedModule.mkLinearMap q.primeCompl N).comp α).restrictScalars R).lTensor
        (IsLocalRing.ResidueField R)) := by
  classical
  let E := p.ResidueField
  let V := Fin r → E
  let e : E ⊗[S] (Fin r → S) ≃ₗ[E] E ⊗[S] N :=
    LinearEquiv.ofBijective (α.baseChange E) hα
  let c := TensorProduct.piScalarRight S E E (Fin r)
  let a : N →ₗ[S] V :=
    (c.toLinearMap.restrictScalars S).comp
      ((e.symm.toLinearMap.restrictScalars S).comp (TensorProduct.mk S E N 1))
  have ha (x : Fin r → S) (i : Fin r) : a (α x) i = algebraMap S E (x i) := by
    change c (e.symm (1 ⊗ₜ[S] α x)) i = _
    have he : e (1 ⊗ₜ[S] x) = 1 ⊗ₜ[S] α x := rfl
    rw [← he, e.symm_apply_apply]
    simp [c, Algebra.smul_def]
  have hu (x : q.primeCompl) : IsUnit (algebraMap S (Module.End S V) x) := by
    have hx : IsUnit (algebraMap S E x) :=
      isUnit_iff_ne_zero.mpr (fun h ↦ x.property (hpq
        (Ideal.algebraMap_residueField_eq_zero.mp h)))
    convert hx.map (Algebra.lsmul S S V) using 1
    rw [AlgHom.commutes]
  let g : LocalizedModule q.primeCompl N →ₗ[S] V :=
    LocalizedModule.lift q.primeCompl a hu
  let gR := g.restrictScalars R
  let m := IsLocalRing.maximalIdeal R
  have hg : m • (⊤ : Submodule R (LocalizedModule q.primeCompl N)) ≤
      LinearMap.ker gR := by
    apply Submodule.smul_le.mpr
    intro b hb x _
    change gR (b • x) = 0
    rw [gR.map_smul]
    ext i
    change b • (g x i) = 0
    rw [← IsScalarTower.algebraMap_smul S b (g x i), Algebra.smul_def]
    have hb' : algebraMap R S b ∈ p := by
      rw [hp]
      exact Ideal.mem_map_of_mem _ hb
    rw [Ideal.algebraMap_residueField_eq_zero.mpr hb', zero_mul]
  let H : IsLocalRing.ResidueField R ⊗[R] LocalizedModule q.primeCompl N →ₗ[R] V :=
    ((m • (⊤ : Submodule R (LocalizedModule q.primeCompl N))).liftQ gR hg).comp
      (TensorProduct.quotTensorEquivQuotSMul _ m).toLinearMap
  let eqp := Ideal.quotientEquivAlgOfEq R hp.symm
  let eqt := (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S m).symm.restrictScalars R
  let d : IsLocalRing.ResidueField R ⊗[R] S →ₗ[R] E :=
    (IsScalarTower.toAlgHom R (S ⧸ p) E).toLinearMap.comp
      (eqp.toLinearMap.comp eqt.toLinearMap)
  have hd : Function.Injective d :=
    (p.injective_algebraMap_quotient_residueField.comp eqp.injective).comp eqt.injective
  have hd_one (s : S) : d (1 ⊗ₜ[R] s) = algebraMap S E s := by
    change algebraMap (S ⧸ p) E (eqp (eqt (1 ⊗ₜ[R] s))) = _
    have ht : eqt (1 ⊗ₜ[R] s) = Ideal.Quotient.mk (m.map (algebraMap R S)) s :=
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S m).symm_apply_eq.mpr
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk S m s).symm
    rw [ht, Ideal.quotientEquivAlgOfEq_mk, Ideal.algebraMap_quotient_residueField_mk]
  let cp := TensorProduct.piRight R R (IsLocalRing.ResidueField R) (fun _ : Fin r ↦ S)
  let D : IsLocalRing.ResidueField R ⊗[R] (Fin r → S) →ₗ[R] V :=
    (LinearMap.pi fun i ↦ d.comp (LinearMap.proj i)).comp cp.toLinearMap
  have hD : Function.Injective D := by
    intro x y h
    apply cp.injective
    funext i
    apply hd
    exact congrFun h i
  have hfactor : H.comp
      ((((LocalizedModule.mkLinearMap q.primeCompl N).comp α).restrictScalars R).lTensor
        (IsLocalRing.ResidueField R)) = D := by
    apply TensorProduct.ext'
    intro b x
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective b
    rw [show IsLocalRing.residue R b = b • (1 : IsLocalRing.ResidueField R) by
      rw [Algebra.smul_def, mul_one]; rfl, TensorProduct.smul_tmul]
    generalize b • x = y
    ext i
    change H (1 ⊗ₜ[R] LocalizedModule.mk (α y) 1) i = _
    change ((m • (⊤ : Submodule R (LocalizedModule q.primeCompl N))).liftQ gR hg)
      (TensorProduct.quotTensorEquivQuotSMul _ m
        (1 ⊗ₜ[R] LocalizedModule.mk (α y) 1)) i = _
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.liftQ_apply]
    change g (LocalizedModule.mk (α y) 1) i = _
    rw [LocalizedModule.lift_mk_one, ha]
    change algebraMap S E (y i) = d (1 ⊗ₜ[R] y i)
    exact (hd_one _).symm
  rw [← hfactor] at hD
  exact fun x y h ↦ hD (congrArg H h)

private theorem compHom_eq_of_tower
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type t) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] :
    Module.compHom M (algebraMap R S) = (inferInstance : Module R M) := by
  apply Module.ext'
  intro a x
  exact IsScalarTower.algebraMap_smul S a x

private theorem lTensor_injective_of_lift
    {R : Type u} [CommRing R]
    {M : Type v} {N : Type t} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N)
    (hf : ∀ (L : Type (max u v t z)) [AddCommGroup L] [Module R L],
      Function.Injective (f.lTensor L))
    (L : Type z) [AddCommGroup L] [Module R L] : Function.Injective (f.lTensor L) := by
  let e : ULift.{max u v t} L ≃ₗ[R] L := ULift.moduleEquiv
  let eM := TensorProduct.congr e (LinearEquiv.refl R M)
  let eN := TensorProduct.congr e (LinearEquiv.refl R N)
  have hcomm : eN.toLinearMap.comp (f.lTensor (ULift.{max u v t} L)) =
      (f.lTensor L).comp eM.toLinearMap := by
    ext x y
    rfl
  intro x y hxy
  apply eM.symm.injective
  apply hf (ULift.{max u v t} L)
  apply eN.injective
  change (eN.toLinearMap.comp (f.lTensor (ULift.{max u v t} L))) (eM.symm x) =
    (eN.toLinearMap.comp (f.lTensor (ULift.{max u v t} L))) (eM.symm y)
  rw [hcomm]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hxy

/-- A generic-basis map into a finite module over a flat finitely presented algebra is
universally injective, with flat localized cokernel.

Source: Stacks Project, Tag 05I3, `lemma-induction-step`, implication (1)⇒(2).
(blueprint: lem-trf-local-generic-basis-universal-injective)

Proof:
1. Use `maximalIdeal_map_isPrime_of_geometricFibres` to obtain primality of `ξ = mS`.
   The node `lem-trf-local-fibres-integral-projective`, recorded as
   `Algebra.projective_of_geometricallyIntegral_fibres`, gives projectivity of `S`
   over `R`, hence of `S^r`. Tensor symmetry and `Spec.residueFieldIso` identify
   its fibre hypothesis with `hgeom`; `geometricFibres_domain_baseChange` handles
   arbitrary universes of field extensions.
2. Reduce `S^r → N_q` modulo `m`. Its composite to `N ⊗[S] κ(ξ)` factors through
   the injection `(S/mS)^r → κ(ξ)^r` and the isomorphism induced by `α`.
   Here `ξ ⊆ q`, so localization at `ξ` factors through localization at `q`.
   Consequently the reduction is injective. Apply
   `lem-trf-local-universal-injective-residue`, recorded as
   `Module.universallyInjective_of_residueField_injective`, to the projective
   source and the flat module `N_q`. This makes `S^r → N_q` universally injective.
3. This map is the composite of `α` with `N → N_q`. Injectivity of that composite
   after tensoring makes `α` universally injective. By
   `lem-trf-local-universal-injective-localization`, recorded as
   `LinearMap.universally_injective_localizedModule_map`, the map localized at `q`
   is also universally injective. Tensor right exactness now makes the localized
   cokernel sequence universally exact. Apply `lem-trf-local-ui-flat-cokernel`,
   recorded as `Module.flat_of_universally_exact`, with flat middle term `N_q`.
   This gives flatness of `(coker α)_q`.

The cases `r = 0`, the zero module and a field base use the same tensor and quotient
constructions. Restricted `R`-actions on localized modules are explicitly `Module.compHom`.
The compatible `R`-action on `N` is its unique restriction along `R → S`.
-/
theorem local_generic_basis_universal_injective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R]
    (hflat : RingHom.Flat (algebraMap R S))
    (hfp : RingHom.FinitePresentation (algebraMap R S))
    (hgeom : ∀ (p : PrimeSpectrum R) (K : Type (max u v w)) [Field K]
      [Algebra R K] (ι : p.asIdeal.ResidueField →+* K),
      algebraMap R K = ι.comp (algebraMap R p.asIdeal.ResidueField) →
      IsDomain (K ⊗[R] S))
    (r : ℕ) (N : Type t) [AddCommGroup N] [Module S N] [Module R N]
    [IsScalarTower R S N] [Module.Finite S N]
    (q : PrimeSpectrum S)
    (hq : q.asIdeal.comap (algebraMap R S) = IsLocalRing.maximalIdeal R)
    (hNq : @Module.Flat R (LocalizedModule q.asIdeal.primeCompl N) _ _
      (Module.compHom (LocalizedModule q.asIdeal.primeCompl N) (algebraMap R S)))
    (α : (Fin r → S) →ₗ[S] N)
    (hα : Function.Bijective
      (LinearMap.lTensor
        (@Ideal.ResidueField S _ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
          (maximalIdeal_map_isPrime_of_geometricFibres (R := R) (S := S) hgeom)) α)) :
    (∀ (L : Type z) [AddCommGroup L] [Module R L],
      Function.Injective (LinearMap.lTensor L (α.restrictScalars R))) ∧
      @Module.Flat R (LocalizedModule q.asIdeal.primeCompl (N ⧸ LinearMap.range α)) _ _
        (Module.compHom (LocalizedModule q.asIdeal.primeCompl (N ⧸ LinearMap.range α))
          (algebraMap R S)) := by
  classical
  have : Module.Projective R S := projective_of_fibres hflat hfp hgeom
  have : Module.Projective R (Fin r → S) :=
    Module.Projective.of_equiv'
      (DirectSum.linearEquivFunOnFintype R (Fin r) (fun _ ↦ S))
  let T := q.asIdeal.primeCompl
  let nq := LocalizedModule.mkLinearMap T N
  let f := (nq.comp α).restrictScalars R
  let : Module.Flat R (LocalizedModule T N) := by
    rwa [compHom_eq_of_tower] at hNq
  have hp : (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤ q.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr hq.ge
  let p := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  have : p.IsPrime := maximalIdeal_map_isPrime_of_geometricFibres hgeom
  have hres : Function.Injective (f.lTensor (IsLocalRing.ResidueField R)) :=
    residue_injective_of_generic p q.asIdeal rfl hp r α hα
  have hf : ∀ (L : Type (max u v t z)) [AddCommGroup L] [Module R L],
      Function.Injective (f.lTensor L) := by
    intro L _ _
    exact Module.universallyInjective_of_residueField_injective f hres L
  have hαui : ∀ (L : Type (max u v t z)) [AddCommGroup L] [Module R L],
      Function.Injective ((α.restrictScalars R).lTensor L) := by
    intro L _ _ x y hxy
    apply hf L
    change ((nq.restrictScalars R).comp (α.restrictScalars R)).lTensor L x =
      ((nq.restrictScalars R).comp (α.restrictScalars R)).lTensor L y
    rw [LinearMap.lTensor_comp]
    exact congrArg ((nq.restrictScalars R).lTensor L) hxy
  refine ⟨lTensor_injective_of_lift (α.restrictScalars R) hαui, ?_⟩
  let β := (LinearMap.range α).mkQ
  let fl := (LocalizedModule.map T α).restrictScalars R
  let gl := (LocalizedModule.map T β).restrictScalars R
  have hex : Function.Exact fl gl :=
    LocalizedModule.map_exact T α β (LinearMap.exact_map_mkQ_range α)
  have hsur : Function.Surjective gl :=
    IsLocalizedModule.map_surjective T _ _ β (Submodule.mkQ_surjective _)
  rw [compHom_eq_of_tower]
  apply Module.flat_of_universally_exact.{u, v, max v t, max v t, max v t z} fl gl
  intro L _ _
  refine ⟨?_, rTensor_exact L hex hsur, gl.rTensor_surjective L hsur⟩
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  exact LinearMap.universally_injective_localizedModule_map T α hαui L

end RingHom
