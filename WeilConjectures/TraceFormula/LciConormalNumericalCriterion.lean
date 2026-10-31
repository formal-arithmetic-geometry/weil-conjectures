/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.CompleteIntersectionLocal
public import WeilConjectures.SixFunctors.TraceFormula.LciConormalFibreFieldChange
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.FiniteType
import all WeilConjectures.AlgebraicGeometry.DimensionAtPointFieldExtension
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import WeilConjectures.TraceFormula.CILocalRingPrincipalNeighbourhood
import WeilConjectures.RingTheory.LciConormalFreeRankCodimension
import WeilConjectures.RingTheory.ConormalGeneratorsGlobalCompleteIntersection
import WeilConjectures.RingTheory.GlobalCompleteIntersectionLocalRegularSequence
import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# Numerical conormal criterion for a local complete intersection

Source: Stacks Project, Algebra, Tags 00SC and 00SF
(blueprint: lem-trf-lci-conormal-numerical-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace Algebra

private theorem global_ci_of_equiv
    {k T U : Type*} [Field k] [CommRing T] [CommRing U]
    [Algebra k T] [Algebra k U] (E : T ≃ₐ[k] U)
    (h : IsGlobalCompleteIntersection k T) : IsGlobalCompleteIntersection k U := by
  rcases h with hz | ⟨n, c, f, hcn, ⟨e⟩, hd⟩
  · exact Or.inl (E.toEquiv.subsingleton_congr.mp hz)
  · refine Or.inr ⟨n, c, f, hcn, ⟨e.trans E⟩, ?_⟩
    rw [← (PrimeSpectrum.homeomorphOfRingEquiv E.toRingEquiv).isHomeomorph.topologicalKrullDim_eq]
    exact hd

private theorem neighbourhood_of_equiv
    {k T U : Type*} [Field k] [CommRing T] [CommRing U]
    [Algebra k T] [Algebra k U] (E : T ≃ₐ[k] U)
    (q : Ideal U) [q.IsPrime]
    (h : ∃ g : T, g ∉ q.comap E.toRingHom ∧
      IsGlobalCompleteIntersection k (Localization.Away g)) :
    ∃ g : U, g ∉ q ∧ IsGlobalCompleteIntersection k (Localization.Away g) := by
  obtain ⟨g, hg, hci⟩ := h
  let EH : Localization.Away g ≃ₐ[k] Localization.Away (E g) :=
    IsLocalization.algEquivOfAlgEquiv
      (M := .powers g) (T := .powers (E g))
      (Localization.Away g) (Localization.Away (E g)) E (Submonoid.map_powers E g)
  exact ⟨E g, hg, global_ci_of_equiv EH hci⟩

private theorem ci_of_regular_presentation
    (k : Type u) [Field k] (B : Type v) [CommRing B] [Algebra k B]
    [IsLocalRing B] [EssFiniteType k B]
    (R : Type u) [CommRing R] [Algebra k R] [IsRegularLocalRing R]
    [EssFiniteType k R] (xs : List R) (hr : RingTheory.Sequence.IsRegular R xs)
    (hm : ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R)
    (e : (R ⧸ Ideal.ofList xs) ≃ₐ[k] B) : IsCompleteIntersectionLocal k B := by
  let S := ULift.{v} R
  let E : R ≃ₐ[k] S := ULift.algEquiv.symm
  have : IsRegularLocalRing S := IsRegularLocalRing.of_ringEquiv E.toRingEquiv
  have : EssFiniteType k S := (EssFiniteType.iff_of_algEquiv E).mp inferInstance
  let ys := xs.map E
  have hy : RingTheory.Sequence.IsRegular S ys :=
    (E.toRingEquiv.toAddEquiv.isRegular_congr
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr
        (fun r _ x => E.map_mul r x)))).mp hr
  have hym : ∀ y ∈ ys, y ∈ IsLocalRing.maximalIdeal S := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal E.toRingEquiv]
    exact Ideal.mem_map_of_mem _ (hm x hx)
  let EQ : (R ⧸ Ideal.ofList xs) ≃ₐ[k] S ⧸ Ideal.ofList ys :=
    Ideal.quotientEquivAlg _ _ E (Ideal.map_ofList E.toRingHom xs).symm
  exact ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, ys,
    hy, hym, ⟨EQ.symm.trans e⟩⟩

private theorem ci_of_global_at_prime
    (k : Type u) [Field k] (T B : Type v) [CommRing T] [Algebra k T]
    [CommRing B] [Algebra k B] [IsLocalRing B] [EssFiniteType k B]
    (q : Ideal T) [q.IsPrime] (e : Localization.AtPrime q ≃ₐ[k] B)
    (h : IsGlobalCompleteIntersection k T) : IsCompleteIntersectionLocal k B := by
  classical
  have : Nontrivial T := (⟨q, inferInstance⟩ : PrimeSpectrum T).nontrivial
  rcases h with hz | ⟨m, t, f, htm, ⟨E⟩, hdim⟩
  · exact False.elim (zero_ne_one (hz.elim 0 1))
  let P := MvPolynomial (Fin m) k
  let I := Ideal.span (Set.range f)
  let r := q.comap E.toRingHom
  let p := r.comap (Ideal.Quotient.mk I)
  let R := Localization.AtPrime p
  let J := I.map (algebraMap P R)
  let xs := (List.ofFn f).map (algebraMap P R)
  have : Nontrivial (P ⧸ I) := E.toEquiv.nontrivial
  have hdim' : topologicalKrullDim (PrimeSpectrum (P ⧸ I)) + (t : WithBot ℕ∞) = m := by
    rw [(PrimeSpectrum.homeomorphOfRingEquiv E.toRingEquiv).isHomeomorph.topologicalKrullDim_eq,
      hdim, ← Nat.cast_add, Nat.sub_add_cancel htm]
  have hIp : I ≤ p := Ideal.le_comap_of_map_le (by simp [r])
  have hr : RingTheory.Sequence.IsRegular R xs :=
    MvPolynomial.isRegular_localizationAtPrime_of_quotient_dimension k m t f hdim' p hIp
  have hxs : Ideal.ofList (List.ofFn f) = I := by
    change Ideal.span {x | x ∈ List.ofFn f} = I
    congr 1
    ext x
    simp [Set.mem_range]
  have hJ : Ideal.ofList xs = J := by
    change Ideal.ofList ((List.ofFn f).map (algebraMap P R)) = J
    rw [← Ideal.map_ofList, hxs]
  have hm : ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff R p a).mpr
    exact hIp (by rw [← hxs]; exact Ideal.subset_span ha)
  have hM : Algebra.algebraMapSubmonoid (P ⧸ I) p.primeCompl = r.primeCompl :=
    r.map_primeCompl_comap_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsLocalization r.primeCompl (R ⧸ J) := by rw [← hM]; infer_instance
  have : IsScalarTower k (P ⧸ I) (R ⧸ J) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    rfl
  let EQ : (R ⧸ J) ≃ₐ[k] Localization.AtPrime r :=
    (IsLocalization.algEquiv r.primeCompl (R ⧸ J) (Localization.AtPrime r)).restrictScalars k
  let EL : Localization.AtPrime r ≃ₐ[k] Localization.AtPrime q :=
    Localization.localAlgEquiv r q E rfl
  exact ci_of_regular_presentation k B R xs hr hm
    ((Ideal.quotientEquivAlgOfEq k hJ).trans (EQ.trans (EL.trans e)))

private theorem ci_of_neighbourhood
    (k : Type u) [Field k] (C : Type v) [CommRing C] [Algebra k C]
    [FiniteType k C] (q : Ideal C) [q.IsPrime]
    (h : ∃ g : C, g ∉ q ∧ IsGlobalCompleteIntersection k (Localization.Away g)) :
    IsCompleteIntersectionLocal k (Localization.AtPrime q) := by
  obtain ⟨g, hg, hci⟩ := h
  have hin : (⟨q, inferInstance⟩ : PrimeSpectrum C) ∈
      Set.range (PrimeSpectrum.comap (algebraMap C (Localization.Away g))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
    exact hg
  obtain ⟨p, hp⟩ := hin
  have hp' : p.asIdeal.comap (algebraMap C (Localization.Away g)) = q :=
    congrArg PrimeSpectrum.asIdeal hp
  let E : Localization.AtPrime q ≃ₐ[k] Localization.AtPrime p.asIdeal := by
    subst q
    exact (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (Submonoid.powers g) p.asIdeal).restrictScalars k
  exact ci_of_global_at_prime k (Localization.Away g) (Localization.AtPrime q)
    p.asIdeal E.symm hci

private theorem residue_generators (R M : Type*) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (c : ℕ)
    (h : Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] M) = c) :
    ∃ g : Fin c → M, Submodule.span R (Set.range g) = ⊤ := by
  classical
  let b := Module.finBasisOfFinrankEq (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField R ⊗[R] M) h
  have hlift (i : Fin c) : ∃ x : M, 1 ⊗ₜ[R] x = b i :=
    _root_.TensorProduct.mk_surjective R M (IsLocalRing.ResidueField R)
      Ideal.Quotient.mk_surjective (b i)
  choose g hg using hlift
  exact ⟨g, IsLocalRing.span_eq_top_of_tmul_eq_basis g b hg⟩

private theorem quotient_conormal_fibre_finrank
    {P : Type*} [CommRing P] (I : Ideal P)
    (q : Ideal (P ⧸ I)) [q.IsPrime] :
    Module.finrank (q.comap (Ideal.Quotient.mk I)).ResidueField
        (AlgebraicGeometry.lciConormalFibre (q.comap (Ideal.Quotient.mk I)) I) =
      Module.finrank q.ResidueField
        (q.ResidueField ⊗[Localization.AtPrime q]
          LocalizedModule q.primeCompl I.Cotangent) := by
  let p := q.comap (Ideal.Quotient.mk I)
  let F := p.ResidueField
  let L := q.ResidueField
  let σ := Ideal.ResidueField.map p q (Ideal.Quotient.mk I) rfl
  let : Algebra F L := σ.toAlgebra
  let : Algebra (Localization.AtPrime p) L :=
    (σ.comp (algebraMap (Localization.AtPrime p) F)).toAlgebra
  have : IsScalarTower (Localization.AtPrime p) F L :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower P F L := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (Ideal.ResidueField.map_algebraMap p q (Ideal.Quotient.mk I) rfl x).symm)
  have : IsScalarTower P (Localization.AtPrime p) L := by
    exact IsScalarTower.of_algebraMap_eq' (by
      change algebraMap P L =
        (σ.comp (algebraMap (Localization.AtPrime p) F)).comp
          (algebraMap P (Localization.AtPrime p))
      rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
      exact IsScalarTower.algebraMap_eq P F L)
  let eP := LocalizedModule.equivTensorProduct p.primeCompl I.Cotangent
  let eQ := LocalizedModule.equivTensorProduct q.primeCompl I.Cotangent
  let e₁ := _root_.TensorProduct.AlgebraTensorModule.cancelBaseChange
    (Localization.AtPrime p) F L L (LocalizedModule p.primeCompl I.Cotangent)
  let e₂ := LinearEquiv.baseChange (Localization.AtPrime p) L _ _ eP
  let e₃ := _root_.TensorProduct.AlgebraTensorModule.cancelBaseChange
    P (Localization.AtPrime p) L L I.Cotangent
  let e₄ := _root_.TensorProduct.AlgebraTensorModule.cancelBaseChange
    (P ⧸ I) (Localization.AtPrime q) L L I.Cotangent
  let e₅ := LinearEquiv.baseChange (Localization.AtPrime q) L _ _ eQ
  have : _root_.TensorProduct.CompatibleSMul P (P ⧸ I) L I.Cotangent :=
    _root_.TensorProduct.CompatibleSMul.of_algebraMap_surjective L I.Cotangent
      Ideal.Quotient.mk_surjective
  let e₆ : L ⊗[P ⧸ I] I.Cotangent ≃ₗ[L] L ⊗[P] I.Cotangent :=
    _root_.TensorProduct.equivOfCompatibleSMul P (P ⧸ I) L L I.Cotangent
  have hbc := Module.finrank_baseChange (R := L) (S := F)
    (M' := AlgebraicGeometry.lciConormalFibre p I)
  exact hbc.symm.trans ((e₁.trans (e₂.trans e₃)).finrank_eq.trans
    ((e₅.trans e₄).trans e₆).finrank_eq.symm)

private theorem quotient_neighbourhood_iff_finrank
    (k : Type u) [Field k] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k))
    (q : Ideal (MvPolynomial (Fin n) k ⧸ I)) [q.IsPrime] :
    (∃ g : MvPolynomial (Fin n) k ⧸ I, g ∉ q ∧
      IsGlobalCompleteIntersection k (Localization.Away g)) ↔
    ∃ d : ℕ,
      topologicalKrullDimAt (⟨q, inferInstance⟩ : PrimeSpectrum _) = (d : WithBot ℕ∞) ∧
      d ≤ n ∧ Module.finrank (q.comap (Ideal.Quotient.mk I)).ResidueField
        (AlgebraicGeometry.lciConormalFibre (q.comap (Ideal.Quotient.mk I)) I) = n - d := by
  rw [quotient_conormal_fibre_finrank]
  let R := Localization.AtPrime q
  let M := LocalizedModule q.primeCompl I.Cotangent
  constructor
  · intro hci
    obtain ⟨d, hd, hdn, ⟨b⟩⟩ :=
      Ideal.exists_basis_cotangent_localization_of_completeIntersection n I
        ⟨q, inferInstance⟩ hci
    refine ⟨d, hd, hdn, ?_⟩
    simpa using Module.finrank_eq_card_basis (b.baseChange q.ResidueField)
  · rintro ⟨d, hd, hdn, hr⟩
    have : Module.Finite (MvPolynomial (Fin n) k ⧸ I) I.Cotangent :=
      Module.Finite.of_restrictScalars_finite (MvPolynomial (Fin n) k) _ _
    have : Module.Finite R M := Module.Finite.of_isLocalizedModule
      q.primeCompl (LocalizedModule.mkLinearMap q.primeCompl I.Cotangent)
    obtain ⟨g, hg⟩ := residue_generators R M (n - d) hr
    obtain ⟨d', hd', _, hcrit⟩ := conormal_generators_global_complete_intersection k n I q
    have he : d' = d := by exact_mod_cast hd'.symm.trans hd
    subst d'
    exact hcrit ⟨g, hg⟩

/-- In a fixed finite polynomial presentation, a local ring is a complete
intersection precisely when the conormal fibre dimension equals the codimension.

Source: Stacks Project, Algebra, Tag 00SC, conditions (1), (3), (4), (5), and
Tag 00SF, independence of the regular local presentation.
(blueprint: lem-trf-lci-conormal-numerical-criterion).

Proof: Replace the presented algebra by the quotient by the kernel. The induced
isomorphisms preserve the local ring, the residue field and local topological
dimension. A complete-intersection presentation gives a regular-sequence kernel
in the polynomial local ring by 00SF. Spread it to a principal neighbourhood by
00SC, (5) implies (1). The conormal rank theorem gives a basis of size n-d;
reducing that basis to the residue field gives the displayed dimension. Conversely,
the conormal module is finite because the polynomial ring is Noetherian. Lift a
basis of its residue fibre to n-d local generators by Nakayama. The conormal
generator criterion 00SC gives a principal global-complete-intersection
neighbourhood. Its regular equations, localized at the given prime, present the
local ring as a quotient of a regular polynomial local ring. Transport this
presentation back to the original algebra. Empty bases and empty regular sequences
are allowed, so the proof includes codimension zero. -/
theorem isCompleteIntersectionLocal_iff_conormal_finrank
    (k : Type u) (C : Type v) [Field k] [CommRing C] [Algebra k C]
    [FiniteType k C] (n : ℕ) (π : MvPolynomial (Fin n) k →ₐ[k] C)
    (hπ : Function.Surjective π) (q : Ideal C) [q.IsPrime] :
    IsCompleteIntersectionLocal k (Localization.AtPrime q) ↔
      ∃ d : ℕ,
        topologicalKrullDimAt (⟨q, inferInstance⟩ : PrimeSpectrum C) =
          (d : WithBot ℕ∞) ∧ d ≤ n ∧
        Module.finrank (q.comap π.toRingHom).ResidueField
          (AlgebraicGeometry.lciConormalFibre (q.comap π.toRingHom)
            (RingHom.ker π.toRingHom)) = n - d := by
  classical
  let I := RingHom.ker π.toRingHom
  let E : (MvPolynomial (Fin n) k ⧸ I) ≃ₐ[k] C :=
    Ideal.quotientKerAlgEquivOfSurjective hπ
  let r := q.comap E.toRingHom
  have hp : r.comap (Ideal.Quotient.mk I) = q.comap π.toRingHom := by
    ext x
    change E (Ideal.Quotient.mk I x) ∈ q ↔ π x ∈ q
    exact congrArg (fun y : C => y ∈ q)
      (Ideal.quotientKerAlgEquivOfSurjective_mk hπ x) |>.to_iff
  have hdim : topologicalKrullDimAt (⟨r, inferInstance⟩ : PrimeSpectrum _) =
      topologicalKrullDimAt (⟨q, inferInstance⟩ : PrimeSpectrum C) :=
    (AlgebraicGeometry.localDim_homeomorph
      (PrimeSpectrum.homeomorphOfRingEquiv E.toRingEquiv).symm
      (⟨q, inferInstance⟩ : PrimeSpectrum C)).symm
  have hcrit := quotient_neighbourhood_iff_finrank k n I r
  have hnum : (∃ d : ℕ,
      topologicalKrullDimAt (⟨r, inferInstance⟩ : PrimeSpectrum _) = (d : WithBot ℕ∞) ∧
      d ≤ n ∧ Module.finrank (r.comap (Ideal.Quotient.mk I)).ResidueField
        (AlgebraicGeometry.lciConormalFibre (r.comap (Ideal.Quotient.mk I)) I) = n - d) ↔
      (∃ d : ℕ,
      topologicalKrullDimAt (⟨q, inferInstance⟩ : PrimeSpectrum C) = (d : WithBot ℕ∞) ∧
      d ≤ n ∧ Module.finrank (q.comap π.toRingHom).ResidueField
        (AlgebraicGeometry.lciConormalFibre (q.comap π.toRingHom) I) = n - d) := by
    rw [hdim]
    have he : Module.finrank (r.comap (Ideal.Quotient.mk I)).ResidueField
        (AlgebraicGeometry.lciConormalFibre (r.comap (Ideal.Quotient.mk I)) I) =
        Module.finrank (q.comap π.toRingHom).ResidueField
        (AlgebraicGeometry.lciConormalFibre (q.comap π.toRingHom) I) := by
      exact (show ∀ (p q : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] [q.IsPrime],
          p = q → Module.finrank p.ResidueField (AlgebraicGeometry.lciConormalFibre p I) =
            Module.finrank q.ResidueField (AlgebraicGeometry.lciConormalFibre q I) from by
        intro p q _ _ h
        subst q
        rfl) _ _ hp
    simp only [he]
  rw [← hnum, ← hcrit]
  constructor
  · rintro ⟨R, _, _, _, _, xs, hr, hm, ⟨e⟩⟩
    let EL : Localization.AtPrime r ≃ₐ[k] Localization.AtPrime q :=
      Localization.localAlgEquiv r q E rfl
    exact TraceFormula.ciLocalRingPrincipalNeighbourhood k _
      (RingHom.finiteType_algebraMap.mpr inferInstance) r R xs hr hm
      (EL.trans e.symm)
  · intro h
    exact ci_of_neighbourhood k C q (neighbourhood_of_equiv E q h)

end Algebra
