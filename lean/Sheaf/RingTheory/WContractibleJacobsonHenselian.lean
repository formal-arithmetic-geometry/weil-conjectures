/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import WeilConjectures.RingTheory.ProEtale.WContractible
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Finiteness.Basic
import WeilConjectures.RingTheory.PairHenselizationFlatQuotients
import WeilConjectures.RingTheory.HenselianIntegralIdempotentLifting

/-! # The Jacobson radical of a w-contractible ring is henselian

Source: Ruimy--Tubach--Wolf, Pro-etale motives and solid rigidity, Proposition 1.1.2;
Stacks Project, Tags 0A02, 0AGU, 09XI, 0982 and 00HP
(blueprint: lem-sfb-wcontractible-jacobson-henselian).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RingTheory

/-- Simple roots descend along a retraction preserving the extended ideal: map the
polynomial and its approximate root into the henselian ring, lift there, and apply the
retraction. The quotient map preserves the derivative's invertibility, and the image
of the extended ideal under the retraction is the original ideal. -/
private theorem henselian_of_retraction {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥) (η : R →+* S) (ρ : S →+* R)
    (hρ : ρ.comp η = RingHom.id R) [HenselianRing S (I.map η)] :
    HenselianRing R I := by
  have hmap : (I.map η).map ρ = I := by
    rw [Ideal.map_map, hρ, Ideal.map_id]
  have hpoint (r : R) : ρ (η r) = r := congrArg (fun f : R →+* R ↦ f r) hρ
  refine ⟨hI, ?_⟩
  intro f hf a₀ ha₀ hu
  let q := Ideal.quotientMap (I.map η) η Ideal.le_comap_map
  have hval : (f.map η).eval (η a₀) ∈ I.map η := by
    rw [Polynomial.eval_map_apply]
    exact Ideal.mem_map_of_mem η ha₀
  have hunit : IsUnit (Ideal.Quotient.mk (I.map η)
      ((f.map η).derivative.eval (η a₀))) := by
    rw [Polynomial.derivative_map, Polynomial.eval_map_apply]
    exact hu.map q
  obtain ⟨a, ha, hdiff⟩ := HenselianRing.is_henselian (f.map η) (hf.map η)
    (η a₀) hval hunit
  refine ⟨ρ a, ?_, ?_⟩
  · have hpoly : (f.map η).map ρ = f := by
      rw [Polynomial.map_map, hρ, Polynomial.map_id]
    rw [Polynomial.IsRoot.def, ← hpoly, Polynomial.eval_map_apply,
      Polynomial.IsRoot.def.mp ha, map_zero]
  · have hm := Ideal.mem_map_of_mem ρ hdiff
    rwa [hmap, map_sub, hpoint] at hm

/-- A w-contractible ring is henselian along its Jacobson radical. The second clause
spells out the equivalent finite-algebra idempotent condition: reduction has exactly
one idempotent preimage for each idempotent of the quotient. No nonzero assumption
is imposed on the ring or its finite algebras.

Source: Ruimy--Tubach--Wolf, Proposition 1.1.2, henselian-pair consequence;
Stacks Project, Tags 0A02, 0AGU, 09XI, 0982 and 00HP
(blueprint: lem-sfb-wcontractible-jacobson-henselian).

Proof:
1. Put J = jacobson of the zero ideal. Pair henselization gives eta : R → H,
   a henselian pair (H,JH), and a bijective canonical map R/J → H/JH. Its
   essentially small filtered etale presentation makes eta ind-etale in R's universe.
2. The henselization map is flat. For each maximal ideal m, J ≤ m, so the inverse
   quotient equivalence gives a map H → R/J → R/m that kills mH. Since R/m is
   nonzero, mH is proper. The maximal-ideal criterion gives faithful flatness.
3. The source class IsWContractibleRing already supplies precisely the hypotheses
   of IsWContractibleRing.exists_retraction; obtain rho : H → R with rho eta = id.
4. Descend the simple-root lifting property along this retraction. Map a monic
   polynomial and its approximate root into H; the derivative remains invertible
   modulo JH. Lift the root in H and apply rho. Evaluation commutes with both
   maps, and rho(JH) = J, giving a root congruent to the original one modulo J.
   Together with J ≤ jacobson of zero this proves HenselianRing R J.
5. A finite R-algebra is integral. Apply the already proved
   Algebra.existsUnique_isIdempotentElem_of_henselianRing to get the second clause.
No nonzero assumption is needed: the maximal-ideal test is vacuous for the zero ring. -/
theorem wcontractible_jacobson_henselian (R : Type u) [CommRing R]
    [IsWContractibleRing R] :
    HenselianRing R (Ideal.jacobson (⊥ : Ideal R)) ∧
      ∀ (B : Type (max u v)) [CommRing B] [Algebra R B] [Module.Finite R B]
        (e₀ : B ⧸ (Ideal.jacobson (⊥ : Ideal R)).map (algebraMap R B)),
        IsIdempotentElem e₀ → ∃! e : B, IsIdempotentElem e ∧
          Ideal.Quotient.mk ((Ideal.jacobson (⊥ : Ideal R)).map (algebraMap R B)) e = e₀ := by
  classical
  let J : Ideal R := Ideal.jacobson ⊥
  let P : CategoryTheory.ObjectProperty (CategoryTheory.Under (CommRingCat.of R)) := fun B ↦
    AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map B.hom) ∧
      Function.Bijective (Ideal.quotientMap (J.map B.hom.hom) B.hom.hom
        Ideal.le_comap_map)
  obtain ⟨hsmall, hfiltered, c, ⟨hc⟩, hhen, hq⟩ := pair_henselization R J
  let : CategoryTheory.EssentiallySmall.{u} P.FullSubcategory := hsmall
  let : CategoryTheory.IsFiltered P.FullSubcategory := hfiltered
  let S := c.pt.right
  let η : R →+* S := c.pt.hom.hom
  let : Algebra R S := η.toAlgebra
  have hind : η.IndEtale := by
    rw [RingHom.IndEtale.iff_ind_etale,
      CategoryTheory.MorphismProperty.ind_iff_ind_underMk]
    change CategoryTheory.ObjectProperty.ind.{u} CommRingCat.etale.underObj c.pt
    apply CategoryTheory.ObjectProperty.of_essentiallySmall_index
      (pres := { diag := P.ι, ι := c.ι, isColimit := hc })
    intro j
    change RingHom.Etale j.obj.hom.hom
    exact (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Etale)).mp j.property.1
  have : Algebra.IndEtale R S := hind
  have hflat : η.Flat := (pair_henselization_flat_quotients R J c hc).1
  have : Module.Flat R S := hflat
  let e : (R ⧸ J) ≃+* (S ⧸ J.map η) := RingEquiv.ofBijective _ hq
  let π : S →+* (R ⧸ J) := e.symm.toRingHom.comp (Ideal.Quotient.mk (J.map η))
  have hπη (r : R) : π (η r) = Ideal.Quotient.mk J r := by
    exact e.symm_apply_apply (Ideal.Quotient.mk J r)
  have : Module.FaithfullyFlat R S := by
    refine (Module.faithfullyFlat_iff R S).mpr ⟨inferInstance, ?_⟩
    intro m hm htop
    have hJm : J ≤ m := sInf_le ⟨bot_le, hm⟩
    let ψ : S →+* (R ⧸ m) := (Ideal.Quotient.factor hJm).comp π
    have hψη (r : R) : ψ (η r) = Ideal.Quotient.mk m r := by
      rw [RingHom.comp_apply, hπη]
      rfl
    have hker : m.map η ≤ RingHom.ker ψ := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      change ψ (η r) = 0
      rw [hψη, Ideal.Quotient.eq_zero_iff_mem]
      exact hr
    have htop' : m.map η = ⊤ := by
      apply Submodule.restrictScalars_injective R S S
      rw [Ideal.smul_top_eq_map] at htop
      change (m.map η).restrictScalars R = ⊤ at htop
      simpa only [Submodule.restrictScalars_top] using htop
    have hone : (1 : S) ∈ m.map η := htop' ▸ Submodule.mem_top
    have hz : (1 : R ⧸ m) = 0 := by
      simpa only [RingHom.mem_ker, map_one] using hker hone
    have : Nontrivial (R ⧸ m) := Ideal.Quotient.nontrivial_iff.mpr hm.ne_top
    exact one_ne_zero hz
  obtain ⟨ρ, hρ⟩ := IsWContractibleRing.exists_retraction R S
  have : HenselianRing S (J.map η) := hhen
  have hR : HenselianRing R J := henselian_of_retraction J le_rfl η ρ hρ
  refine ⟨hR, ?_⟩
  have : HenselianRing R J := hR
  intro B _ _ _ e₀ he₀
  exact Algebra.existsUnique_isIdempotentElem_of_henselianRing R J B e₀ he₀

end RingTheory
