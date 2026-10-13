/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.FieldTheory.Separable

import Mathlib.RingTheory.Etale.StandardEtale

/-!
# Lifting a finite separable residue-field extension

Source: Stacks Project, Algebra, Tag 04GK, the field-lifting paragraph.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace CommAlgCat.FiniteEtale

/-- A finite separable extension of the residue field lifts to a finite étale algebra.
Source: Stacks Project, Algebra, Tag 04GK, using Tags 00UD and 04GJ.
(blueprint: lem-weil-pbc-henselian-finite-etale-field-lift).

Proof: Apply the prescribed-residue-field étale algebra theorem (00UD) at the maximal
ideal of R to obtain an étale R-algebra C and a prime q over that ideal whose residue
extension is L. Henselian finite-type decomposition (04GJ) writes C as a finite product
of local finite R-algebras Aᵢ and a factor B with no quasi-finite prime above the maximal
ideal. Each factor is an idempotent localization of C, hence étale. Étale algebras are
quasi-finite everywhere (00U5), so B has no prime above the maximal ideal and q belongs
to one Aᵢ. Finiteness over the local base shows that this prime is maximal. The étale
prime-generation theorem (00U4) gives mAᵢ = nᵢ, and hence κ ⊗[R] Aᵢ is its residue
field, compatibly with the prescribed isomorphism to L. Take S to be this finite étale
factor. This is an existence theorem only; it defines no algebra by choosing a witness.
The degree-one case is included, while the field hypothesis excludes the zero algebra. -/
theorem exists_finiteEtale_residueField_equiv_of_finite_separable
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (L : Type (max u v)) [Field L] [Algebra (IsLocalRing.ResidueField R) L]
    [Module.Finite (IsLocalRing.ResidueField R) L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) L] :
    ∃ S : CommAlgCat.FiniteEtale.{max u v} R,
      Nonempty ((IsLocalRing.ResidueField R ⊗[R] S) ≃ₐ[IsLocalRing.ResidueField R] L) := by
  -- Lift the minimal polynomial of a primitive element, then use its monic quotient.
  -- Henselianity is not needed for this field-lifting step beyond the local-ring instance.
  classical
  let k : Type u := IsLocalRing.ResidueField R
  have hetale (f : Polynomial R) (hf : f.Monic)
      (hs : (f.map (IsLocalRing.residue R)).Separable) : Algebra.Etale R (AdjoinRoot f) := by
    let := hf.finite_adjoinRoot
    have hd : IsUnit (AdjoinRoot.mk f f.derivative) := by
      by_contra hn
      obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal
        (Ideal.span {AdjoinRoot.mk f f.derivative})
        (fun h ↦ hn (Ideal.span_singleton_eq_top.mp h))
      let := hq
      have hc : q.comap (algebraMap R (AdjoinRoot f)) = IsLocalRing.maximalIdeal R :=
        IsLocalRing.eq_maximalIdeal
          (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q)
      let φ : IsLocalRing.ResidueField R →+* AdjoinRoot f ⧸ q :=
        Ideal.Quotient.lift _ ((Ideal.Quotient.mk q).comp (algebraMap R (AdjoinRoot f)))
          (fun r hr ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (by rwa [← hc] at hr))
      have he (g : Polynomial R) :
          (g.map (IsLocalRing.residue R)).eval₂ φ
            (Ideal.Quotient.mk q (AdjoinRoot.root f)) =
          Ideal.Quotient.mk q (AdjoinRoot.mk f g) := by
        rw [Polynomial.eval₂_map]
        change g.eval₂ ((Ideal.Quotient.mk q).comp (algebraMap R (AdjoinRoot f))) _ = _
        rw [← Polynomial.hom_eval₂, ← Polynomial.aeval_def, AdjoinRoot.aeval_eq]
      have hnz := hs.eval₂_derivative_ne_zero φ (x :=
        Ideal.Quotient.mk q (AdjoinRoot.root f)) (by rw [he, AdjoinRoot.mk_self, map_zero])
      rw [Polynomial.derivative_map, he] at hnz
      exact hnz (Ideal.Quotient.eq_zero_iff_mem.mpr
        (hle (Ideal.subset_span (by simp))))
    let P : StandardEtalePair R := ⟨f, hf, f.derivative, ⟨1, 0, 1, by simp⟩⟩
    have hm : P.HasMap (AdjoinRoot.root f) :=
      ⟨by simp [P, AdjoinRoot.aeval_eq], by simpa [P, AdjoinRoot.aeval_eq] using hd⟩
    let e : P.Ring ≃ₐ[R] AdjoinRoot f := .ofAlgHom
      (P.lift (AdjoinRoot.root f) hm)
      (AdjoinRoot.liftAlgHom f (Algebra.ofId R P.Ring) P.X P.hasMap_X.1)
      (AdjoinRoot.algHom_ext (by simp [AdjoinRoot.liftAlgHom_root]))
      (StandardEtalePair.hom_ext (by simp [AdjoinRoot.liftAlgHom_root]))
    exact Algebra.Etale.of_equiv e
  -- Base change commutes with adjoining a root; simplify the coefficient tensor product.
  have hbaseChange (f : Polynomial R) :
      Nonempty ((k ⊗[R] AdjoinRoot f) ≃ₐ[k] AdjoinRoot (f.map (algebraMap R k))) := by
    let e := Algebra.TensorProduct.rid R k k
    refine ⟨(AdjoinRoot.tensorAlgEquiv f _ rfl).trans
      (AdjoinRoot.mapAlgEquiv e _ _ ?_)⟩
    apply Associated.of_eq
    rw [Polynomial.map_map]
    congr 1
    ext r
    simp [e, Algebra.smul_def]
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k L
  have hi : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  obtain ⟨f, hmap, -, hf⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.mem_lifts _).mpr
      (Polynomial.map_surjective _ (IsLocalRing.residue_surjective (R := R)) (minpoly k α)))
    (minpoly.monic hi)
  have hs : (f.map (IsLocalRing.residue R)).Separable := by
    rw [hmap]
    exact Algebra.IsSeparable.isSeparable k α
  let := hf.finite_adjoinRoot
  let := hetale f hf hs
  let A := ULift.{v} (AdjoinRoot f)
  let : Module.Finite R A := Module.Finite.equiv (ULift.algEquiv.toLinearEquiv.symm)
  let : Algebra.Etale R A := Algebra.Etale.of_equiv (ULift.algEquiv.symm)
  refine ⟨CommAlgCat.FiniteEtale.of R A, ⟨?_⟩⟩
  let e₁ : (k ⊗[R] A) ≃ₐ[k] (k ⊗[R] AdjoinRoot f) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl (R := k) (A₁ := k)) (ULift.algEquiv (R := R))
  let e₂ := (hbaseChange f).some
  let e₃ : AdjoinRoot (f.map (algebraMap R k)) ≃ₐ[k] AdjoinRoot (minpoly k α) :=
    AdjoinRoot.algEquivOfEq _ _ _ hmap
  exact e₁.trans (e₂.trans (e₃.trans
    ((IntermediateField.adjoinRootEquivAdjoin k hi).trans
      ((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv))))

end CommAlgCat.FiniteEtale
