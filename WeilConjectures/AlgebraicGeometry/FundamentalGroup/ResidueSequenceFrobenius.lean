/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ResidueSequence
public import WeilConjectures.Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# Frobenius equivariance of the residue sequence

Let `U ⊆ C` be a nonempty open of an integral scheme over a field `k`, and let `E` be an
automorphism of `C` restricting to an automorphism of `U` and semilinear over an automorphism
`σ₀` of `k`. Transport along `E` acts on torsors over `U` (in the torsor model of `H¹`), and the
residues of the transported torsor are those of the torsor, moved along `E` and twisted by `σ₀`
on the roots of unity (`AlgebraicGeometry.Scheme.EtaleTorsor.residue_mapIso`). This is the
Frobenius equivariance of the residue map of blueprint `lem-wf-open-curve-residue-sequence`.

For a power `Φ ^ m` of the geometric Frobenius fixing a boundary point `z`, `σ₀ = φ ^ m` with
`σ₀(x) ^ Q = x`, `Q = q ^ m`, so the pullback along `Φ ^ m` (transport along its inverse) acts on
the residues at `z` as multiplication by `Q`
(`AlgebraicGeometry.Scheme.EtaleTorsor.residue_mapIso_symm_eq_smul`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme

/-- The order of vanishing is invariant under automorphisms: for an automorphism `E` of a locally
noetherian integral scheme, inducing `e` on the function field, `ord_z(e f) = ord_{E z}(f)`. -/
lemma ord_functionFieldAut {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (E : X ≅ X)
    (f : X.functionField) (z : X) :
    X.ord ((functionFieldAut E).hom f) z = X.ord f (E.hom z) :=
  Scheme.ord_functionFieldIso E.hom z f

/-- The automorphism of the function field induced by an automorphism `E` of a `k`-scheme,
semilinear over `σ₀`, acts on the constants through `σ₀`. -/
lemma functionFieldAut_functionFieldConstants {X : Scheme.{u}} [IsIntegral X] {k : Type u}
    [Field k] (p : X ⟶ Spec (.of k)) (E : X ≅ X) (σ₀ : k ≃+* k)
    (hσ₀ : E.hom ≫ p = p ≫ Spec.map (CommRingCat.ofHom (σ₀ : k →+* k))) (b : k) :
    (functionFieldAut E).hom (p.functionFieldConstants b) = p.functionFieldConstants (σ₀ b) := by
  change (functionFieldAut E).hom (X.presheaf.germ ⊤ (genericPoint X) trivial
    (p.appTop ((Scheme.ΓSpecIso (.of k)).inv b))) = _
  rw [functionFieldAut_germ]
  change _ = X.presheaf.germ ⊤ (genericPoint X) trivial
    (p.appTop ((Scheme.ΓSpecIso (.of k)).inv (σ₀ b)))
  congr 1
  have h1 := congrArg (fun h ↦ (Scheme.Hom.appTop h).hom ((Scheme.ΓSpecIso (.of k)).inv b)) hσ₀
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h1
  rw [h1]
  congr 1
  exact (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (σ₀ : k →+* k))) b).symm

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.EtaleTorsor

section Transport

variable {C U : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] (j : U ⟶ C)
  [IsOpenImmersion j] [Nonempty U] {k : Type u} [Field k] (p : C ⟶ Spec (.of k)) {N : ℕ}
  [NeZero N] [NeZero (N : k)] [HasEnoughRootsOfUnity k N]

open FiniteEtale

local notation "Ω" => SeparableClosure (Scheme.functionField C)

/-- Blueprint `lem-wf-open-curve-residue-sequence`: Frobenius equivariance of the residue map.

Let `E_C` be an automorphism of `C`, semilinear over an automorphism `σ₀` of `k`, restricting to
an automorphism `E_U` of `U`. The residue at `E_C z` against `ξ` of the transport of a torsor `T`
along `E_U` is the residue of `T` at `z` against `σ₀ ξ`. -/
theorem residue_mapIso (EC : C ≅ C) (EU : U ≅ U) (hE : EU.hom ≫ j = j ≫ EC.hom)
    (σ₀ : k ≃+* k) (hσ₀ : EC.hom ≫ p = p ≫ Spec.map (CommRingCat.ofHom (σ₀ : k →+* k)))
    (T : EtaleTorsor (ULift.{u + 1} (ZMod N)) U) (z : C) (ξ ξ' : rootsOfUnity N k)
    (hξ : ((ξ' : kˣ) : k) = σ₀ ((ξ : kˣ) : k)) :
    (T.mapIso EU).residue j p (EC.hom z) (Additive.ofMul ξ) =
      T.residue j p z (Additive.ofMul ξ') := by
  obtain ⟨φ, hφF, hφη⟩ := exists_ringEquiv_separableClosure EC Ω
  set F := C.functionField
  let ι : F →+* Ω := algebraMap F Ω
  let e := functionFieldAut EC
  let η := genericGeometricPoint (C := C) j
  have hηj : η ≫ j = Spec.map (CommRingCat.ofHom ι) ≫ C.fromSpecFunctionField := by
    simp only [η, genericGeometricPoint, pointOfAlgebra, Category.assoc, genericPointLift_comp]
    rfl
  have hyU : Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω)) ≫ η = η ≫ EU.hom := by
    rw [← cancel_mono j, Category.assoc, hηj, hφη, Category.assoc, hE, ← Category.assoc η, hηj,
      Category.assoc]
  have hFinv (f : F) : φ.symm (ι f) = ι (e.inv f) := by
    rw [RingEquiv.symm_apply_eq, hφF, ← ConcreteCategory.comp_apply, e.inv_hom_id,
      CommRingCat.id_apply]
  have hspec (a b : Ω ≃+* Ω) : Spec.map (CommRingCat.ofHom ((a.trans b : Ω ≃+* Ω) : Ω →+* Ω)) =
      Spec.map (CommRingCat.ofHom (b : Ω →+* Ω)) ≫ Spec.map (CommRingCat.ofHom (a : Ω →+* Ω)) := by
    rw [← Spec.map_comp]
    rfl
  have hφφ : Spec.map (CommRingCat.ofHom (φ.symm : Ω →+* Ω)) ≫
      Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω)) = 𝟙 _ := by
    rw [← hspec, RingEquiv.self_trans_symm]
    exact Spec.map_id _
  -- a point of the transported torsor over the generic geometric point
  let t := T.genericFiberPoint j
  have ht : t ≫ T.π = η := T.genericFiberPoint_comp j
  let t' : Spec (.of Ω) ⟶ (T.mapIso EU).P := Spec.map (CommRingCat.ofHom (φ.symm : Ω →+* Ω)) ≫ t
  have ht' : t' ≫ (T.mapIso EU).π = η := by
    simp only [t', mapIso_π, Category.assoc]
    rw [reassoc_of% ht, ← hyU, ← Category.assoc, hφφ, Category.id_comp]
  -- the Galois character of the transported torsor is that of `T` conjugated by `φ`
  let conj (σ : Gal(Ω/F)) : Gal(Ω/F) :=
    AlgEquiv.ofRingEquiv (f := φ.symm.trans (σ.toRingEquiv.trans φ)) fun f ↦ by
      change φ (σ (φ.symm (ι f))) = ι f
      rw [hFinv, σ.commutes, ← hFinv, RingEquiv.apply_symm_apply]
  have hconj (σ : Gal(Ω/F)) (w : Ω) : φ.symm (conj σ w) = σ (φ.symm w) := by
    change φ.symm (φ (σ (φ.symm w))) = _
    rw [RingEquiv.symm_apply_apply]
  have hχ (σ : Gal(Ω/F)) :
      (T.mapIso EU).galoisCharacter j σ = T.galoisCharacter j (conj σ) := by
    refine galoisCharacter_eq_of_specMap_comp_eq j _ σ t' ht' ?_
    have h1 : (φ.symm.trans σ.toRingEquiv : Ω ≃+* Ω) =
        ((conj σ).toRingEquiv.trans φ.symm : Ω ≃+* Ω) := by
      refine RingEquiv.ext fun w ↦ ?_
      exact (hconj σ w).symm
    have h2 : Spec.map (CommRingCat.ofHom ((conj σ).toRingEquiv : Ω →+* Ω)) ≫ t =
        t ≫ T.vadd ⟨T.galoisCharacter j (conj σ)⟩ :=
      T.specMap_comp_eq_comp_vadd_galoisCharacter j (conj σ) t ht
    change Spec.map (CommRingCat.ofHom (σ.toRingEquiv : Ω →+* Ω)) ≫
      Spec.map (CommRingCat.ofHom (φ.symm : Ω →+* Ω)) ≫ t = _
    rw [← Category.assoc, ← hspec, h1, hspec, Category.assoc, h2]
    simp only [t', Category.assoc, mapIso_vadd]
  -- a Kummer element of `T` against `σ₀ ξ` gives one of the transported torsor against `ξ`
  have hξ'N : ((ξ' : kˣ) : k) ^ N = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity N _).1 ξ'.2, Units.val_one]
  obtain ⟨x, f, hx, hf, hxσ⟩ := T.exists_kummerElement j p hξ'N
  have hκ : φ.symm (ι (p.functionFieldConstants ((ξ' : kˣ) : k))) =
      ι (p.functionFieldConstants ((ξ : kˣ) : k)) := by
    rw [hFinv, hξ, ← functionFieldAut_functionFieldConstants p EC σ₀ hσ₀]
    change ι ((e.hom ≫ e.inv) _) = _
    rw [e.hom_inv_id]
    rfl
  rw [T.residue_eq_ord j p z (Additive.ofMul ξ') hx hf hxσ]
  rw [(T.mapIso EU).residue_eq_ord j p (EC.hom z) (Additive.ofMul ξ) (x := φ.symm x)
    (f := e.inv f) ((map_ne_zero_iff _ φ.symm.injective).2 hx)
    (by rw [← hFinv, hf, map_pow]) fun σ ↦ ?_]
  · rw [← ord_functionFieldAut EC (e.inv f) z]
    change ((C.ord ((e.inv ≫ e.hom) f) z : ℤ) : ZMod N) = _
    rw [e.inv_hom_id]
    rfl
  · rw [← hconj, hxσ, map_mul, map_pow, hκ, hχ]
    rfl

/-- Blueprint `lem-wf-open-curve-residue-sequence`: a Frobenius power fixing a boundary point
acts on the residues there as multiplication by `Q`.

Let `E_C` be an automorphism of `C` fixing `z`, semilinear over `σ₀` with `σ₀(x) ^ Q = x` (for a
power `Φ ^ m` of the geometric Frobenius over `𝔽_q`, `Q = q ^ m`), and restricting to `E_U` on `U`.
Then the residue at `z` of the pullback of a torsor `T` along `E_U`, i.e. its transport along
`E_U⁻¹`, is `Q` times the residue of `T`: `Φ_Q` acts on `ℤ / N (-1)` as multiplication by `Q`. -/
theorem residue_mapIso_symm_eq_smul (EC : C ≅ C) (EU : U ≅ U) (hE : EU.hom ≫ j = j ≫ EC.hom)
    (σ₀ : k ≃+* k) (hσ₀ : EC.hom ≫ p = p ≫ Spec.map (CommRingCat.ofHom (σ₀ : k →+* k)))
    (Q : ℕ) (hQ : ∀ x : k, σ₀ x ^ Q = x) (z : C) (hz : EC.hom z = z)
    (T : EtaleTorsor (ULift.{u + 1} (ZMod N)) U) :
    (T.mapIso EU.symm).residue j p z = Q • T.residue j p z := by
  have hT : ((T.mapIso EU.symm).mapIso EU).IsIsomorphic T :=
    ⟨Iso.refl _, by simp, fun _ ↦ by simp⟩
  refine AddMonoidHom.ext fun ξ ↦ ?_
  -- `ξ = σ₀ (ξ ^ Q)`
  have hξ : ((ξ.toMul : kˣ) : k) = σ₀ (((ξ.toMul ^ Q : rootsOfUnity N k) : kˣ) : k) := by
    simp only [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, map_pow, hQ]
  have h := residue_mapIso j p EC EU hE σ₀ hσ₀ (T.mapIso EU.symm) z (ξ.toMul ^ Q) ξ.toMul hξ
  rw [hz, residue_eq_of_isIsomorphic j p hT, ofMul_pow, map_nsmul, ofMul_toMul] at h
  rw [AddMonoidHom.smul_apply, ← h]

end Transport

end AlgebraicGeometry.Scheme.EtaleTorsor
