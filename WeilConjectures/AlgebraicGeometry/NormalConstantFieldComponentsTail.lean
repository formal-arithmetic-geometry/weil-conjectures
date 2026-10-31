/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalConstantFieldBasic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Connected.Basic

public import WeilConjectures.AlgebraicGeometry.FrobeniusDetailed

/-! # Frobenius orbit of a supplied constant-field component

Source: Stacks Project, fields.tex, Tags 09HY, 09I1 and 0CKN, with the geometric
Frobenius convention of Deligne, Weil II (1.1.7).
(blueprint: lem-dl-a1-normal-constant-field-components-tail).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

private theorem finite_embeddings_cyclic
    (K E Ω : Type u) [Field K] [Fintype K] [Field E] [Finite E]
    [Algebra K E] [Field Ω] [Algebra K Ω] (σ : E →ₐ[K] Ω) :
    Function.Bijective (fun i : Fin (Module.finrank K E) ↦
      σ.comp (FiniteField.frobeniusAlgEquivOfAlgebraic K E ^ (i : ℕ)).toAlgHom) := by
  let : Algebra E Ω := σ.toRingHom.toAlgebra
  have : IsScalarTower K E Ω := IsScalarTower.of_algebraMap_eq' σ.comp_algebraMap.symm
  have : Fintype E := Fintype.ofFinite E
  exact (Normal.algHomEquivAut K Ω E).symm.bijective.comp
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K E)

private theorem frobenius_pow_projections
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (m : ℕ) :
    let _ := Fintype.ofFinite D.k₀
    let γ := (FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ D.k).symm
    (D.geometricFrobenius X₀ ^ m).hom ≫ pullback.fst X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ∧
    (D.geometricFrobenius X₀ ^ m).hom ≫ pullback.snd X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.snd X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫
        Spec.map (CommRingCat.ofHom (γ ^ m).toRingHom) := by
  let _ := Fintype.ofFinite D.k₀
  let γ := (FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ D.k).symm
  have h := D.galoisMap_projections X₀.hom γ
  induction m with
  | zero =>
      constructor
      · exact Category.id_comp _
      · change (𝟙 _) ≫ _ = _ ≫ Spec.map (𝟙 _)
        rw [Spec.map_id, Category.comp_id, Category.id_comp]
  | succ m ih =>
      constructor
      · rw [pow_succ, Aut.Aut_mul_def, Iso.trans_hom, Category.assoc, ih.1]
        exact h.1
      · rw [pow_succ, Aut.Aut_mul_def, Iso.trans_hom, Category.assoc, ih.2]
        change D.galoisMap X₀.hom γ ≫ pullback.snd X₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫
            Spec.map (CommRingCat.ofHom (γ ^ m).toRingHom) = _
        erw [reassoc_of% h.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        change pullback.snd X₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫
            Spec.map (CommRingCat.ofHom (γ * γ ^ m).toRingHom) = _
        rw [← pow_succ']

/-- The translates of the supplied pullback component form one Frobenius cycle.

Source: Stacks Project, fields.tex, Tags 09HY, 09I1 and 0CKN; Deligne, Weil II (1.1.7).
(blueprint: lem-dl-a1-normal-constant-field-components-tail).

Proof: let F be q-power Frobenius on L and γ inverse q-power Frobenius on k. Through
the algebra structure induced by σ, the maps σᵢ = σ Fⁱ for 0 ≤ i < d are exactly the
k₀-embeddings of L into k, each once, and γⁿ ∘ σ Fⁿ = σ for every n. Iterating the
projection equations of geometric Frobenius Φ and transporting the supplied pullback
along Spec(γⁿ) shows that j Φⁿ has projections p and s Spec(γⁿ) onto a pullback of g and
Spec(σ Fⁿ). C is connected by geometric connectedness of g, and each j Φⁱ is an open and
closed immersion, so its range is the connected component of each of its points.
For a point x, the residue-field point Spec κ(x) → X gives compatible embeddings of L
and k into κ(x). The embedding of L factors through k, since k is algebraically closed,
and is then some σᵢ. The universal property of the i-th transported pullback lifts the
point through j Φⁱ, so the translates cover. If two translates meet, their nonempty
intersection pullback maps flatly and surjectively, hence epimorphically, to Spec k.
Cancelling it gives Spec σᵢ = Spec σᵢ', and so i = i'. Since F^d = 1, the d-th
transported pullback has bottom arrow Spec σ. Comparing it with the original pullback
gives r : C ≅ C with r p = p and r s = s Spec(γ^d), and the projections of the geometric
fibre give r j = j Φ^d. Surjectivity of r reduces exponents modulo d, which gives the
successor identity. No positive-dimensional hypothesis is used, and d = 1 gives the
single-component case. -/
theorem normal_constant_field_components_tail
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (U₀ : Over (Spec (CommRingCat.of D.k₀)))
    [ConnectedSpace U₀.left] [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [IsSeparated U₀.hom]
    [IsIntegral U₀.left] [Algebra D.k₀ U₀.left.functionField]
    (b : NormalConstantFieldBasicData D U₀)
    (σ : b.L →ₐ[D.k₀] D.k) (C : Scheme.{u})
    (p : C ⟶ U₀.left) (s : C ⟶ Spec (CommRingCat.of D.k))
    (j : C ⟶ (D.geometricFiber U₀).left)
    (hpb : IsPullback p s b.g (Spec.map (CommRingCat.ofHom σ.toRingHom)))
    (hp : j ≫ pullback.fst U₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = p)
    (hs : j ≫ pullback.snd U₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = s)
    (ho : IsOpenImmersion j) (hc : IsClosedImmersion j) :
        (∀ i : Fin b.d,
          IsOpenImmersion (j ≫ (D.geometricFrobenius U₀ ^ (i : ℕ)).hom) ∧
          IsClosedImmersion (j ≫ (D.geometricFrobenius U₀ ^ (i : ℕ)).hom)) ∧
        (∀ x : (D.geometricFiber U₀).left, ∃ i : Fin b.d,
          connectedComponent x =
            Set.range (j ≫ (D.geometricFrobenius U₀ ^ (i : ℕ)).hom)) ∧
        (Pairwise fun i i' : Fin b.d ↦
          Disjoint (Set.range (j ≫ (D.geometricFrobenius U₀ ^ (i : ℕ)).hom))
            (Set.range (j ≫ (D.geometricFrobenius U₀ ^ (i' : ℕ)).hom))) ∧
        (⋃ i : Fin b.d, Set.range (j ≫ (D.geometricFrobenius U₀ ^ (i : ℕ)).hom)) =
          Set.univ ∧
        (∀ i : Fin b.d,
          (D.geometricFrobenius U₀).hom ''
              Set.range (j ≫ (D.geometricFrobenius U₀ ^ (i : ℕ)).hom) =
            Set.range (j ≫
              (D.geometricFrobenius U₀ ^ (((i : ℕ) + 1) % b.d)).hom)) ∧
        ∃ r : C ≅ C,
          r.hom ≫ j = j ≫ (D.geometricFrobenius U₀ ^ b.d).hom ∧
          r.hom ≫ p = p ∧
          r.hom ≫ s = s ≫ Spec.map (CommRingCat.ofHom
            ((@FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ _
              (Fintype.ofFinite D.k₀) D.k _ _ _).symm ^ b.d).toRingHom) := by
  classical
  let := Fintype.ofFinite D.k₀
  let : Module.Finite D.k₀ b.L := b.finite
  let : Finite b.L := Module.finite_of_finite D.k₀
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let F := FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ b.L
  let γ := (FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ D.k).symm
  let Φ := D.geometricFrobenius U₀
  let X := (D.geometricFiber U₀).left
  let P : X ⟶ U₀.left := pullback.fst U₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  let Q : X ⟶ Spec (CommRingCat.of D.k) := pullback.snd U₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  have hX : IsPullback P Q U₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) := .of_hasPullback _ _
  have hp' : j ≫ P = p := hp
  have hs' : j ≫ Q = s := hs
  let a (n : ℕ) := Spec.map (CommRingCat.ofHom (γ ^ n).toRingHom)
  let σn (n : ℕ) : b.L →ₐ[D.k₀] D.k := σ.comp (F ^ n).toAlgHom
  have hσn (n : ℕ) : a n ≫ Spec.map (CommRingCat.ofHom (σn n).toRingHom) =
      Spec.map (CommRingCat.ofHom σ.toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext z
    change (γ ^ n) (σ ((F ^ n) z)) = σ z
    have hn : σ ((F ^ n) z) =
        (FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ D.k ^ n) (σ z) := by
      simp only [F, AlgEquiv.coe_pow,
        FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
      exact map_pow σ z _
    rw [hn]
    change ((FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ D.k)⁻¹ ^ n)
      ((FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ D.k ^ n) (σ z)) = σ z
    rw [inv_pow]
    exact (FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ D.k ^ n).symm_apply_apply _
  have hproj (n : ℕ) : (Φ ^ n).hom ≫ P = P ∧
      (Φ ^ n).hom ≫ Q = Q ≫ a n := frobenius_pow_projections D U₀ n
  have hjP (n : ℕ) : (j ≫ (Φ ^ n).hom) ≫ P = p := by
    rw [Category.assoc, (hproj n).1]
    exact hp
  have hjQ (n : ℕ) : (j ≫ (Φ ^ n).hom) ≫ Q = s ≫ a n := by
    rw [Category.assoc, (hproj n).2, ← Category.assoc]
    exact congrArg (fun t ↦ t ≫ a n) hs
  have hpbN (n : ℕ) : IsPullback p (s ≫ a n) b.g
      (Spec.map (CommRingCat.ofHom (σn n).toRingHom)) := by
    let e : Spec (CommRingCat.of D.k) ≅ Spec (CommRingCat.of D.k) :=
      Scheme.Spec.mapIso (γ ^ n).toRingEquiv.toCommRingCatIso.op
    exact hpb.of_iso (.refl _) (.refl _) e (.refl _)
      (by simp) (by rfl) (by simp) (by simpa [e, a] using (hσn n).symm)
  let : ConnectedSpace C :=
    b.geometricallyConnected.geometrically_connectedSpace _ _ _ hpb
  let : IsOpenImmersion j := ho
  let : IsClosedImmersion j := hc
  have himm (n : ℕ) : IsOpenImmersion (j ≫ (Φ ^ n).hom) ∧
      IsClosedImmersion (j ≫ (Φ ^ n).hom) := ⟨inferInstance, inferInstance⟩
  have hcomponents (n : ℕ) (x : X) (hx : x ∈ Set.range (j ≫ (Φ ^ n).hom)) :
      connectedComponent x = Set.range (j ≫ (Φ ^ n).hom) := by
    let := (himm n).1
    let := (himm n).2
    apply Set.Subset.antisymm
    · exact (show IsClopen (Set.range (j ≫ (Φ ^ n).hom)) from
        ⟨(j ≫ (Φ ^ n).hom).isClosedEmbedding.isClosed_range,
          (j ≫ (Φ ^ n).hom).isOpenEmbedding.isOpen_range⟩).connectedComponent_subset hx
    · exact (isConnected_range (j ≫ (Φ ^ n).hom).continuous).subset_connectedComponent hx
  have hbij : Function.Bijective (fun i : Fin b.d ↦ σn (i : ℕ)) := by
    rw [b.d_eq]
    exact finite_embeddings_cyclic D.k₀ b.L D.k σ
  have hcover : ∀ x : X, ∃ i : Fin b.d, x ∈ Set.range (j ≫ (Φ ^ (i : ℕ)).hom) := by
    intro x
    let κ := X.residueField x
    let η : Spec (CommRingCat.of κ) ⟶ X := X.fromSpecResidueField x
    let χ : D.k →+* κ := (Spec.preimage (η ≫ Q)).hom
    let ψ : b.L →+* κ := (Spec.preimage (η ≫ P ≫ b.g)).hom
    have hχ : Spec.map (CommRingCat.ofHom χ) = η ≫ Q := Spec.map_preimage _
    have hψ : Spec.map (CommRingCat.ofHom ψ) = η ≫ P ≫ b.g := Spec.map_preimage _
    have heq : Spec.map (CommRingCat.ofHom ψ) ≫
          Spec.map (CommRingCat.ofHom (algebraMap D.k₀ b.L)) =
        Spec.map (CommRingCat.ofHom χ) ≫
          Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
      rw [hχ, hψ]
      simpa only [Category.assoc, b.factor] using
        congrArg (fun t ↦ η ≫ t) hX.w
    have hcomm : ψ.comp (algebraMap D.k₀ b.L) =
        χ.comp (algebraMap D.k₀ D.k) := by
      rw [← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp] at heq
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective heq)
    let : Algebra D.k κ := χ.toAlgebra
    let : Algebra D.k₀ κ := (χ.comp (algebraMap D.k₀ D.k)).toAlgebra
    let : IsScalarTower D.k₀ D.k κ := IsScalarTower.of_algebraMap_eq' rfl
    let ψa : b.L →ₐ[D.k₀] κ :=
      { toRingHom := ψ
        commutes' := fun z ↦ congrArg (fun f : D.k₀ →+* κ ↦ f z) hcomm }
    let hsplits : ∀ z : b.L,
        ((minpoly D.k₀ z).map (algebraMap D.k₀ D.k)).Splits :=
      fun _ ↦ IsAlgClosed.splits _
    let e := Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits κ D.k hsplits
    let τ := e.symm ψa
    have hτ (z : b.L) : χ (τ z) = ψ z := by
      change algebraMap D.k κ (τ z) = ψa z
      rw [← Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits_apply_apply κ D.k hsplits]
      exact congrArg (fun f : b.L →ₐ[D.k₀] κ ↦ f z) (e.apply_symm_apply ψa)
    obtain ⟨i, hi⟩ := hbij.2 τ
    have hi' : σn (i : ℕ) = τ := hi
    have hring : χ.comp (σn (i : ℕ)).toRingHom = ψ := by
      ext z
      change χ (σn (i : ℕ) z) = ψ z
      rw [hi']
      exact hτ z
    have heta : (η ≫ P) ≫ b.g =
        (η ≫ Q) ≫ Spec.map (CommRingCat.ofHom (σn (i : ℕ)).toRingHom) := by
      rw [Category.assoc, ← hψ, ← hχ, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hring]
    let t := (hpbN (i : ℕ)).lift (η ≫ P) (η ≫ Q) heta
    have ht : t ≫ j ≫ (Φ ^ (i : ℕ)).hom = η := by
      apply hX.hom_ext
      · simpa only [Category.assoc, (hproj (i : ℕ)).1, hp'] using
          (hpbN (i : ℕ)).lift_fst (η ≫ P) (η ≫ Q) heta
      · simpa only [Category.assoc, (hproj (i : ℕ)).2, reassoc_of% hs'] using
          (hpbN (i : ℕ)).lift_snd (η ≫ P) (η ≫ Q) heta
    refine ⟨i, t (IsLocalRing.closedPoint κ), ?_⟩
    change (t ≫ j ≫ (Φ ^ (i : ℕ)).hom) (IsLocalRing.closedPoint κ) = x
    rw [ht]
    exact Scheme.fromSpecResidueField_apply _ _
  have hdisj : Pairwise fun i i' : Fin b.d ↦
      Disjoint (Set.range (j ≫ (Φ ^ (i : ℕ)).hom))
        (Set.range (j ≫ (Φ ^ (i' : ℕ)).hom)) := by
    intro i i' hii'
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx⟩ ⟨y, hy⟩
    let ji := j ≫ (Φ ^ (i : ℕ)).hom
    let jj := j ≫ (Φ ^ (i' : ℕ)).hom
    obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := ji) (g := jj) x y (hx.trans hy.symm)
    let f := pullback.fst ji jj
    let f' := pullback.snd ji jj
    have heqP : f ≫ p = f' ≫ p := by
      simpa only [ji, jj, Category.assoc, (hproj (i : ℕ)).1,
        (hproj (i' : ℕ)).1, hp'] using
          congrArg (fun t ↦ t ≫ P) (pullback.condition (f := ji) (g := jj))
    have heqQ : f ≫ s ≫ a (i : ℕ) = f' ≫ s ≫ a (i' : ℕ) := by
      simpa only [ji, jj, Category.assoc, (hproj (i : ℕ)).2,
        (hproj (i' : ℕ)).2, reassoc_of% hs'] using
          congrArg (fun t ↦ t ≫ Q) (pullback.condition (f := ji) (g := jj))
    let q := f ≫ s ≫ a (i : ℕ)
    let : Surjective q := ⟨fun t ↦ ⟨w, Subsingleton.elim _ _⟩⟩
    let : Epi q := Flat.epi_of_flat_of_surjective q
    have hemb : Spec.map (CommRingCat.ofHom (σn (i : ℕ)).toRingHom) =
        Spec.map (CommRingCat.ofHom (σn (i' : ℕ)).toRingHom) := by
      apply (cancel_epi q).mp
      have hpi : p ≫ b.g = s ≫ a (i : ℕ) ≫
          Spec.map (CommRingCat.ofHom (σn (i : ℕ)).toRingHom) := by
        simpa only [Category.assoc] using (hpbN (i : ℕ)).w
      have hpj : p ≫ b.g = s ≫ a (i' : ℕ) ≫
          Spec.map (CommRingCat.ofHom (σn (i' : ℕ)).toRingHom) := by
        simpa only [Category.assoc] using (hpbN (i' : ℕ)).w
      calc
        q ≫ _ = f ≫ p ≫ b.g := by simp only [q, Category.assoc, ← hpi]
        _ = f' ≫ p ≫ b.g := by rw [← Category.assoc, heqP, Category.assoc]
        _ = f' ≫ s ≫ a (i' : ℕ) ≫ _ := by rw [hpj]
        _ = q ≫ _ := by
          simpa only [q, Category.assoc] using
            congrArg (fun t ↦ t ≫
              Spec.map (CommRingCat.ofHom (σn (i' : ℕ)).toRingHom)) heqQ.symm
    apply hii'
    apply hbij.1
    ext z
    exact congrArg
      (fun t : CommRingCat.of b.L ⟶ CommRingCat.of D.k ↦ t.hom z)
      (Spec.map_injective hemb)
  have hσd : σn b.d = σ := by
    have horder : F ^ b.d = 1 := by
      rw [b.d_eq, ← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic D.k₀ b.L]
      exact pow_orderOf_eq_one F
    ext z
    change σ ((F ^ b.d) z) = σ z
    rw [horder]
    rfl
  have hpbD : IsPullback p (s ≫ a b.d) b.g
      (Spec.map (CommRingCat.ofHom σ.toRingHom)) := by
    simpa only [hσd] using hpbN b.d
  let r : C ≅ C := hpbD.isoPullback ≪≫ hpb.isoPullback.symm
  have hrp : r.hom ≫ p = p := by simp [r]
  have hrs : r.hom ≫ s = s ≫ a b.d := by simp [r]
  have hrj : r.hom ≫ j = j ≫ (Φ ^ b.d).hom := by
    apply hX.hom_ext
    · simpa only [Category.assoc, hp'] using hrp.trans (hjP b.d).symm
    · simpa only [Category.assoc, hs'] using hrs.trans (hjQ b.d).symm
  have hperiod (n : ℕ) :
      Set.range (j ≫ (Φ ^ (b.d + n)).hom) = Set.range (j ≫ (Φ ^ n).hom) := by
    rw [Nat.add_comm b.d n, pow_add, Aut.Aut_mul_def, Iso.trans_hom,
      ← Category.assoc, ← hrj, Category.assoc]
    change Set.range ((j ≫ (Φ ^ n).hom) ∘ r.hom) = _
    rw [Set.range_comp, r.hom.surjective.range_eq, Set.image_univ]
  have hmod (n : ℕ) :
      Set.range (j ≫ (Φ ^ n).hom) = Set.range (j ≫ (Φ ^ (n % b.d)).hom) := by
    have hmul (k : ℕ) :
        Set.range (j ≫ (Φ ^ (b.d * k + n % b.d)).hom) =
          Set.range (j ≫ (Φ ^ (n % b.d)).hom) := by
      induction k with
      | zero => simp
      | succ k ih =>
          rw [Nat.mul_succ, Nat.add_comm (b.d * k) b.d, Nat.add_assoc, hperiod, ih]
    convert hmul (n / b.d) using 1
    rw [Nat.add_comm, Nat.mod_add_div]
  refine ⟨fun i ↦ himm i, ?_, hdisj, ?_, ?_, r, hrj, hrp, hrs⟩
  · intro x
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨i, hcomponents i x hi⟩
  · exact Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr (hcover x)
  · intro i
    rw [← hmod ((i : ℕ) + 1), pow_succ', Aut.Aut_mul_def, Iso.trans_hom,
      ← Category.assoc]
    change Φ.hom '' Set.range (j ≫ (Φ ^ (i : ℕ)).hom) =
      Set.range (fun x ↦ Φ.hom ((j ≫ (Φ ^ (i : ℕ)).hom) x))
    exact (Set.range_comp _ _).symm

end AlgebraicGeometry
