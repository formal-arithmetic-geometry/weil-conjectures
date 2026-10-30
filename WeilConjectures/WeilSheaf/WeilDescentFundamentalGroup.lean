/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ConstantExtension
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroupDense
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobenius
public import WeilConjectures.Mathlib.FieldTheory.Finite.Extension
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension
public import WeilConjectures.WeilSheaf.WeilDescentFundamentalGroupAux
public import WeilConjectures.WeilSheaf.WeilMonodromyGeneral

/-!
# The Weil group inside the arithmetic fundamental group

Let `X₀` be a scheme over a finite field `K`, `π : X ⟶ X₀` the projection of its geometric
fibre and `B = (t, β)` base point data (`AlgebraicGeometry.FrobeniusBasePoint`). The abstract
Weil group `W = π₁(X, t) ⋊ ℤ` of `B` (`AlgebraicGeometry.FrobeniusBasePoint.WeilGroup`) maps to
the arithmetic fundamental group `π₁(X₀, t ≫ π) = Aut F_{t ≫ π}`: a loop `g` at `t` goes to the
induced loop `π_* g`, and the generator of `ℤ` goes to the *arithmetic Frobenius element*
`π_* β` (`AlgebraicGeometry.FrobeniusBasePoint.arithFrob`), a loop at `t ≫ π` since
`Fr ≫ π = π`. This is `AlgebraicGeometry.FrobeniusBasePoint.toArith`.

For `X₀` geometrically connected and quasi-compact quasi-separated, the homotopy exact sequence
shows:

* `π₁(X, t) → π₁(X₀, t ≫ π)` is continuous and injective
  (`AlgebraicGeometry.FrobeniusBasePoint.continuous_toArith_inl`,
  `AlgebraicGeometry.FrobeniusBasePoint.injective_toArith_inl`);
* the image of `W` is dense (`AlgebraicGeometry.FrobeniusBasePoint.denseRange_toArith`);
* the degree is continuous for the profinite topology: for every `M > 0` there is a
  neighbourhood `U` of `1` such that `toArith w ∈ U` forces `M ∣ deg w`
  (`AlgebraicGeometry.FrobeniusBasePoint.exists_nhds_forall_dvd_deg`), the stabiliser of a point of
  the geometric fibre of the constant cover of degree `M`.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry.FrobeniusBasePoint

open Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
  (B : FrobeniusBasePoint K X)

/-- The *arithmetic Frobenius element* `π_* β ∈ π₁(X₀, t ≫ π)`: the path `β : F_t ≅ F_{t ≫ Fr}`
of the geometric fibre, pushed down along the projection `π : X ⟶ X₀`, which is a loop at
`t ≫ π` since `Fr ≫ π = π`. -/
noncomputable def arithFrob : Aut (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)) :=
  pullbackPathIso (X ↘ Spec (.of K)).geometricFiberProj B.frobPath ≪≫
    eqToIso (congrArg fiber (by
      rw [Category.assoc, Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj]))

/-- Conjugation by the arithmetic Frobenius element induces the Frobenius transport
`B.frobConj` on the image of `π₁(X, t)`. -/
theorem pullbackPathHom_frobConj (g : Aut (fiber B.t)) :
    pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t (B.frobConj g) =
      B.arithFrob⁻¹ * pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t g *
        B.arithFrob := by
  rw [pullbackPathHom_apply, pullbackPathHom_apply, frobConj_apply, arithFrob,
    pullbackPathIso_trans, pullbackPathIso_trans, pullbackPathIso_symm,
    pullbackPathIso_pullbackPathIso_of_comp_eq
      (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _)]
  simp only [Aut.Aut_mul_def, Aut.Aut_inv_def, Iso.trans_symm, eqToIso_symm', Iso.trans_assoc]

/-- Conjugation by the inverse of the arithmetic Frobenius element induces the inverse of the
Frobenius transport `B.frobConj` on the image of `π₁(X, t)`. -/
lemma pullbackPathHom_frobConj_symm (g : Aut (fiber B.t)) :
    pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t (B.frobConj.symm g) =
      B.arithFrob * pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t g *
        B.arithFrob⁻¹ := by
  have h := B.pullbackPathHom_frobConj (B.frobConj.symm g)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h]
  group

/-- The action of `n ∈ ℤ` on `π₁(X, t)` defining the Weil group `π₁(X, t) ⋊ ℤ` becomes
conjugation by the `n`-th power of the arithmetic Frobenius element in `π₁(X₀, t ≫ π)`. -/
lemma pullbackPathHom_frobAction (n : ℤ) (g : Aut (fiber B.t)) :
    pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t
        (B.frobAction (Multiplicative.ofAdd n) g) =
      B.arithFrob ^ n * pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t g *
        (B.arithFrob ^ n)⁻¹ := by
  simp only [frobAction, zpowersHom_apply, toAdd_ofAdd]
  induction n using Int.induction_on generalizing g with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, MulAut.mul_apply, ih, MulAut.inv_apply, pullbackPathHom_frobConj_symm]
    group
  | pred n ih =>
    rw [zpow_sub_one, MulAut.mul_apply, ih, inv_inv, pullbackPathHom_frobConj]
    group

/-- **The Weil group in the arithmetic fundamental group**: the homomorphism
`π₁(X, t) ⋊ ℤ → π₁(X₀, t ≫ π)`, `(g, n) ↦ π_* g · φⁿ` with `φ = π_* β` the arithmetic Frobenius
element. -/
noncomputable def toArith :
    B.WeilGroup →* Aut (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)) :=
  SemidirectProduct.lift (pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t)
    (zpowersHom _ B.arithFrob) fun n ↦ by
      ext1 x
      have h := B.pullbackPathHom_frobAction (Multiplicative.toAdd n) x
      rw [ofAdd_toAdd] at h
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        zpowersHom_apply]
      exact h

@[simp]
lemma toArith_inl (g : Aut (fiber B.t)) :
    B.toArith (SemidirectProduct.inl g) =
      pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t g :=
  SemidirectProduct.lift_inl _ _ _ g

@[simp]
lemma toArith_inr (n : Multiplicative ℤ) :
    B.toArith (SemidirectProduct.inr n) = B.arithFrob ^ n.toAdd :=
  SemidirectProduct.lift_inr _ _ _ n

/-- The arithmetic Frobenius element is the image of the lift of the Frobenius. -/
lemma toArith_frobLift : B.toArith B.weilData.frobLift = B.arithFrob := by
  rw [weilData, toArith_inr, toAdd_ofAdd, zpow_one]

/-- The map `π₁(X, t) → π₁(X₀, t ≫ π)` is continuous. -/
theorem continuous_toArith_inl :
    Continuous fun g : Aut (fiber B.t) ↦ B.toArith (SemidirectProduct.inl g) := by
  simp only [toArith_inl]
  exact continuous_pullbackPathHom _ _

section WeilGroup

open PreGaloisCategory

/-- `Aut F_t` acts naturally on the fibres. -/
lemma isNaturalSMul_aut_fiber : IsNaturalSMul (fiber B.t) (Aut (fiber B.t)) :=
  ⟨fun σ _ _ f x ↦ (mulAction_naturality (fiber B.t) σ f x).symm⟩

/-- The image of a loop of the geometric fibre acts trivially on the geometric fibres of the
constant covers. -/
theorem mem_weilGroup_pullbackPathHom [GeometricallyConnected (X ↘ Spec (.of K))]
    (ht : B.t ≫ (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure = 𝟙 _)
    (g : Aut (fiber B.t)) :
    (pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t g, (1 : Multiplicative ℤ)) ∈
      weilGroup (X ↘ Spec (.of K)) (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)
        (Aut (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj))) := by
  have := B.isNaturalSMul_aut_fiber
  refine (mem_weilGroup_iff _ _ _).2 fun A y ↦ ?_
  obtain ⟨z, rfl⟩ : ∃ z : (fiber B.t).obj ((pullback (X ↘ Spec (.of K)).geometricFiberProj).obj
      (constantCover (X ↘ Spec (.of K)) A)),
      (pullbackFiberIso (X ↘ Spec (.of K)).geometricFiberProj B.t).hom.app _ z = y :=
    ⟨(pullbackFiberIso _ B.t).inv.app _ y,
      ConcreteCategory.congr_hom ((pullbackFiberIso _ _).inv_hom_id_app _) y⟩
  rw [toAdd_one, zpow_zero, Equiv.Perm.one_apply, mulAction_def, pullbackPathHom_apply]
  have h := smul_eq_self_pullback_constantCover (X ↘ Spec (.of K)) ht (Aut (fiber B.t)) A z g
  rw [mulAction_def] at h
  simp only [pullbackPathIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  rw [FintypeCat.inv_app_hom_app_apply]
  exact congrArg _ h

/-- **The arithmetic Frobenius element has degree one**: it acts on the geometric fibres of the
constant covers as the geometric Frobenius. -/
theorem mem_weilGroup_arithFrob [GeometricallyConnected (X ↘ Spec (.of K))]
    (ht : B.t ≫ (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure = 𝟙 _) :
    (B.arithFrob, Multiplicative.ofAdd (1 : ℤ)) ∈
      weilGroup (X ↘ Spec (.of K)) (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)
        (Aut (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj))) := by
  refine (mem_weilGroup_iff _ _ _).2 fun A y ↦ ?_
  rw [toAdd_ofAdd, zpow_one]
  apply ((ConcreteCategory.isIso_iff_bijective _).1 (inferInstance : IsIso
    ((fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)).map
      (arithmeticFrobenius (X ↘ Spec (.of K)) A).hom))).1
  rw [fiber_map_arithmeticFrobenius_geometricFrobenius, mulAction_def]
  obtain ⟨z, rfl⟩ : ∃ z : (fiber B.t).obj ((pullback (X ↘ Spec (.of K)).geometricFiberProj).obj
      (constantCover (X ↘ Spec (.of K)) A)),
      (pullbackFiberIso (X ↘ Spec (.of K)).geometricFiberProj B.t).hom.app _ z = y :=
    ⟨(pullbackFiberIso _ B.t).inv.app _ y,
      ConcreteCategory.congr_hom ((pullbackFiberIso _ _).inv_hom_id_app _) y⟩
  apply fiber_ext
  simp only [arithFrob, Iso.trans_hom, NatTrans.comp_app, ConcreteCategory.comp_apply]
  rw [fiber_map_left, eqToIso_hom_app_left (by
    rw [Category.assoc, Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj])]
  simp only [pullbackPathIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    pullbackFiberIso_hom_app_left]
  rw [FintypeCat.inv_app_hom_app_apply]
  erw [path_section B.frobPath _ _ (sectionOfPoint_snd (X ↘ Spec (.of K)) A _ _) z
    (left_eq_sectionOfPoint (X ↘ Spec (.of K)) ht A z)]
  conv_rhs => rw [left_eq_sectionOfPoint (X ↘ Spec (.of K)) ht A z]
  apply Limits.pullback.hom_ext
  · simp [-constantCover_obj_hom, arithmeticFrobenius, constantCoverIso]
  · have key := comp_specMap_frobenius A (pointOfFiber (X ↘ Spec (.of K)) A z)
    simp only [pointOfFiber, Category.assoc] at key
    simp [-constantCover_obj_hom, arithmeticFrobenius, constantCoverIso, key]

/-- **The Weil group maps into the Weil group of `X₀`**: the image of `w` acts on the geometric
fibres of the constant covers as the `deg w`-th power of the geometric Frobenius. -/
theorem mem_weilGroup_toArith [GeometricallyConnected (X ↘ Spec (.of K))]
    (ht : B.t ≫ (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure = 𝟙 _) (w : B.WeilGroup) :
    (B.toArith w, B.weilData.deg w) ∈
      weilGroup (X ↘ Spec (.of K)) (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)
        (Aut (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj))) := by
  have h : (B.toArith w, B.weilData.deg w) =
      (pullbackPathHom (X ↘ Spec (.of K)).geometricFiberProj B.t w.left, 1) *
        (B.arithFrob, Multiplicative.ofAdd (1 : ℤ)) ^ Multiplicative.toAdd w.right := by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right w]
    refine Prod.ext ?_ ?_
    · rw [map_mul, toArith_inl, toArith_inr]
      simp
    · apply Multiplicative.toAdd.injective
      simp [weilData]
  rw [h]
  exact mul_mem (B.mem_weilGroup_pullbackPathHom ht _) (zpow_mem (B.mem_weilGroup_arithFrob ht) _)

open scoped FintypeCatDiscrete in
/-- **The degree is continuous for the profinite topology**: for every `M > 0` there is a
neighbourhood `U` of `1` in `π₁(X₀, t ≫ π)` such that the degree of every element of the Weil
group mapping into `U` is divisible by `M` (`U` is the stabiliser of a point of the geometric
fibre of the constant cover of degree `M`, on which an element of degree `n` acts as the `n`-th
power of the geometric Frobenius). -/
theorem exists_nhds_forall_dvd_deg [GeometricallyConnected (X ↘ Spec (.of K))]
    [CompactSpace X] [QuasiSeparatedSpace X] [ConnectedSpace X]
    (ht : B.t ≫ (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure = 𝟙 _) (M : ℕ) (hM : 0 < M) :
    ∃ U ∈ 𝓝 (1 : Aut (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj))),
      ∀ w, B.toArith w ∈ U → (M : ℤ) ∣ Multiplicative.toAdd (B.weilData.deg w) := by
  obtain ⟨F, hF⟩ := FiniteField.exists_intermediateField_finrank_eq K (AlgebraicClosure K) hM
  have hfd : FiniteDimensional K F := Module.finite_of_finrank_pos (hF ▸ hM)
  have : Algebra.Etale K F := (FiniteSubfield.toFiniteEtaleAlgebra (K := K) ⟨F, hfd⟩).2.2
  obtain ⟨z⟩ := nonempty_fiber_constantCover_of (X ↘ Spec (.of K))
    (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj) F
  refine ⟨{σ | σ • z = z}, ((isOpen_discrete {z}).preimage (f := fun σ ↦ σ • z)
    (by fun_prop)).mem_nhds (by simp), fun w hw ↦ ?_⟩
  have hw' : B.toArith w • z = z := hw
  have h := (mem_weilGroup_iff _ _ _).1 (B.mem_weilGroup_toArith ht w) _ z
  rw [hw'] at h
  rw [← hF]
  exact dvd_of_geometricFrobenius_zpow_apply _ _ F z _ h.symm

/-- The map `π₁(X, t) → π₁(X₀, t ≫ π)` is injective (homotopy exact sequence). -/
theorem injective_toArith_inl [CompactSpace X] [QuasiSeparatedSpace X] [ConnectedSpace X]
    [ConnectedSpace (X ↘ Spec (.of K)).geometricFiber] :
    Function.Injective fun g : Aut (fiber B.t) ↦ B.toArith (SemidirectProduct.inl g) := by
  obtain ⟨G', _, _⟩ := exists_isFundamentalGroup B.t
  obtain ⟨G, _, _⟩ := exists_isFundamentalGroup (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)
  intro g g' h
  obtain ⟨k, rfl⟩ := (toAut_bijective (fiber B.t) G').2 g
  obtain ⟨k', rfl⟩ := (toAut_bijective (fiber B.t) G').2 g'
  simp only [toArith_inl, ← toAut_fundamentalGroupMap_pullbackFiberIso _ _ G' G] at h
  rw [fundamentalGroupMap_injective_geometricFiber (X ↘ Spec (.of K)) _ G' G
    ((toAut_bijective _ G).1 h)]

/-- **The Weil group is dense in the arithmetic fundamental group.** -/
theorem denseRange_toArith [GeometricallyConnected (X ↘ Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))] [CompactSpace X]
    [QuasiSeparatedSpace X] [ConnectedSpace X]
    (ht : B.t ≫ (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure = 𝟙 _) :
    DenseRange B.toArith := by
  have : ConnectedSpace (X ↘ Spec (.of K)).geometricFiber :=
    GeometricallyConnected.geometrically_connectedSpace (f := X ↘ Spec (.of K))
      (Scheme.specAlgebraicClosure K).hom (X ↘ Spec (.of K)).geometricFiberProj
      (X ↘ Spec (.of K)).geometricFiberToAlgebraicClosure (IsPullback.of_hasPullback _ _)
  obtain ⟨G', _, _⟩ := exists_isFundamentalGroup B.t
  obtain ⟨G, _, _⟩ := exists_isFundamentalGroup (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)
  have hH : B.toArith.range.topologicalClosure.comap (toAut _ G) = ⊤ := by
    refine eq_top_of_forall_mem_weilGroup (X ↘ Spec (.of K))
      (t := B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj) G _
      (B.toArith.range.isClosed_topologicalClosure.preimage (toAut_isHomeomorph _ G).continuous)
      fun ⟨x, n⟩ hw ↦ B.toArith.range.le_topologicalClosure ?_
    obtain ⟨g, hg⟩ := (toAut_bijective _ G).2
      (toAut _ G x * B.arithFrob ^ (-Multiplicative.toAdd n))
    have h1 : (toAut _ G g, (1 : Multiplicative ℤ)) ∈ weilGroup (X ↘ Spec (.of K))
        (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj)
        (Aut (fiber (B.t ≫ (X ↘ Spec (.of K)).geometricFiberProj))) := by
      have := mul_mem ((toAut_mem_weilGroup_iff _ _ G x n).2 hw)
        (zpow_mem (B.mem_weilGroup_arithFrob ht) (-Multiplicative.toAdd n))
      convert this using 1
      refine Prod.ext ?_ ?_
      · simp [hg]
      · apply Multiplicative.toAdd.injective
        simp
    rw [toAut_mem_weilGroup_iff] at h1
    obtain ⟨k, hk⟩ := mem_range_fundamentalGroupMap_of_mem_weilGroup (X ↘ Spec (.of K))
      (pullbackFiberIso (X ↘ Spec (.of K)).geometricFiberProj B.t) G' G g h1
    refine ⟨SemidirectProduct.inl (toAut (fiber B.t) G' k) * SemidirectProduct.inr n, ?_⟩
    rw [map_mul, toArith_inl, toArith_inr, ← toAut_fundamentalGroupMap_pullbackFiberIso _ _ G' G,
      hk, hg, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  have hH' : B.toArith.range.topologicalClosure = ⊤ := eq_top_iff.2 fun a _ ↦ by
    obtain ⟨g, rfl⟩ := (toAut_bijective _ G).2 a
    have hg := Subgroup.mem_top g
    rw [← hH] at hg
    exact hg
  rw [DenseRange, dense_iff_closure_eq, ← MonoidHom.coe_range, ← Subgroup.topologicalClosure_coe,
    hH', Subgroup.coe_top]

end WeilGroup

end AlgebraicGeometry.FrobeniusBasePoint
