/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.AdditiveCharacters
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.CurvePairing
public import WeilConjectures.GroupTheory.TateModuleDual

/-!
# `lim_n H¹(C, ℤ/ℓⁿ)` is the dual of the Tate module of the Picard group

Let `X` be a smooth proper connected curve over an algebraically closed field `k`, with a
geometric point `s` and fundamental group `G = π₁(X, s)`, and let `ℓ` be a prime invertible in
`k`. At finite level the cup-trace pairing `H¹(X, ℤ/ℓⁿ) × H¹(X, μ_{ℓⁿ}) → ℤ/ℓⁿ` is perfect
(`AlgebraicGeometry.Scheme.EtaleTorsor.bijective_curvePairing`), and Kummer theory identifies
`H¹(X, μ_{ℓⁿ})` with `Pic(X)[ℓⁿ]` (`AlgebraicGeometry.Scheme.kummerTorsionEquiv`). This gives
group isomorphisms

`H¹(X, ℤ/ℓⁿ) ≃+ Hom(Pic(X)[ℓⁿ], ℤ/ℓⁿ)`

(`AlgebraicGeometry.Scheme.EtaleTorsor.sheafHPicTorsionDualAddEquiv`), under which the
reduction `ℤ/ℓⁿ⁺¹ → ℤ/ℓⁿ` corresponds to the dual of multiplication by `ℓ`
(`AlgebraicGeometry.Scheme.EtaleTorsor.sheafHPicTorsionDualAddEquiv_map_reduction`), and the
transport along an automorphism `f` of `X` (over an automorphism of `Spec k`, e.g. a Galois
element acting on a geometric fibre) corresponds to precomposition with `f^*`
(`AlgebraicGeometry.Scheme.EtaleTorsor.sheafHPicTorsionDualAddEquiv_mapIsoH1`).

The groups `Pic(X)[ℓⁿ] ≅ (ℤ/ℓⁿ)^{2g}` have `ℓ ^ (2 g n)` elements, so the `ℓ`-power torsion
of `Pic(X)` is `ℓ`-divisible, and passing to the limit gives blueprint (4.1),

`lim_n H¹(X, ℤ/ℓⁿ) ≃+ Hom_{ℤ_ℓ}(T_ℓ Pic(X), ℤ_ℓ)`

(`AlgebraicGeometry.Scheme.EtaleTorsor.sheafHOneLimitAddEquivDualTateModule`), with
`T_ℓ Pic(X) = T_ℓ J` the Tate module of the Jacobian.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.EtaleTorsor

open FiniteEtale

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [ConnectedSpace X] (s : Spec (.of k) ⟶ X)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]
  {l : ℕ} [Fact l.Prime] (hl : (l : k) ≠ 0)

omit [IsAlgClosed k] [Fact l.Prime] in
include hl in
lemma natCast_pow_ne_zero_of_natCast_ne_zero (n : ℕ) : ((l ^ n : ℕ) : k) ≠ 0 := by
  rw [Nat.cast_pow]
  exact pow_ne_zero _ hl

omit [Fact l.Prime] in
variable (X l) in
/-- `Pic(X)[ℓⁿ]`, written with `ℓ ^ n` cast from `ℕ` or computed in `ℤ`. -/
noncomputable def picTorsionByPowEquiv (n : ℕ) :
    AddSubgroup.torsionBy (Additive X.Pic) ((l ^ n : ℕ) : ℤ) ≃+
      AddSubgroup.torsionBy (Additive X.Pic) ((l : ℤ) ^ n) :=
  AddEquiv.addSubgroupCongr (by rw [Nat.cast_pow])

omit [Fact l.Prime] [ConnectedSpace X] in
@[simp]
lemma coe_picTorsionByPowEquiv_symm_apply (n : ℕ)
    (y : AddSubgroup.torsionBy (Additive X.Pic) ((l : ℤ) ^ n)) :
    ((picTorsionByPowEquiv X l n).symm y : Additive X.Pic) = y :=
  rfl

instance neZero_pow_of_prime (n : ℕ) : NeZero (l ^ n) :=
  ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

variable [GeometricallyIntegral (X ↘ Spec (.of k))] [Nonempty X]

/-- Blueprint `lem-wf-curve-h1-dual-tate-module`: Untwisted integral classes form the dual Tate
module, the finite-level isomorphism (4.3) with `J[ℓⁿ] = Pic(X)[ℓⁿ]`.

The group isomorphism `H¹(X, ℤ/ℓⁿ) ≃+ Hom(Pic(X)[ℓⁿ], ℤ/ℓⁿ)` adjoint to the perfect cup-trace
pairing `H¹(X, ℤ/ℓⁿ) × H¹(X, μ_{ℓⁿ}) → ℤ/ℓⁿ` (blueprint `lem-wf-curve-finite-level-pd`),
composed with the Kummer identification `H¹(X, μ_{ℓⁿ}) ≃+ Pic(X)[ℓⁿ]`. The class of a torsor
`t` is sent to its character `AlgebraicGeometry.Scheme.EtaleTorsor.picPairing`
(`AlgebraicGeometry.Scheme.EtaleTorsor.sheafHPicTorsionDualAddEquiv_classH1`). -/
noncomputable def sheafHPicTorsionDualAddEquiv (n : ℕ) :
    Sheaf.H (constantZModPow X l n) 1 ≃+
      (AddSubgroup.torsionBy (Additive X.Pic) ((l : ℤ) ^ n) →+ ZMod (l ^ n)) :=
  (sheafHAddEquivContinuousMonoidHom _ s G).trans
    ((AddEquiv.ofBijective _ (bijective_curvePairing s G l n
      (natCast_pow_ne_zero_of_natCast_ne_zero hl n)).1).trans
      (AddEquiv.addMonoidHomCongrLeft ((kummerTorsionEquiv (l ^ n)
        (natCast_pow_ne_zero_of_natCast_ne_zero hl n)).trans (picTorsionByPowEquiv X l n))))

/-- The class of a `ℤ/ℓⁿ`-torsor `t` is sent to its character
`AlgebraicGeometry.Scheme.EtaleTorsor.picPairing` of `Pic(X)[ℓⁿ]`. -/
lemma sheafHPicTorsionDualAddEquiv_classH1 (n : ℕ)
    (t : EtaleTorsor (ULift.{u + 1} (ZMod (l ^ n))) X)
    (y : AddSubgroup.torsionBy (Additive X.Pic) ((l : ℤ) ^ n)) :
    sheafHPicTorsionDualAddEquiv s G hl n (classH1 _ X ⟦t⟧) y =
      t.picPairing (natCast_pow_ne_zero_of_natCast_ne_zero hl n)
        ((picTorsionByPowEquiv X l n).symm y) := by
  rw [picPairing_apply, ← AddMonoidHom.comp_apply,
    ← charPairing_eq s G _ t (sheafHEquivContinuousMonoidHom_classH1 s G t).symm]
  rfl

/-- **Compatibility with reduction.** Under the finite-level isomorphisms, the reduction
`ℤ/ℓⁿ⁺¹ → ℤ/ℓⁿ` of coefficients corresponds to the dual of multiplication by `ℓ`,
`Pic(X)[ℓⁿ⁺¹] → Pic(X)[ℓⁿ]`, followed by the reduction. -/
lemma sheafHPicTorsionDualAddEquiv_map_reduction (n : ℕ)
    (x : Sheaf.H (constantZModPow X l (n + 1)) 1)
    (y : AddSubgroup.torsionBy (Additive X.Pic) ((l : ℤ) ^ (n + 1))) :
    sheafHPicTorsionDualAddEquiv s G hl n (Sheaf.H.map (constantZModPowReduction X l n) 1 x)
        ⟨(l : ℤ) • (y : Additive X.Pic), AddSubgroup.zsmul_mem_torsionBy_pow y.2⟩ =
      ZMod.castHom (pow_dvd_pow l (Nat.le_add_right n 1)) (ZMod (l ^ n))
        (sheafHPicTorsionDualAddEquiv s G hl (n + 1) x y) := by
  obtain ⟨T', rfl⟩ := (bijective_classH1 (M := ULift.{u + 1} (ZMod (l ^ (n + 1)))) (Y := X)).2 x
  induction T' using Quotient.inductionOn with | h t' => ?_
  obtain ⟨T, hT⟩ := (bijective_classH1 (M := ULift.{u + 1} (ZMod (l ^ n))) (Y := X)).2
    (Sheaf.H.map (constantZModPowReduction X l n) 1 (classH1 _ X ⟦t'⟧))
  induction T using Quotient.inductionOn with | h t => ?_
  have hmon := (map_constantZModPowReduction_eq_iff l s G n _ _).1 hT.symm
  simp only [sheafHEquivContinuousMonoidHom_classH1] at hmon
  rw [← hT, sheafHPicTorsionDualAddEquiv_classH1, sheafHPicTorsionDualAddEquiv_classH1]
  exact picPairing_zsmul_of_monodromy s G _ _ t t' hmon ((picTorsionByPowEquiv X l (n + 1)).symm y)
    ((picTorsionByPowEquiv X l n).symm ⟨_, AddSubgroup.zsmul_mem_torsionBy_pow y.2⟩).2

omit [GeometricallyIntegral (X ↘ Spec (.of k))] [Nonempty X] in
include hl in
/-- `Pic(X)[ℓⁿ]` has `ℓ ^ (2 g n)` elements, as `H¹(X, μ_{ℓⁿ}) ≅ (ℤ/ℓⁿ)^{2g}`. -/
lemma natCard_picTorsionBy [Nonempty X] (n : ℕ) :
    Nat.card (AddSubgroup.torsionBy (Additive X.Pic) ((l : ℤ) ^ n)) =
      l ^ (2 * (X ↘ Spec (.of k)).genus * n) := by
  obtain ⟨e⟩ := nonempty_addEquiv_sheafH_rootsOfUnitySheaf_one (k := k) (X := X) (l ^ n)
    (natCast_pow_ne_zero_of_natCast_ne_zero hl n)
  rw [← Nat.card_congr ((kummerTorsionEquiv (l ^ n)
    (natCast_pow_ne_zero_of_natCast_ne_zero hl n)).trans (picTorsionByPowEquiv X l n)).toEquiv,
    Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_fin, ← pow_mul, mul_comm n]

omit [GeometricallyIntegral (X ↘ Spec (.of k))] [Nonempty X] in
include hl in
/-- The `ℓ`-power torsion of `Pic(X)` is `ℓ`-divisible. -/
lemma exists_zsmul_eq_of_pow_zsmul_eq_zero [Nonempty X] (n : ℕ) (y : Additive X.Pic)
    (hy : (l : ℤ) ^ n • y = 0) : ∃ z, (l : ℤ) • z = y :=
  AddCommGroup.exists_zsmul_eq_of_natCard_torsionBy
    (Fact.out : l.Prime).ne_zero (natCard_picTorsionBy hl) n y hy

/-- Blueprint `lem-wf-curve-h1-dual-tate-module`: Untwisted integral classes form the dual Tate
module, the compatible system of finite-level isomorphisms.

The isomorphisms `H¹(X, ℤ/ℓⁿ) ≃+ Hom(Pic(X)[ℓⁿ], ℤ/ℓⁿ)` identify the inverse limit along the
reductions with the inverse limit along the duals of multiplication by `ℓ`. -/
noncomputable def sheafHOneLimitAddEquivTorsionDualLimit :
    sheafHOneLimit X l ≃+ AddCommGroup.torsionDualLimit l (Additive X.Pic) where
  toFun x := ⟨fun n ↦ sheafHPicTorsionDualAddEquiv s G hl n (x.1 n), fun n y ↦ by
    exact (congrArg (fun w ↦ sheafHPicTorsionDualAddEquiv s G hl n w
      ⟨_, AddSubgroup.zsmul_mem_torsionBy_pow y.2⟩) (x.2 n)).symm.trans
        (sheafHPicTorsionDualAddEquiv_map_reduction s G hl n _ y)⟩
  invFun ψ := ⟨fun n ↦ (sheafHPicTorsionDualAddEquiv s G hl n).symm (ψ.1 n), fun n ↦ by
    refine (sheafHPicTorsionDualAddEquiv s G hl n).injective (AddMonoidHom.ext fun y ↦ ?_)
    obtain ⟨z, hz⟩ := exists_zsmul_eq_of_pow_zsmul_eq_zero hl (n + 1) y.1 (by
      rw [pow_succ', mul_smul, (Submodule.mem_torsionBy_iff _ _).1 y.2, smul_zero])
    have hz' : z ∈ AddSubgroup.torsionBy (Additive X.Pic) ((l : ℤ) ^ (n + 1)) :=
      (Submodule.mem_torsionBy_iff _ _).2 (by
        rw [pow_succ, mul_smul, hz, (Submodule.mem_torsionBy_iff _ _).1 y.2])
    have hy : y = ⟨(l : ℤ) • z, AddSubgroup.zsmul_mem_torsionBy_pow hz'⟩ := Subtype.ext hz.symm
    rw [hy]
    refine (sheafHPicTorsionDualAddEquiv_map_reduction s G hl n _ ⟨z, hz'⟩).trans ?_
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact (ψ.2 n ⟨z, hz'⟩).symm⟩
  left_inv x := Subtype.ext (funext fun n ↦ AddEquiv.symm_apply_apply _ _)
  right_inv ψ := Subtype.ext (funext fun n ↦ AddEquiv.apply_symm_apply _ _)
  map_add' x y := Subtype.ext (funext fun n ↦ map_add _ _ _)

/-- Blueprint `lem-wf-curve-h1-dual-tate-module`: Untwisted integral classes form the dual Tate
module.

Let `X` be a smooth proper connected curve over an algebraically closed field `k` (e.g. the
geometric fibre of a curve over a finite field) and `ℓ` a prime invertible in `k`. There is a
natural group isomorphism (4.1)

`lim_n H¹(X, ℤ/ℓⁿ) ≃+ Hom_{ℤ_ℓ}(T_ℓ Pic(X), ℤ_ℓ)`,

where the inverse limit is taken along the reductions `ℤ/ℓⁿ⁺¹ → ℤ/ℓⁿ` and
`T_ℓ Pic(X) = lim_n Pic(X)[ℓⁿ] = T_ℓ J` is the Tate module of the Jacobian. It is characterised
by `f(t) ≡ ⟨xₙ, tₙ⟩ mod ℓⁿ`, where `⟨-, -⟩` is the cup-trace pairing with the Kummer class
(`AlgebraicGeometry.Scheme.EtaleTorsor.toZModPow_sheafHOneLimitAddEquivDualTateModule_apply`),
and it is equivariant for automorphisms of `X`, e.g. for the Galois action
(`AlgebraicGeometry.Scheme.EtaleTorsor.sheafHOneLimitAddEquivDualTateModule_mapIsoH1`). -/
noncomputable def sheafHOneLimitAddEquivDualTateModule :
    sheafHOneLimit X l ≃+
      (AddCommGroup.tateModule l (Additive X.Pic) →ₗ[ℤ_[l]] ℤ_[l]) :=
  (sheafHOneLimitAddEquivTorsionDualLimit s G hl).trans
    (AddCommGroup.tateModule.torsionDualLimitAddEquiv
      (exists_zsmul_eq_of_pow_zsmul_eq_zero hl))

/-- The reduction modulo `ℓⁿ` of `f(t)`, for `f` attached to a compatible family `x` of classes,
is the pairing of `xₙ` with the `n`-th coordinate of `t`. -/
lemma toZModPow_sheafHOneLimitAddEquivDualTateModule_apply (x : sheafHOneLimit X l)
    (t : AddCommGroup.tateModule l (Additive X.Pic)) (n : ℕ) :
    PadicInt.toZModPow n (sheafHOneLimitAddEquivDualTateModule s G hl x t) =
      sheafHPicTorsionDualAddEquiv s G hl n (x.1 n)
        (AddCommGroup.tateModule.coordTorsion t n) :=
  AddCommGroup.tateModule.toZModPow_torsionDualLimitAddEquiv_apply
    (exists_zsmul_eq_of_pow_zsmul_eq_zero hl) (sheafHOneLimitAddEquivTorsionDualLimit s G hl x) t n

section Transport

variable (f : X ⟶ X) [IsIso f] (σ : Spec (.of k) ⟶ Spec (.of k)) [IsIso σ]
  (hf : f ≫ (X ↘ Spec (.of k)) = (X ↘ Spec (.of k)) ≫ σ)

include hf in
/-- **Equivariance at finite level.** For an automorphism `f` of `X` over an automorphism of
`Spec k`, the transport of classes along `f` corresponds to precomposition with the pullback
`f^*` of line bundles. -/
lemma sheafHPicTorsionDualAddEquiv_mapIsoH1 (n : ℕ) (x : Sheaf.H (constantZModPow X l n) 1)
    (y : AddSubgroup.torsionBy (Additive X.Pic) ((l : ℤ) ^ n)) :
    sheafHPicTorsionDualAddEquiv s G hl n (mapIsoH1 X _ (asIso f) x) y =
      sheafHPicTorsionDualAddEquiv s G hl n x
        ⟨(Pic.mapHom f).toAdditive y, AddSubgroup.apply_mem_torsionBy _ y.2⟩ := by
  obtain ⟨T, rfl⟩ := (bijective_classH1 (M := ULift.{u + 1} (ZMod (l ^ n))) (Y := X)).2 x
  induction T using Quotient.inductionOn with | h t => ?_
  rw [mapIsoH1_classH1, sheafHPicTorsionDualAddEquiv_classH1, sheafHPicTorsionDualAddEquiv_classH1,
    picPairing_transport f σ hf _ t (t.mapIso (asIso f)) (𝟙 _) (Category.id_comp _).symm
      (by rw [Category.comp_id, Category.id_comp]; rfl)]
  rfl

include hf in
/-- **Equivariance.** For an automorphism `f` of `X` over an automorphism of `Spec k` (e.g. the
action of an element of `Gal(k̄₀ / k₀)` on the geometric fibre of a curve over `k₀`), the
isomorphism `lim_n H¹(X, ℤ/ℓⁿ) ≃+ Hom_{ℤ_ℓ}(T_ℓ Pic(X), ℤ_ℓ)` carries the transport of
compatible families of classes along `f` to precomposition with the map `T_ℓ(f^*)` induced by
the pullback of line bundles. -/
theorem sheafHOneLimitAddEquivDualTateModule_mapIsoH1 (x y : sheafHOneLimit X l)
    (hxy : ∀ n, y.1 n = mapIsoH1 X _ (asIso f) (x.1 n)) :
    sheafHOneLimitAddEquivDualTateModule s G hl y =
      (sheafHOneLimitAddEquivDualTateModule s G hl x).comp
        (AddCommGroup.tateModule.map (Pic.mapHom f).toAdditive) := by
  refine LinearMap.ext fun t ↦ PadicInt.ext_of_toZModPow.1 fun n ↦ ?_
  rw [LinearMap.comp_apply, toZModPow_sheafHOneLimitAddEquivDualTateModule_apply,
    toZModPow_sheafHOneLimitAddEquivDualTateModule_apply, hxy,
    sheafHPicTorsionDualAddEquiv_mapIsoH1 s G hl f σ hf]
  rfl

end Transport

end AlgebraicGeometry.Scheme.EtaleTorsor
