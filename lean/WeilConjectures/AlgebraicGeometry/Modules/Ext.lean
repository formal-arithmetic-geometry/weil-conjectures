/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.Cohomology.InjectiveFlasque
public import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
public import WeilConjectures.AlgebraicGeometry.Modules.HomTensor
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-!
# Ext groups of sheaves of modules on a scheme

For `𝒪_X`-modules `ℱ` and `𝒢` on a scheme `X`, the group `Ext^i_X(ℱ, 𝒢)` is the `i`-th right
derived functor of `Hom_{𝒪_X}(-, 𝒢)` evaluated at `ℱ`. We use Mathlib's `Abelian.Ext`, the
morphisms `ℱ ⟶ 𝒢[i]` in the derived category of the abelian category `X.Modules`, which computes
these derived functors.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.Ext`: the group `Ext^i_X(ℱ, 𝒢)`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.contravariantSequence_ext_exact`: the long exact sequence of
  `Ext(-, 𝒢)` attached to a short exact sequence.
- `AlgebraicGeometry.Scheme.Modules.nonempty_ext_unit_addEquiv_H`: `Ext^n_X(𝒪_X, M) ≅ H^n(X, M)`,
  by dimension shifting, injective `𝒪_X`-modules being flasque, hence acyclic.
- `AlgebraicGeometry.Scheme.Modules.nonempty_ext_addEquiv_H`: for finite locally free `ℱ`,
  `Ext^i_X(ℱ, 𝒢) ≅ H^i(X, ℱᵛ ⊗ 𝒢)`.

## Implementation notes

The `Ext` groups need the hypothesis `HasExt.{u} X.Modules`, which holds because `X.Modules` is a
Grothendieck abelian category (`AlgebraicGeometry.Scheme.Modules.isGrothendieckAbelian`); it is
kept as an instance argument.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [HasExt.{u} X.Modules]

/-- The **Ext groups** `Ext^i_X(ℱ, 𝒢)` of two `𝒪_X`-modules: the right derived functors of
`Hom_{𝒪_X}(-, 𝒢)` on the abelian category of `𝒪_X`-modules, evaluated at `ℱ`. In degree `0` this
is `Hom_{𝒪_X}(ℱ, 𝒢)` (`CategoryTheory.Abelian.Ext.homEquiv₀`).

(blueprint: `def-sc-ext-sheaf`) -/
abbrev Ext (ℱ 𝒢 : X.Modules) (i : ℕ) : Type u :=
  Abelian.Ext ℱ 𝒢 i

/-- **The long exact `Ext` sequence.** A short exact sequence `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of
`𝒪_X`-modules gives, for every `𝒢` and `1 + n₀ = n₁`, the exact sequence
`Ext^{n₀}(ℱ₃, 𝒢) → Ext^{n₀}(ℱ₂, 𝒢) → Ext^{n₀}(ℱ₁, 𝒢) → Ext^{n₁}(ℱ₃, 𝒢) → Ext^{n₁}(ℱ₂, 𝒢) →
Ext^{n₁}(ℱ₁, 𝒢)`. The comparison with sheaf cohomology for finite locally free `ℱ` is
`AlgebraicGeometry.Scheme.Modules.nonempty_ext_addEquiv_H`.

(blueprint: `rem-ptr-sc-ext-sheaf-4`) -/
theorem contravariantSequence_ext_exact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (𝒢 : X.Modules) (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    (Abelian.Ext.contravariantSequence hS 𝒢 n₀ n₁ h).Exact :=
  Abelian.Ext.contravariantSequence_exact hS 𝒢 n₀ n₁ h


section Comparison

/-- Two quotients by the kernels of surjective additive maps are identified by an additive
equivalence of the sources matching the kernels. -/
private noncomputable def addEquivOfSurjective {A₁ A₂ B₁ B₂ : Type*} [AddCommGroup A₁]
    [AddCommGroup A₂] [AddCommGroup B₁] [AddCommGroup B₂] (δ₁ : A₁ →+ B₁) (δ₂ : A₂ →+ B₂)
    (h₁ : Function.Surjective δ₁) (h₂ : Function.Surjective δ₂) (e : A₁ ≃+ A₂)
    (he : δ₁.ker.map e.toAddMonoidHom = δ₂.ker) : B₁ ≃+ B₂ :=
  (QuotientAddGroup.quotientKerEquivOfSurjective δ₁ h₁).symm.trans
    ((QuotientAddGroup.congr _ _ e he).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective δ₂ h₂))

/-- The global sections of `M` as morphisms `𝒪_X ⟶ M`. -/
noncomputable def unitHomAddEquiv (M : X.Modules) : (𝟙_ X.Modules ⟶ M) ≃+ Γ(M, ⊤) where
  toFun f := Hom.app f ⊤ (1 : Γ(X, ⊤))
  invFun u := homOfGlobalSection M u
  left_inv f := by
    refine (SheafOfModules.unitHomEquiv M).injective (Subtype.ext (funext fun U ↦ ?_))
    change Hom.app (homOfGlobalSection M (Hom.app f ⊤ (1 : Γ(X, ⊤)))) U.unop (1 : Γ(X, U.unop)) =
      Hom.app f U.unop (1 : Γ(X, U.unop))
    rw [homOfGlobalSection_app_one, ← Hom.app_presheaf_map]
    exact congrArg (Hom.app f U.unop)
      (map_one (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op).hom :)
  right_inv u := by
    change Hom.app (homOfGlobalSection M u) ⊤ (1 : Γ(X, ⊤)) = u
    rw [homOfGlobalSection_app_one, presheaf_map_id_apply]
  map_add' f g := rfl

omit [HasExt X.Modules] in
lemma unitHomAddEquiv_comp {M N : X.Modules} (f : 𝟙_ X.Modules ⟶ M) (g : M ⟶ N) :
    unitHomAddEquiv N (f ≫ g) = Hom.app g ⊤ (unitHomAddEquiv M f) :=
  rfl

/-- `Ext⁰(𝒪_X, M)` is the group of global sections of `M`. -/
noncomputable def extUnitZeroAddEquiv (M : X.Modules) : Ext (𝟙_ X.Modules) M 0 ≃+ Γ(M, ⊤) :=
  Abelian.Ext.addEquiv₀.trans (unitHomAddEquiv M)

lemma extUnitZeroAddEquiv_comp {M N : X.Modules} (g : M ⟶ N) (x : Ext (𝟙_ X.Modules) M 0) :
    extUnitZeroAddEquiv N (x.comp (Abelian.Ext.mk₀ g) (add_zero 0)) =
      Hom.app g ⊤ (extUnitZeroAddEquiv M x) := by
  obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective (𝟙_ X.Modules) M).2 x
  rw [Abelian.Ext.mk₀_comp_mk₀]
  have h (P : X.Modules) (h : 𝟙_ X.Modules ⟶ P) :
      Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ h) = h :=
    Abelian.Ext.addEquiv₀.apply_symm_apply h
  simp only [extUnitZeroAddEquiv, AddEquiv.trans_apply, h]
  rfl

omit [HasExt X.Modules] in
/-- `H⁰(X, M) ≅ Γ(M, ⊤)`, naturally. -/
lemma zeroLinearEquiv_map {M N : X.Modules} (g : M ⟶ N) (x : M.H 0) :
    H.zeroLinearEquiv N (H.map g 0 x) = Hom.app g ⊤ (H.zeroLinearEquiv M x) :=
  (Sheaf.H.equiv₀_naturality (hT := isTerminalTop) _ x).symm

/-- **`Ext` from the structure sheaf is sheaf cohomology.** For every `𝒪_X`-module `M`,
`Ext^n_X(𝒪_X, M) ≅ H^n(X, M)`: both vanish on injective `𝒪_X`-modules in positive degrees
(`AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_injective`), agree with global sections in
degree `0`, and have long exact sequences, so dimension shifting along an embedding of `M` into
an injective module identifies them. -/
theorem nonempty_ext_unit_addEquiv_H (n : ℕ) (M : X.Modules) :
    Nonempty (Ext (𝟙_ X.Modules) M n ≃+ M.H n) := by
  have : IsGrothendieckAbelian.{u} X.Modules := SheafOfModules.isGrothendieckAbelian X.ringCatSheaf
  have : EnoughInjectives X.Modules := IsGrothendieckAbelian.enoughInjectives
  induction n generalizing M with
  | zero => exact ⟨(extUnitZeroAddEquiv M).trans (H.zeroLinearEquiv M).toAddEquiv.symm⟩
  | succ n ih =>
    let S := ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M)) (cokernel.condition _)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    have hHI := subsingleton_H_of_injective S.X₂ n
    -- the connecting maps
    let δE : Ext (𝟙_ X.Modules) S.X₃ n →+ Ext (𝟙_ X.Modules) S.X₁ (n + 1) :=
      hS.extClass.postcomp (𝟙_ X.Modules) rfl
    have hδE : Function.Surjective δE := fun x ↦
      Abelian.Ext.covariant_sequence_exact₁ _ hS x (Abelian.Ext.eq_zero_of_injective _) rfl
    have hkerE : δE.ker = ((Abelian.Ext.mk₀ S.g).postcomp (𝟙_ X.Modules) (add_zero n)).range := by
      ext x
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
      constructor
      · intro hx
        exact Abelian.Ext.covariant_sequence_exact₃ _ hS x rfl hx
      · rintro ⟨y, rfl⟩
        change (y.comp (Abelian.Ext.mk₀ S.g) (add_zero n)).comp hS.extClass rfl = 0
        rw [Abelian.Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Abelian.Ext.comp_zero]
    have hδH : Function.Surjective (H.δ hS n) := by
      rw [← AddMonoidHom.range_eq_top, ← H.ker_map_f_eq_range_δ hS n]
      exact eq_top_iff.mpr fun x _ ↦ Subsingleton.elim _ _
    have hkerH := H.ker_δ_eq_range_map_g hS n
    rcases n with _ | n
    · -- degree one: the cokernels of `Γ(I) ⟶ Γ(Q)` on both sides
      let e : Ext (𝟙_ X.Modules) S.X₃ 0 ≃+ S.X₃.H 0 :=
        (extUnitZeroAddEquiv S.X₃).trans (H.zeroLinearEquiv S.X₃).toAddEquiv.symm
      refine ⟨addEquivOfSurjective δE (H.δ hS 0) hδE hδH e ?_⟩
      rw [hkerE, hkerH]
      ext z
      simp only [AddSubgroup.mem_map, AddMonoidHom.mem_range]
      constructor
      · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
        refine ⟨(H.zeroLinearEquiv S.X₂).symm (extUnitZeroAddEquiv S.X₂ y), ?_⟩
        apply (H.zeroLinearEquiv S.X₃).injective
        change _ = (H.zeroLinearEquiv S.X₃) ((H.zeroLinearEquiv S.X₃).symm _)
        rw [LinearEquiv.apply_symm_apply, zeroLinearEquiv_map, LinearEquiv.apply_symm_apply]
        exact (extUnitZeroAddEquiv_comp S.g y).symm
      · rintro ⟨y, rfl⟩
        refine ⟨_, ⟨(extUnitZeroAddEquiv S.X₂).symm (H.zeroLinearEquiv S.X₂ y), rfl⟩, ?_⟩
        apply (H.zeroLinearEquiv S.X₃).injective
        change (H.zeroLinearEquiv S.X₃) ((H.zeroLinearEquiv S.X₃).symm _) = _
        rw [LinearEquiv.apply_symm_apply, zeroLinearEquiv_map]
        exact (extUnitZeroAddEquiv_comp S.g _).trans
          (congrArg _ (AddEquiv.apply_symm_apply _ _))
    · -- higher degrees: both connecting maps are isomorphisms
      obtain ⟨e⟩ := ih S.X₃
      have hEI : Subsingleton (Ext (𝟙_ X.Modules) S.X₂ (n + 1)) :=
        Abelian.Ext.subsingleton_of_injective _ _ n
      have hHI' := subsingleton_H_of_injective S.X₂ n
      refine ⟨addEquivOfSurjective δE (H.δ hS (n + 1)) hδE hδH e ?_⟩
      rw [hkerE, hkerH]
      have h₁ : ((Abelian.Ext.mk₀ S.g).postcomp (𝟙_ X.Modules) (add_zero (n + 1))).range = ⊥ := by
        refine eq_bot_iff.mpr ?_
        rintro _ ⟨y, rfl⟩
        rw [Subsingleton.elim y 0, map_zero]
        exact zero_mem _
      have h₂ : (H.map S.g (n + 1)).range = ⊥ := by
        refine eq_bot_iff.mpr ?_
        rintro _ ⟨y, rfl⟩
        rw [Subsingleton.elim y 0, map_zero]
        exact zero_mem _
      rw [h₁, h₂, AddSubgroup.map_bot]

end Comparison


section LocallyFree

/-- `Ext` is invariant under isomorphisms in its second variable. -/
noncomputable def extAddEquivOfIsoRight {A B B' : X.Modules} (e : B ≅ B') (n : ℕ) :
    Ext A B n ≃+ Ext A B' n where
  toFun x := x.comp (Abelian.Ext.mk₀ e.hom) (add_zero n)
  invFun x := x.comp (Abelian.Ext.mk₀ e.inv) (add_zero n)
  left_inv x := by
    simp only [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
      Iso.hom_inv_id]
    exact Abelian.Ext.comp_mk₀_id x
  right_inv x := by
    simp only [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
      Iso.inv_hom_id]
    exact Abelian.Ext.comp_mk₀_id x
  map_add' x y := Abelian.Ext.add_comp _ _ _ _

/-- `Ext` is invariant under isomorphisms in its first variable. -/
noncomputable def extAddEquivOfIsoLeft {A A' B : X.Modules} (e : A' ≅ A) (n : ℕ) :
    Ext A B n ≃+ Ext A' B n where
  toFun x := (Abelian.Ext.mk₀ e.hom).comp x (zero_add n)
  invFun x := (Abelian.Ext.mk₀ e.inv).comp x (zero_add n)
  left_inv x := by
    dsimp only
    rw [← Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀, Iso.inv_hom_id]
    exact Abelian.Ext.mk₀_id_comp x
  right_inv x := by
    dsimp only
    rw [← Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀, Iso.hom_inv_id]
    exact Abelian.Ext.mk₀_id_comp x
  map_add' x y := Abelian.Ext.comp_add _ _ _ _

/-- For a finite locally free `ℱ`, tensoring with the dual is the internal hom out of `ℱ`. -/
noncomputable def tensorLeftDualIsoIhom (ℱ : X.Modules) [ℱ.IsFiniteLocallyFree] :
    tensorLeft ℱᵛ ≅ ihom ℱ :=
  NatIso.ofComponents (fun N ↦ asIso (dualTensorHom ℱ N)) fun g ↦
    dualTensorHom_naturality_right ℱ g

end LocallyFree
/-- **Ext of a finite locally free module.** For a finite locally free `𝒪_X`-module `ℱ` and any
`𝒪_X`-module `𝒢`, `Ext^i_X(ℱ, 𝒢) ≅ H^i(X, ℱᵛ ⊗ 𝒢)`. Indeed `Hom(ℱ, -) = Γ(X, ℱᵛ ⊗ -)` is the
composite of the exact functor `ℱᵛ ⊗ -` with `Γ(X, -)`. In particular
`Ext^i_X(𝒪_X, 𝒢) = H^i(X, 𝒢)`.

(blueprint: `lem-sc-ext-locally-free`) -/
theorem nonempty_ext_addEquiv_H (ℱ 𝒢 : X.Modules) [ℱ.IsFiniteLocallyFree] (i : ℕ) :
    Nonempty (Ext ℱ 𝒢 i ≃+ (ℱᵛ ⊗ 𝒢).H i) := by
  have : IsGrothendieckAbelian.{u} X.Modules := SheafOfModules.isGrothendieckAbelian X.ringCatSheaf
  have : EnoughInjectives X.Modules := IsGrothendieckAbelian.enoughInjectives
  have := IsFiniteLocallyFree.dual ℱ
  have := SheafOfModules.isIso_bidual (R := X.sheaf) ℱ
  -- `ℱ ⊗ -` and `Hom(ℱ, -)` are exact: they are isomorphic to internal homs, respectively
  -- tensor products, out of finite locally free modules
  let eR : tensorLeft ℱᵛ ≅ ihom ℱ := tensorLeftDualIsoIhom ℱ
  let eL : tensorLeft ℱ ≅ ihom ℱᵛ :=
    (tensoringLeft X.Modules).mapIso (asIso (SheafOfModules.bidual (R := X.sheaf) ℱ)) ≪≫
      tensorLeftDualIsoIhom ℱᵛ
  have hadd (A : X.Modules) : (tensorLeft A).Additive := by
    have : PreservesColimitsOfSize.{0, 0} (tensorLeft A) :=
      (ihom.adjunction A).leftAdjoint_preservesColimits
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft A)
    exact Functor.additive_of_preservesBinaryBiproducts _
  have := hadd ℱ
  have := hadd ℱᵛ
  have : PreservesFiniteLimits (tensorLeft ℱ) := preservesFiniteLimits_of_natIso eL.symm
  have : PreservesFiniteColimits (ihom ℱ) := preservesFiniteColimits_of_natIso eR
  have : (ihom ℱ).Additive := Functor.additive_of_iso eR
  let adj := ihom.adjunction ℱ
  have hbij := adj.mapExtCounit_bijective (𝟙_ X.Modules) 𝒢 i
  obtain ⟨e⟩ := nonempty_ext_unit_addEquiv_H i (ℱᵛ ⊗ 𝒢)
  exact ⟨(extAddEquivOfIsoLeft (ρ_ ℱ) i).trans ((AddEquiv.ofBijective _ hbij).symm.trans
    ((extAddEquivOfIsoRight (eR.app 𝒢).symm i).trans e))⟩

end AlgebraicGeometry.Scheme.Modules
