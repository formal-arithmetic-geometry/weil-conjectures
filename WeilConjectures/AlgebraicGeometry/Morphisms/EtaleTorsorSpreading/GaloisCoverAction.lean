/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading.GaloisCoverRank

/-!
# The ring of functions of a Galois cover over an affine open

Let `Z` be a Galois cover of a scheme `Y` with finite group `G` and `V ⊆ Y` an affine open, with
`A = Γ(Y, V)` and `L = Γ(Z.P, π⁻¹ V)`. Then:

* `G` acts on `L` by `A`-algebra automorphisms
  (`AlgebraicGeometry.Scheme.GaloisCover.galoisAction`, `g • f = f ∘ g⁻¹`);
* `L` is faithfully flat over `A`
  (`AlgebraicGeometry.Scheme.GaloisCover.comap_surjective_app`);
* `L` has rank `|G|` over `A` at every prime
  (`AlgebraicGeometry.Scheme.GaloisCover.rankAtStalk_app_eq`);
* the invariants of `L` are `A`
  (`AlgebraicGeometry.Scheme.GaloisCover.mem_range_app_of_forall_smul_eq`).

So `L` is a Galois `A`-algebra with group `G`. These facts are used in the trait case of the
proof of the spreading theorem (blueprint `sbc-thm-spreading-finite-etale-galois`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

/-- Sections of the structure sheaf of a scheme agree if they agree after pullback along a
jointly surjective family of open immersions. -/
lemma Scheme.app_eq_of_isOpenImmersion {X : Scheme.{u}} {ι : Type*} {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (f i)] (hf : ∀ x : X, ∃ i y, f i y = x)
    {U : X.Opens} {s t : Γ(X, U)} (h : ∀ i, (f i).app U s = (f i).app U t) : s = t := by
  refine TopCat.Presheaf.section_ext X.sheaf U s t fun x hx ↦ ?_
  obtain ⟨i, y, rfl⟩ := hf x
  have h' : X.presheaf.germ U (f i y) hx s = X.presheaf.germ U (f i y) hx t := by
    apply (ConcreteCategory.bijective_of_isIso ((f i).stalkMap y)).1
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply, h i]
  exact h'

/-- `appLE` only depends on the morphism. -/
lemma Scheme.Hom.appLE_eq_of_eq {X X' : Scheme.{u}} {f f' : X ⟶ X'} (h : f = f') (U : X'.Opens)
    (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ f' ⁻¹ᵁ U) : f.appLE U V e = f'.appLE U V e' := by
  subst h
  rfl

/-- `appLE` of the identity on an open is the identity. -/
lemma Scheme.Hom.id_appLE_self {X : Scheme.{u}} (U : X.Opens) (e : U ≤ (𝟙 X) ⁻¹ᵁ U) :
    (𝟙 X : X ⟶ X).appLE U U e = 𝟙 _ := by
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
  exact X.presheaf.map_id _

/-- Every point of a coproduct of schemes lies in one of the summands. -/
lemma exists_sigmaι_eq {σ : Type*} [Small.{u} σ] (g : σ → Scheme.{u}) (x : (∐ g :)) :
    ∃ i y, Sigma.ι g i y = x := by
  obtain ⟨y, hy⟩ := (sigmaOpenCover g).covers x
  exact ⟨_, y, hy⟩

/-- If `m` maps everything into `U`, so does `f ≫ m`. -/
lemma Scheme.Hom.top_le_preimage_comp {X X' Y : Scheme.{u}} (f : X ⟶ X') (m : X' ⟶ Y)
    {U : Y.Opens} (e : ⊤ ≤ m ⁻¹ᵁ U) : ⊤ ≤ (f ≫ m) ⁻¹ᵁ U := by
  rw [top_le_iff] at e ⊢
  rw [Scheme.Hom.comp_preimage, e, Scheme.Hom.preimage_top]

/-- Pulling back along `f` a section pulled back along `m` is pulling back along `f ≫ m`. -/
lemma Scheme.Hom.app_top_appLE_apply {X X' Y : Scheme.{u}} (f : X ⟶ X') (m : X' ⟶ Y)
    (U : Y.Opens) (e : ⊤ ≤ m ⁻¹ᵁ U) (s : Γ(Y, U)) :
    (f.app ⊤).hom ((m.appLE U ⊤ e).hom s) =
      ((f ≫ m).appLE U ⊤ (f.top_le_preimage_comp m e)).hom s := by
  have h : f.appLE ⊤ ⊤ (by simp) = f.app ⊤ := by
    simp [Scheme.Hom.appLE]
  rw [← Scheme.Hom.appLE_comp_appLE f m U ⊤ ⊤ e (by simp), h]
  rfl

/-- Pulling back sections over an affine open `U` along `Spec Γ(X, U) ⟶ X` is the inverse of
`Γ(Spec R, ⊤) ≅ R`. -/
lemma IsAffineOpen.fromSpec_appLE_top {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (e : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ e = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp,
    Subsingleton.elim (_ ≫ _) (𝟙 _), CategoryTheory.Functor.map_id, Category.comp_id]

/-- For an affine open `U` and a ring map `r : Γ(X, U) ⟶ R`, pulling back sections over `U`
along `Spec R ⟶ Spec Γ(X, U) ⟶ X` is `r`. -/
lemma IsAffineOpen.appLE_SpecMap_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {R : CommRingCat.{u}} (r : Γ(X, U) ⟶ R) (e : ⊤ ≤ (Spec.map r ≫ hU.fromSpec) ⁻¹ᵁ U) :
    (Spec.map r ≫ hU.fromSpec).appLE U ⊤ e ≫ (Scheme.ΓSpecIso R).hom = r := by
  have h : (Spec.map r).appLE ⊤ ⊤ (by simp) = (Spec.map r).appTop := by
    simp [Scheme.Hom.appLE]
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map r) hU.fromSpec U ⊤ ⊤ (by simp) (by simp),
    hU.fromSpec_appLE_top, h, Category.assoc, Scheme.ΓSpecIso_naturality,
    Iso.inv_hom_id_assoc]

namespace Scheme.GaloisCover

variable {G : Type (u + 1)} [Group G] [Finite G] {Y : Scheme.{u}} (Z : GaloisCover G Y)

/-- The open `π⁻¹ V` is stable under the action of `G`. -/
lemma le_preimage_smul (g : G) (V : Y.Opens) : Z.π ⁻¹ᵁ V ≤ Z.smul g ⁻¹ᵁ Z.π ⁻¹ᵁ V := by
  intro x hx
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, Z.smul_π]
  exact hx

/-- The pullback of functions on `π⁻¹ V` along the action of `g`. -/
def appSMul (g : G) (V : Y.Opens) : Γ(Z.P, Z.π ⁻¹ᵁ V) ⟶ Γ(Z.P, Z.π ⁻¹ᵁ V) :=
  (Z.smul g).appLE _ _ (Z.le_preimage_smul g V)

lemma appSMul_one (V : Y.Opens) : Z.appSMul 1 V = 𝟙 _ := by
  rw [appSMul, Scheme.Hom.appLE_eq_of_eq Z.one_smul (Z.π ⁻¹ᵁ V) (Z.π ⁻¹ᵁ V) _ le_rfl,
    Scheme.Hom.id_appLE_self]

lemma appSMul_mul (g h : G) (V : Y.Opens) :
    Z.appSMul (g * h) V = Z.appSMul g V ≫ Z.appSMul h V := by
  rw [appSMul, appSMul, appSMul, Scheme.Hom.appLE_comp_appLE]
  exact Scheme.Hom.appLE_eq_of_eq (Z.mul_smul g h) _ _ _ _

lemma app_comp_appSMul (g : G) (V : Y.Opens) :
    Z.π.app V ≫ Z.appSMul g V = Z.π.app V := by
  rw [Scheme.Hom.app_eq_appLE, appSMul, Scheme.Hom.appLE_comp_appLE]
  exact Scheme.Hom.appLE_eq_of_eq (Z.smul_π g) _ _ _ _

lemma appSMul_app_apply (g : G) (V : Y.Opens) (a : Γ(Y, V)) :
    (Z.appSMul g V).hom ((Z.π.app V).hom a) = (Z.π.app V).hom a :=
  congr(($(Z.app_comp_appSMul g V)).hom a)

/-- The action of `G` on `Γ(Z.P, π⁻¹ V)`: `g • f = f ∘ g⁻¹`. This is data and not an instance;
use it through `letI`. -/
@[reducible] def galoisAction (V : Y.Opens) : MulSemiringAction G Γ(Z.P, Z.π ⁻¹ᵁ V) where
  smul g x := (Z.appSMul g⁻¹ V).hom x
  one_smul x := by
    have e : Z.appSMul 1⁻¹ V = 𝟙 _ := by rw [inv_one, appSMul_one]
    exact congr(($e).hom x)
  mul_smul g h x := by
    have e : Z.appSMul (g * h)⁻¹ V = Z.appSMul h⁻¹ V ≫ Z.appSMul g⁻¹ V := by
      rw [mul_inv_rev, appSMul_mul]
    exact congr(($e).hom x)
  smul_zero g := map_zero _
  smul_add g := map_add _
  smul_one g := map_one _
  smul_mul g := map_mul _

lemma galoisAction_smul (V : Y.Opens) (g : G) (x : Γ(Z.P, Z.π ⁻¹ᵁ V)) :
    letI := Z.galoisAction V
    g • x = (Z.appSMul g⁻¹ V).hom x :=
  rfl

/-- The action of `G` on `Γ(Z.P, π⁻¹ V)` is by `Γ(Y, V)`-algebra automorphisms. -/
lemma smulCommClass_galoisAction (V : Y.Opens) :
    letI := Z.galoisAction V
    letI := (Z.π.app V).hom.toAlgebra
    SMulCommClass G Γ(Y, V) Γ(Z.P, Z.π ⁻¹ᵁ V) := by
  let := Z.galoisAction V
  let := (Z.π.app V).hom.toAlgebra
  refine ⟨fun g a x ↦ ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def, galoisAction_smul, galoisAction_smul, map_mul]
  exact congrArg (· * _) (Z.appSMul_app_apply g⁻¹ V a)

/-- Over an affine open `V`, every prime of `Γ(Y, V)` lies under a prime of `Γ(Z.P, π⁻¹ V)`. -/
lemma comap_surjective_app {V : Y.Opens} (hV : IsAffineOpen V) :
    Function.Surjective (PrimeSpectrum.comap (Z.π.app V).hom) := by
  intro p
  have := Z.isFinite
  have := Z.surjective
  have hW : IsAffineOpen (Z.π ⁻¹ᵁ V) := hV.preimage Z.π
  obtain ⟨z, hz⟩ := Z.π.surjective (hV.fromSpec p)
  have hzW : z ∈ Z.π ⁻¹ᵁ V := by
    rw [Scheme.Hom.mem_preimage, hz, ← SetLike.mem_coe, ← hV.range_fromSpec]
    exact Set.mem_range_self _
  rw [← SetLike.mem_coe, ← hW.range_fromSpec] at hzW
  obtain ⟨P, rfl⟩ := hzW
  refine ⟨P, ?_⟩
  have h1 := congrArg (fun m ↦ m P) (IsAffineOpen.SpecMap_appLE_fromSpec Z.π hV hW le_rfl)
  simp only [Scheme.Hom.comp_apply] at h1
  rw [hz] at h1
  have := hV.isOpenImmersion_fromSpec
  rw [Scheme.Hom.app_eq_appLE]
  exact hV.fromSpec.isOpenEmbedding.injective h1

set_option backward.isDefEq.respectTransparency false in
/-- **The rank of a Galois cover.** For a Galois cover `Z` of `Y` with group `G` and an affine
open `V ⊆ Y`, the rank of `Γ(Z.P, π⁻¹ V)` over `Γ(Y, V)` is `|G|` at every prime: the
geometric fibre is nonempty (`π` is surjective) and `G` acts freely on its points. -/
theorem rankAtStalk_app_eq {V : Y.Opens} (hV : IsAffineOpen V) (p : PrimeSpectrum Γ(Y, V)) :
    letI := (Z.π.app V).hom.toAlgebra
    Module.rankAtStalk (R := Γ(Y, V)) Γ(Z.P, Z.π ⁻¹ᵁ V) p = Nat.card G := by
  let := (Z.π.app V).hom.toAlgebra
  refine le_antisymm (Z.rankAtStalk_app_le hV p) ?_
  have := Z.isFinite
  have := Z.etale
  have hW : IsAffineOpen (Z.π ⁻¹ᵁ V) := hV.preimage Z.π
  have : Module.Finite Γ(Y, V) Γ(Z.P, Z.π ⁻¹ᵁ V) := IsFinite.finite_app Z.π _ hV
  have : Algebra.Etale Γ(Y, V) Γ(Z.P, Z.π ⁻¹ᵁ V) := by
    have := HasRingHomProperty.appLE @Etale Z.π inferInstance ⟨_, hV⟩ ⟨_, hW⟩ le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at this
  -- the geometric fibre over `p`
  let Ω := AlgebraicClosure p.asIdeal.ResidueField
  let A := Ω ⊗[Γ(Y, V)] Γ(Z.P, Z.π ⁻¹ᵁ V)
  have hrank : Module.rankAtStalk (R := Γ(Y, V)) Γ(Z.P, Z.π ⁻¹ᵁ V) p =
      Module.finrank Ω A := by
    have h := Module.rankAtStalk_baseChange (R := Γ(Y, V)) (M := Γ(Z.P, Z.π ⁻¹ᵁ V))
      (S := Ω) ⟨⊥, Ideal.isPrime_bot⟩
    have hp : PrimeSpectrum.comap (algebraMap Γ(Y, V) Ω) ⟨⊥, Ideal.isPrime_bot⟩ = p := by
      ext1
      rw [PrimeSpectrum.comap_asIdeal, ← RingHom.ker_eq_comap_bot,
        IsScalarTower.algebraMap_eq Γ(Y, V) p.asIdeal.ResidueField Ω,
        RingHom.ker_comp_of_injective _ (algebraMap p.asIdeal.ResidueField Ω).injective,
        Ideal.ker_algebraMap_residueField]
    rw [hp, Module.rankAtStalk_eq_finrank_of_free] at h
    exact h.symm
  have hpos : 0 < Module.finrank Ω A := by
    rw [← hrank, Module.rankAtStalk_pos_iff_mem_support, Module.support_of_algebra,
      PrimeSpectrum.mem_zeroLocus]
    obtain ⟨P, hP⟩ := Z.comap_surjective_app hV p
    rw [← hP]
    intro x hx
    exact Ideal.mem_comap.2 ((RingHom.mem_ker.1 hx).symm ▸ zero_mem _)
  obtain ⟨ψ, -⟩ := Algebra.Etale.exists_injective_algHom_of_isSepClosed Ω A
  -- a geometric point `f₀` of the fibre and its translates
  let f₀ : Γ(Z.P, Z.π ⁻¹ᵁ V) →+* Ω :=
    (((ψ ⟨0, hpos⟩).restrictScalars Γ(Y, V)).comp Algebra.TensorProduct.includeRight).toRingHom
  let σ (g : G) : Γ(Z.P, Z.π ⁻¹ᵁ V) →ₐ[Γ(Y, V)] Γ(Z.P, Z.π ⁻¹ᵁ V) :=
    { (Z.appSMul g V).hom with commutes' := Z.appSMul_app_apply g V }
  let ψg (g : G) : A →ₐ[Ω] Ω :=
    (ψ ⟨0, hpos⟩).comp (Algebra.TensorProduct.map (AlgHom.id Ω Ω) (σ g))
  have hψg (g : G) (x : Γ(Z.P, Z.π ⁻¹ᵁ V)) : ψg g (1 ⊗ₜ x) = f₀ ((Z.appSMul g V).hom x) := by
    rw [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul]
    rfl
  have hinj : Function.Injective ψg := by
    intro g h hgh
    let x₀ : Spec (.of Ω) ⟶ Z.P := Spec.map (CommRingCat.ofHom f₀) ≫ hW.fromSpec
    have hx (g : G) : Spec.map (CommRingCat.ofHom (f₀.comp (Z.appSMul g V).hom)) ≫
        hW.fromSpec = x₀ ≫ Z.smul g := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom, appSMul,
        IsAffineOpen.SpecMap_appLE_fromSpec (Z.smul g) hW hW, ← Category.assoc]
    have heq : f₀.comp (Z.appSMul g V).hom = f₀.comp (Z.appSMul h V).hom := by
      ext x
      rw [RingHom.comp_apply, RingHom.comp_apply, ← hψg, ← hψg, hgh]
    have : Nonempty (Spec (.of Ω)) := inferInstanceAs (Nonempty (PrimeSpectrum Ω))
    exact Z.eq_of_comp_smul_eq x₀ (by rw [← hx, ← hx, heq])
  have := Fintype.ofFinite G
  rw [hrank, Nat.card_eq_fintype_card, ← Module.finrank_linearMap_self Ω Ω A]
  exact ((linearIndependent_toLinearMap Ω A Ω).comp ψg hinj).fintype_card_le_finrank

/-- A function on `π⁻¹ V` fixed by all `appSMul g` is equal to its two pullbacks to
`Spec (L ⊗[A] L)`. -/
lemma tmul_one_eq_one_tmul {V : Y.Opens} (hV : IsAffineOpen V) (x : Γ(Z.P, Z.π ⁻¹ᵁ V))
    (hx : ∀ g : G, (Z.appSMul g V).hom x = x) :
    letI := (Z.π.app V).hom.toAlgebra
    x ⊗ₜ[Γ(Y, V)] (1 : Γ(Z.P, Z.π ⁻¹ᵁ V)) = 1 ⊗ₜ x := by
  let := (Z.π.app V).hom.toAlgebra
  have := Z.isFinite
  have hW : IsAffineOpen (Z.π ⁻¹ᵁ V) := hV.preimage Z.π
  let R : CommRingCat.{u} := .of (Γ(Z.P, Z.π ⁻¹ᵁ V) ⊗[Γ(Y, V)] Γ(Z.P, Z.π ⁻¹ᵁ V))
  let iL : Γ(Z.P, Z.π ⁻¹ᵁ V) ⟶ R := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let iR : Γ(Z.P, Z.π ⁻¹ᵁ V) ⟶ R :=
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  let a : Spec R ⟶ Z.P := Spec.map iL ≫ hW.fromSpec
  let b : Spec R ⟶ Z.P := Spec.map iR ≫ hW.fromSpec
  have hab : a ≫ Z.π = b ≫ Z.π := by
    have h1 : Z.π.app V ≫ iL = Z.π.app V ≫ iR := by
      ext r
      exact Algebra.TensorProduct.tmul_one_eq_one_tmul (A := Γ(Z.P, Z.π ⁻¹ᵁ V))
        (B := Γ(Z.P, Z.π ⁻¹ᵁ V)) r
    simp only [a, b, Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec Z.π hV hW le_rfl,
      ← Scheme.Hom.app_eq_appLE, ← Spec.map_comp_assoc, h1]
  have := Z.isIso_sigmaDesc
  let e := asIso (Sigma.desc fun g : G ↦
    pullback.lift (f := Z.π) (g := Z.π) (Z.smul g) (𝟙 Z.P) (by simp [Z.smul_π]))
  let t := pullback.lift a b hab
  let fg (g : G) := pullback.fst t (Sigma.ι (fun _ : G ↦ Z.P) g ≫ e.hom)
  let sg (g : G) := pullback.snd t (Sigma.ι (fun _ : G ↦ Z.P) g ≫ e.hom)
  have hfst (g : G) : fg g ≫ a = sg g ≫ Z.smul g := by
    have := congrArg (· ≫ pullback.fst Z.π Z.π) (pullback.condition (f := t)
      (g := Sigma.ι (fun _ : G ↦ Z.P) g ≫ e.hom))
    simpa [t, e, fg, sg] using this
  have hsnd (g : G) : fg g ≫ b = sg g := by
    have := congrArg (· ≫ pullback.snd Z.π Z.π) (pullback.condition (f := t)
      (g := Sigma.ι (fun _ : G ↦ Z.P) g ≫ e.hom))
    simpa [t, e, fg, sg] using this
  have key : (a.appLE (Z.π ⁻¹ᵁ V) ⊤ (by simp [a])).hom x =
      (b.appLE (Z.π ⁻¹ᵁ V) ⊤ (by simp [b])).hom x := by
    refine Scheme.app_eq_of_isOpenImmersion fg (fun y ↦ ?_) fun g ↦ ?_
    · obtain ⟨g, z, hz⟩ := exists_sigmaι_eq (fun _ : G ↦ Z.P) (e.inv (t y))
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := t)
        (g := Sigma.ι (fun _ : G ↦ Z.P) g ≫ e.hom) y z (by
          rw [Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply, e.inv_hom_id]
          rfl)
      exact ⟨g, w, hw⟩
    · have hle : Z.π ⁻¹ᵁ V ≤ Z.smul g ⁻¹ᵁ Z.π ⁻¹ᵁ V := Z.le_preimage_smul g V
      have hsW : ⊤ ≤ sg g ⁻¹ᵁ Z.π ⁻¹ᵁ V := hsnd g ▸ (fg g).top_le_preimage_comp b (by simp [b])
      rw [Scheme.Hom.app_top_appLE_apply, Scheme.Hom.app_top_appLE_apply,
        Scheme.Hom.appLE_eq_of_eq (hfst g) _ _ _ (hsW.trans (Scheme.Hom.preimage_mono _ hle)),
        Scheme.Hom.appLE_eq_of_eq (hsnd g) _ _ _ hsW,
        ← Scheme.Hom.appLE_comp_appLE (sg g) (Z.smul g) _ _ ⊤ hle hsW]
      rw [CommRingCat.comp_apply]
      exact congrArg _ (hx g)
  have hL := congr(($(hW.appLE_SpecMap_fromSpec iL (by simp))).hom x)
  have hR := congr(($(hW.appLE_SpecMap_fromSpec iR (by simp))).hom x)
  rw [CommRingCat.comp_apply] at hL hR
  exact hL.symm.trans ((congrArg _ key).trans hR)

/-- **The invariants of a Galois cover.** For a Galois cover `Z` of `Y` with group `G` and an
affine open `V ⊆ Y`, a function on `π⁻¹ V` invariant under `G` comes from `Γ(Y, V)`: it agrees
with its translate on `Spec (L ⊗[A] L) ⟶ P ×_Y P ≅ ∐_{g ∈ G} P`, and `A → L` is faithfully
flat. -/
theorem mem_range_app_of_forall_smul_eq {V : Y.Opens} (hV : IsAffineOpen V)
    (x : Γ(Z.P, Z.π ⁻¹ᵁ V)) (hx : letI := Z.galoisAction V; ∀ g : G, g • x = x) :
    x ∈ Set.range (Z.π.app V).hom := by
  let := (Z.π.app V).hom.toAlgebra
  have := Z.isFinite
  have := Z.etale
  have hW : IsAffineOpen (Z.π ⁻¹ᵁ V) := hV.preimage Z.π
  have : Algebra.Etale Γ(Y, V) Γ(Z.P, Z.π ⁻¹ᵁ V) := by
    have := HasRingHomProperty.appLE @Etale Z.π inferInstance ⟨_, hV⟩ ⟨_, hW⟩ le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at this
  have : Module.FaithfullyFlat Γ(Y, V) Γ(Z.P, Z.π ⁻¹ᵁ V) :=
    .of_comap_surjective (Z.comap_surjective_app hV)
  have hE := Algebra.IsEffective.of_faithfullyFlat Γ(Y, V) Γ(Z.P, Z.π ⁻¹ᵁ V)
  refine hE.eqLocus_includeLeft_includeRight.le ?_
  exact Z.tmul_one_eq_one_tmul hV x fun g ↦ by
    simpa [galoisAction_smul] using hx g⁻¹

end Scheme.GaloisCover

end AlgebraicGeometry
