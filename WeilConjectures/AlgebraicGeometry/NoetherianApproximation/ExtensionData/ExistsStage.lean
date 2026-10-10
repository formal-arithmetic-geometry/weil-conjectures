/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.ExtensionData.Basic
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# Existence of stages

Following Stacks 01Z7, stages exist below every index: the sections of `Wⱼ` over a basic open
form a finitely generated `ℤ`-algebra, and adjoining suitable elements of the fiber product
`Γ(X, V) ×_{Γ(W)} Γ(Wⱼ)` to a finitely generated subalgebra yields a stage
(`PreStage.stage`, `Stage.restrict`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
namespace Scheme.NoetherianApproximation
namespace ExtensionData

variable (E : ExtensionData.{u})
variable {E}

/-!
#### Existence of stages

Following Stacks 01Z7, we produce stages: the sections of `Wⱼ` over a basic open `Wⱼ(r l)`
form a finitely generated `ℤ`-algebra, and each generator is, up to a power of `r l`, the
second component of an element of the fiber product `Γ(X, V) ×_{Γ(W)} Γ(Wⱼ)`. Adjoining
these elements to any finitely generated subalgebra of the fiber product yields a stage.
-/

/-- (Implementation) The fiber product `Γ(X, V) ×_{Γ(W, 𝒪)} Γ(Wⱼ, 𝒪)`, i.e. the pairs of
sections agreeing on `W`, as a subalgebra of the product ring. The coefficient algebra of a
stage at `j` is a finitely generated subalgebra of it. -/
noncomputable def fiberProduct (E : ExtensionData.{u}) (j : Over E.i₀) :
    Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)) :=
  AlgHom.equalizer (E.sV.hom.comp (RingHom.fst _ _)).toIntAlgHom
    ((E.t j).hom.comp (RingHom.snd _ _)).toIntAlgHom

lemma mem_fiberProduct_iff (E : ExtensionData.{u}) {j : Over E.i₀}
    (p : Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)) :
    p ∈ E.fiberProduct j ↔ E.sV p.1 = E.t j p.2 := Iff.rfl

/-- (Implementation) The basic open of `W` attached to a generator `b l` is the pullback of
the basic open of `X` attached to it. -/
lemma basicOpen_sV (E : ExtensionData.{u}) (l : Fin E.n) :
    E.Wc.pt.basicOpen (E.sV (E.b l)) =
      (E.WU.ι ≫ E.U.ι) ⁻¹ᵁ E.X.basicOpen (E.b l) := by
  simp only [ExtensionData.sV, Scheme.basicOpen_appLE, top_inf_eq]

/-- (Implementation) The basic opens of the chosen generators cover `W`. -/
lemma iSup_basicOpen_sV (E : ExtensionData.{u}) :
    ⨆ l, E.Wc.pt.basicOpen (E.sV (E.b l)) = ⊤ := by
  simp_rw [E.basicOpen_sV]
  rw [← Scheme.Hom.preimage_iSup, ← E.hb']
  refine eq_top_iff.mpr fun x _ ↦ ?_
  have : (E.WU.ι ≫ E.U.ι) x ∈ (E.WU.ι ≫ E.U.ι).opensRange := ⟨x, rfl⟩
  rw [E.opensRange_WUι_comp_Uι] at this
  exact this

/-- (Implementation) `Wⱼ` is of finite type over `ℤ`, being open in a stage of the
approximation of `U`. -/
instance (j : Over E.i₀) :
    LocallyOfFiniteType (specULiftZIsTerminal.from (E.WD.obj j)) := by
  rw [specULiftZIsTerminal.hom_ext (specULiftZIsTerminal.from (E.WD.obj j))
    ((E.N.D.map j.hom ⁻¹ᵁ E.W₀).ι ≫ specULiftZIsTerminal.from (E.N.D.obj j.left))]
  infer_instance

instance : CompactSpace E.Wc.pt := by
  have := isAffineHom_π_app E.N.D E.cone E.N.isLimit E.i₀
  exact isCompact_iff_compactSpace.mp
    (QuasiCompact.isCompact_preimage (f := E.N.π.app E.i₀) _ E.W₀.2 E.hW₀c)

instance : QuasiSeparatedSpace E.Wc.pt := by
  have : QuasiSeparatedSpace E.U.toScheme :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ E.U.2).mp (.of_quasiSeparatedSpace _)
  exact (isQuasiSeparated_iff_quasiSeparatedSpace _ E.WU.2).mp (.of_quasiSeparatedSpace _)

variable (E) in
/-- (Implementation) Restricting a global section of `W` to the basic open of `sV (b l)`
factors through the restriction to the pullback of `X.basicOpen (b l)`; the two opens are
equal by `basicOpen_sV`. -/
lemma restrict_basicOpen_sV_eq (l : Fin E.n) (x : Γ(E.Wc.pt, ⊤)) :
    x |_ E.Wc.pt.basicOpen (E.sV (E.b l)) =
      (E.Wc.pt.presheaf.map (eqToHom (E.basicOpen_sV l)).op)
        ((E.Wc.pt.presheaf.map (homOfLE le_top).op) x) := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
  exact congrArg
    (fun f : E.Wc.pt.basicOpen (E.sV (E.b l)) ⟶ (⊤ : E.Wc.pt.Opens) ↦
      (E.Wc.pt.presheaf.map f.op).hom x)
    (Subsingleton.elim _ _)

/-- (Implementation, Stacks 01Z7) Every section over a basic open `Wⱼ(r l)` is, up to a
power of `r l`, the restriction of the second component of an element of the fiber product
`Γ(X, V) ×_{Γ(W)} Γ(Wⱼ)`. -/
lemma exists_mem_fiberProduct_res_eq_mul_pow (E : ExtensionData.{u}) {j : Over E.i₀}
    {l : Fin E.n} {rl : Γ(E.WD.obj j, ⊤)} (hrl : E.t j rl = E.sV (E.b l))
    (z : Γ(E.WD.obj j, (E.WD.obj j).basicOpen rl)) :
    ∃ (m : ℕ) (p : Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)), p ∈ E.fiberProduct j ∧
      ((E.WD.obj j).presheaf.map (homOfLE le_top).op) p.2 =
        z * ((E.WD.obj j).presheaf.map (homOfLE le_top).op) rl ^ m := by
  classical
  -- Lift `z` to a global section `y` of `Wⱼ`, up to a power of `rl`.
  obtain ⟨m₀, y, hy⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated
    (E.WD.obj j) ⊤ isCompact_univ isQuasiSeparated_univ rl z
  -- The restriction of `t y` to the basic open of `W` comes from a section `zV` of
  -- `X.basicOpen (b l)`.
  have hiso := (E.WU.ι ≫ E.U.ι).isIso_app _ (E.basicOpen_le_opensRange l)
  obtain ⟨zV, hzV⟩ := (ConcreteCategory.bijective_of_isIso
    ((E.WU.ι ≫ E.U.ι).app (E.X.basicOpen (E.b l)))).2
    ((E.WU.toScheme.presheaf.map (homOfLE le_top).op) (E.t j y))
  -- Write `zV` as `v₀ / (b l) ^ K` using that `V` is affine.
  have := E.hV.isLocalization_basicOpen (E.b l)
  obtain ⟨⟨v₀, ⟨_, K, rfl⟩⟩, hv⟩ := IsLocalization.surj (M := Submonoid.powers (E.b l)) zV
  rw [map_pow] at hv
  -- Restricting sections of `V` to `X.basicOpen (b l)` and pulling back to `W` agrees with
  -- pulling back to `W` and restricting.
  have happ : ∀ x : Γ(E.X, E.V),
      ((E.WU.ι ≫ E.U.ι).app (E.X.basicOpen (E.b l)))
        ((algebraMap Γ(E.X, E.V) Γ(E.X, E.X.basicOpen (E.b l))) x) =
      (E.WU.toScheme.presheaf.map (homOfLE le_top).op) (E.sV x) := fun x ↦ by
    have h := congrArg
      (fun f : Γ(E.X, E.V) ⟶
          Γ(E.WU.toScheme, (E.WU.ι ≫ E.U.ι) ⁻¹ᵁ E.X.basicOpen (E.b l)) ↦ f x)
      (E.res_app_eq_sV_res l)
    dsimp only at h
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h
    exact h
  -- Transport the localization relation along the pullback to `W`.
  have e₁ := congrArg ((E.WU.ι ≫ E.U.ι).app (E.X.basicOpen (E.b l)) ·) hv
  dsimp only at e₁
  rw [map_mul, map_pow, happ, happ, hzV] at e₁
  have e₁' : (E.Wc.pt.presheaf.map (homOfLE le_top).op) (E.t j y) *
        (E.Wc.pt.presheaf.map (homOfLE le_top).op) (E.sV (E.b l)) ^ K =
      (E.Wc.pt.presheaf.map (homOfLE (le_top :
        (E.WU.ι ≫ E.U.ι) ⁻¹ᵁ E.X.basicOpen (E.b l) ≤ ⊤)).op) (E.sV v₀) := e₁
  -- `sV v₀` and `t (rl ^ K * y)` agree on the basic open of `sV (b l)`.
  have h6 : E.sV v₀ |_ E.Wc.pt.basicOpen (E.sV (E.b l)) =
      E.t j (rl ^ K * y) |_ E.Wc.pt.basicOpen (E.sV (E.b l)) := by
    rw [E.restrict_basicOpen_sV_eq, E.restrict_basicOpen_sV_eq]
    congr 1
    rw [map_mul, map_pow, hrl, map_mul, map_pow]
    linear_combination -e₁'
  -- Hence they agree after multiplication by a power of `sV (b l)`.
  obtain ⟨M, hM⟩ := exists_of_res_eq_of_qcqs_of_top (X := E.Wc.pt) h6
  -- Assemble the element of the fiber product.
  refine ⟨M + K + m₀, (E.b l ^ M * v₀, rl ^ (M + K) * y), ?_, ?_⟩
  · rw [E.mem_fiberProduct_iff]
    dsimp only
    rw [map_mul, map_pow, hM, ← hrl, ← map_pow, ← map_mul, ← mul_assoc, ← pow_add]
  · dsimp only
    rw [map_mul, map_pow]
    have hy' : ((E.WD.obj j).presheaf.map (homOfLE le_top).op) y =
        ((E.WD.obj j).presheaf.map (homOfLE le_top).op) rl ^ m₀ * z := hy
    rw [hy', pow_add, pow_add]
    ring

/-!
#### The category of stages

Following `lemma:nagata-valid-refinements-directed`, the stages form a nonempty cofiltered
category: any finitely generated subalgebra of the fiber product can be enlarged to satisfy
the generation condition (Stacks 01Z7), lifts of the generators exist at a common index by
the section-descent lemmas for the limit `W = lim Wⱼ`, and the covering and affineness
conditions descend from the limit by Stacks 01Z4.
-/

instance (j : Over E.i₀) : IsNoetherian (E.WD.obj j) := ⟨⟩

/-- (Implementation) The identity on the `V`-component times restriction on the section
component, as a morphism of `ℤ`-algebras. It maps the fiber product at `j` into the fiber
product at `j'`. -/
noncomputable def resAlgHom {j j' : Over E.i₀} (k : j' ⟶ j) :
    (Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)) →ₐ[ℤ] Γ(E.X, E.V) × Γ(E.WD.obj j', ⊤) :=
  ((RingHom.id Γ(E.X, E.V)).prodMap (E.res k).hom).toIntAlgHom

@[simp] lemma resAlgHom_apply {j j' : Over E.i₀} (k : j' ⟶ j)
    (p : Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)) :
    resAlgHom k p = (p.1, E.res k p.2) := rfl

lemma resAlgHom_mem_fiberProduct {j j' : Over E.i₀} (k : j' ⟶ j)
    {p : Γ(E.X, E.V) × Γ(E.WD.obj j, ⊤)} (hp : p ∈ E.fiberProduct j) :
    resAlgHom k p ∈ E.fiberProduct j' := by
  rw [E.mem_fiberProduct_iff] at hp ⊢
  rw [resAlgHom_apply, E.t_res]
  exact hp

lemma Stage.A_le_fiberProduct (T : E.Stage) : T.A ≤ E.fiberProduct T.j :=
  fun p hp ↦ (E.mem_fiberProduct_iff p).mpr (T.hA p hp)

variable (E)

/-- (Implementation) The data of a stage without its coefficient algebra: an index `j` and
lifts `r` of the generators of the intersection such that the basic opens of the `r l` form
an affine cover of `Wⱼ`. -/
structure PreStage where
  /-- The underlying index. -/
  j : Over E.i₀
  /-- The lifts of the generators of the intersection. -/
  r : Fin E.n → Γ(E.WD.obj j, ⊤)
  hr (l : Fin E.n) : E.t j (r l) = E.sV (E.b l)
  hcov : ⨆ l, (E.WD.obj j).basicOpen (r l) = ⊤
  haff (l : Fin E.n) : IsAffineOpen ((E.WD.obj j).basicOpen (r l))

variable {E}

/-- (Implementation) The pre-stage underlying a stage. -/
def Stage.toPreStage (T : E.Stage) : E.PreStage :=
  ⟨T.j, T.r, T.hr, T.hcov, T.haff⟩

/-- (Implementation) Pre-stages restrict along morphisms of indices. -/
noncomputable def PreStage.restrict (P : E.PreStage) {j' : Over E.i₀} (k : j' ⟶ P.j) :
    E.PreStage where
  j := j'
  r l := E.res k (P.r l)
  hr l := by rw [E.t_res, P.hr]
  hcov := by
    have h : ∀ l, (E.WD.obj j').basicOpen (E.res k (P.r l)) =
        E.WD.map k ⁻¹ᵁ ((E.WD.obj P.j).basicOpen (P.r l)) :=
      fun l ↦ (Scheme.preimage_basicOpen_top (E.WD.map k) (P.r l)).symm
    simp_rw [h, ← Scheme.Hom.preimage_iSup, P.hcov, Scheme.Hom.preimage_top]
  haff l := by
    rw [show (E.WD.obj j').basicOpen (E.res k (P.r l)) =
        E.WD.map k ⁻¹ᵁ ((E.WD.obj P.j).basicOpen (P.r l)) from
      (Scheme.preimage_basicOpen_top (E.WD.map k) (P.r l)).symm]
    exact (P.haff l).preimage _

/-- (Implementation, Stacks 01Z7) For every pre-stage and every generator index `l`, there
is a finite subset of the fiber product such that every subalgebra containing it and the
tautological pair `(b l, r l)` satisfies the generation condition of a stage at `l`: the
sections over the affine basic open `Wⱼ(r l)` form a finitely generated `ℤ`-algebra, and
every generator is, up to a power of `r l`, the section component of an element of the
fiber product. -/
lemma PreStage.exists_finset_hgen (P : E.PreStage) (l : Fin E.n) :
    ∃ s : Finset (Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤)),
      (∀ q ∈ s, q ∈ E.fiberProduct P.j) ∧
      ∀ A : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤)),
        (E.b l, P.r l) ∈ A → (∀ q ∈ s, q ∈ A) →
        ∀ z : Γ(E.WD.obj P.j, (E.WD.obj P.j).basicOpen (P.r l)),
          ∃ (m : ℕ) (p : Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤)), p ∈ A ∧
            ((E.WD.obj P.j).presheaf.map (homOfLE le_top).op).hom p.2 =
              z * ((E.WD.obj P.j).presheaf.map (homOfLE le_top).op).hom (P.r l) ^ m := by
  classical
  have hft : Algebra.FiniteType ℤ Γ(E.WD.obj P.j, (E.WD.obj P.j).basicOpen (P.r l)) :=
    IsAffineOpen.algebra_finiteType_of_locallyOfFiniteType
      (f := specULiftZIsTerminal.from (E.WD.obj P.j)) (P.haff l)
  obtain ⟨s₀, hs₀⟩ := hft.1
  choose m p hp₁ hp₂ using fun z : s₀ ↦
    E.exists_mem_fiberProduct_res_eq_mul_pow (P.hr l) (z : _)
  refine ⟨s₀.attach.image p, fun q hq ↦ ?_, ?_⟩
  · obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hq
    exact hp₁ z
  · intro A hbr hsub z
    set ρ := ((E.WD.obj P.j).presheaf.map
      (homOfLE (le_top : (E.WD.obj P.j).basicOpen (P.r l) ≤ ⊤)).op).hom with hρ
    let S : Subalgebra ℤ Γ(E.WD.obj P.j, (E.WD.obj P.j).basicOpen (P.r l)) :=
      { carrier := {z | ∃ (m : ℕ) (p : Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤)), p ∈ A ∧
          ρ p.2 = z * ρ (P.r l) ^ m}
        one_mem' := ⟨0, 1, one_mem A, by simp⟩
        zero_mem' := ⟨0, 0, zero_mem A, by simp⟩
        mul_mem' := by
          rintro z₁ z₂ ⟨m₁, p₁, h₁, e₁⟩ ⟨m₂, p₂, h₂, e₂⟩
          refine ⟨m₁ + m₂, p₁ * p₂, mul_mem h₁ h₂, ?_⟩
          change ρ (p₁.2 * p₂.2) = _
          rw [map_mul, e₁, e₂]
          ring
        add_mem' := by
          rintro z₁ z₂ ⟨m₁, p₁, h₁, e₁⟩ ⟨m₂, p₂, h₂, e₂⟩
          refine ⟨m₁ + m₂, p₁ * (E.b l, P.r l) ^ m₂ + p₂ * (E.b l, P.r l) ^ m₁,
            add_mem (mul_mem h₁ (pow_mem hbr m₂)) (mul_mem h₂ (pow_mem hbr m₁)), ?_⟩
          change ρ (p₁.2 * P.r l ^ m₂ + p₂.2 * P.r l ^ m₁) = _
          rw [map_add, map_mul, map_mul, map_pow, map_pow, e₁, e₂]
          ring
        algebraMap_mem' := fun c ↦ ⟨0, algebraMap ℤ _ c, A.algebraMap_mem c, by
          change ρ (algebraMap ℤ _ c) = _
          rw [pow_zero, mul_one]
          exact map_intCast ρ c⟩ }
    have hS : Algebra.adjoin ℤ (↑s₀ : Set _) ≤ S := by
      refine Algebra.adjoin_le fun z hz ↦ ?_
      exact ⟨m ⟨z, hz⟩, p ⟨z, hz⟩,
        hsub _ (Finset.mem_image.mpr ⟨⟨z, hz⟩, Finset.mem_attach _ _, rfl⟩), hp₂ ⟨z, hz⟩⟩
    have := hS (hs₀ ▸ Algebra.mem_top (R := ℤ) (x := z))
    exact this

/-- (Implementation, Stacks 01Z7) Enlarge a finitely generated subalgebra of the fiber
product containing the tautological pairs to the coefficient algebra of a stage over a
given pre-stage. -/
noncomputable def PreStage.mkStage (P : E.PreStage)
    (A₀ : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj P.j, ⊤)))
    (hA₀ : A₀ ≤ E.fiberProduct P.j) (hfg : A₀.FG)
    (hmem : ∀ l, (E.b l, P.r l) ∈ A₀) : E.Stage where
  j := P.j
  r := P.r
  hr := P.hr
  hcov := P.hcov
  haff := P.haff
  A := A₀ ⊔ Algebra.adjoin ℤ (⋃ l, ↑(P.exists_finset_hgen l).choose)
  hA p hp := by
    have h : A₀ ⊔ Algebra.adjoin ℤ (⋃ l, ↑(P.exists_finset_hgen l).choose) ≤
        E.fiberProduct P.j := by
      refine sup_le hA₀ (Algebra.adjoin_le fun q hq ↦ ?_)
      obtain ⟨l, hql⟩ := Set.mem_iUnion.mp hq
      exact (P.exists_finset_hgen l).choose_spec.1 q hql
    exact (E.mem_fiberProduct_iff p).mp (h hp)
  hAfg := hfg.sup (Subalgebra.fg_def.mpr
    ⟨_, Set.finite_iUnion fun l ↦ (P.exists_finset_hgen l).choose.finite_toSet, rfl⟩)
  hmem l := Algebra.mem_sup_left (hmem l)
  hgen l z :=
    (P.exists_finset_hgen l).choose_spec.2 _
      (Algebra.mem_sup_left (hmem l))
      (fun q hq ↦ Algebra.mem_sup_right
        (Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨l, hq⟩))) z

@[simp] lemma PreStage.mkStage_j (P : E.PreStage) (A₀) (hA₀) (hfg) (hmem) :
    (P.mkStage A₀ hA₀ hfg hmem).j = P.j := rfl

@[simp] lemma PreStage.mkStage_r (P : E.PreStage) (A₀) (hA₀) (hfg) (hmem) :
    (P.mkStage A₀ hA₀ hfg hmem).r = P.r := rfl

lemma PreStage.le_mkStage_A (P : E.PreStage) (A₀) (hA₀) (hfg) (hmem) :
    A₀ ≤ (P.mkStage A₀ hA₀ hfg hmem).A := le_sup_left

/-- (Implementation) The minimal stage over a pre-stage: adjoin the tautological pairs and
close up under the generation condition. -/
noncomputable def PreStage.stage (P : E.PreStage) : E.Stage :=
  P.mkStage (Algebra.adjoin ℤ (Set.range fun l ↦ (E.b l, P.r l)))
    (Algebra.adjoin_le (by rintro p ⟨l, rfl⟩; exact (E.mem_fiberProduct_iff _).mpr (P.hr l).symm))
    (Subalgebra.fg_def.mpr ⟨_, Set.finite_range _, rfl⟩)
    (fun l ↦ Algebra.subset_adjoin ⟨l, rfl⟩)

@[simp] lemma PreStage.stage_j (P : E.PreStage) : P.stage.j = P.j := rfl

/-- (Implementation) Restrict a stage along a morphism of indices, adjoining an extra
finitely generated subalgebra of the fiber product. -/
noncomputable def Stage.restrict (T : E.Stage) {j' : Over E.i₀} (k : j' ⟶ T.j)
    (A' : Subalgebra ℤ (Γ(E.X, E.V) × Γ(E.WD.obj j', ⊤)))
    (hA' : A' ≤ E.fiberProduct j') (hfg : A'.FG) : E.Stage :=
  (T.toPreStage.restrict k).mkStage (T.A.map (resAlgHom k) ⊔ A')
    (sup_le (by rintro p ⟨q, hq, rfl⟩; exact resAlgHom_mem_fiberProduct k (T.A_le_fiberProduct hq))
      hA')
    ((T.hAfg.map _).sup hfg)
    (fun l ↦ Algebra.mem_sup_left ⟨(E.b l, T.r l), T.hmem l, rfl⟩)

@[simp] lemma Stage.restrict_j (T : E.Stage) {j' : Over E.i₀} (k : j' ⟶ T.j)
    (A') (hA') (hfg) : (T.restrict k A' hA' hfg).j = j' := rfl

@[simp] lemma Stage.restrict_r (T : E.Stage) {j' : Over E.i₀} (k : j' ⟶ T.j)
    (A') (hA') (hfg) (l : Fin E.n) :
    (T.restrict k A' hA' hfg).r l = E.res k (T.r l) := rfl

lemma Stage.le_restrict_A (T : E.Stage) {j' : Over E.i₀} (k : j' ⟶ T.j)
    (A') (hA') (hfg) : A' ≤ (T.restrict k A' hA' hfg).A :=
  le_trans le_sup_right ((T.toPreStage.restrict k).le_mkStage_A _ _ _ _)

/-- (Implementation) The canonical morphism from a restricted stage. -/
noncomputable def Stage.restrictHom (T : E.Stage) {j' : Over E.i₀} (k : j' ⟶ T.j)
    (A') (hA') (hfg) : T.restrict k A' hA' hfg ⟶ T where
  base := k
  res_r _ := rfl
  map_mem p hp := (T.toPreStage.restrict k).le_mkStage_A _ _ _ _
    (Algebra.mem_sup_left ⟨p, hp, rfl⟩)

@[simp] lemma Stage.restrictHom_base (T : E.Stage) {j' : Over E.i₀} (k : j' ⟶ T.j)
    (A') (hA') (hfg) : (T.restrictHom k A' hA' hfg).base = k := rfl

end ExtensionData

end Scheme.NoetherianApproximation

end AlgebraicGeometry
