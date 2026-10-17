/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import WeilConjectures.AlgebraicGeometry.ProEtale.CohomologyFilteredColimit
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProfiniteCoefficientCohomology
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.ForgetModuleCohomology

/-!
# Cohomological dimension of the constant `ℓ`-adic sheaf

Let `S` be a quasi-compact quasi-separated scheme of finite type and of dimension at most `d`
over a separably closed field. Then the pro-étale cohomology `Hᵠ(S_proét, ℚ̄_ℓ)` of the constant
`ℓ`-adic sheaf `ℚ̄_ℓ,S = AlgebraicGeometry.ProEtale.adicConstantSheaf l S` (of locally finite
continuous functions to `ℚ̄_ℓ`) vanishes for `q > 2d`.

Indeed `ℚ̄_ℓ,S` is the filtered union of the subsheaves `U ↦ C(U, L)` of continuous functions
with values in the compact subgroups `L = V ∩ {‖x‖ ≤ ℓⁿ}`, for `V ⊆ ℚ̄_ℓ` a finite-dimensional
`ℚ_ℓ`-subspace: a locally finite function is, on an affine open, a continuous function with
compact image in a finite-dimensional subspace. Each `L` is profinite, the limit of the finite
discrete groups `L/(L ∩ {‖x‖ ≤ ℓ⁻ᵐ})`, so its cohomology vanishes above `2d`
(`AlgebraicGeometry.ProEtale.subsingleton_H_continuousSheaf_of_two_mul_lt_of_compact`), and
cohomology commutes with filtered colimits on a qcqs scheme
(`AlgebraicGeometry.Scheme.ProEt.subsingleton_H_of_isColimit_of_isFiltered`).

## Main statements

- `AlgebraicGeometry.ProEtale.subsingleton_H_adicConstantSheaf_of_two_mul_lt`:
  `Hᵠ(S_proét, ℚ̄_ℓ) = 0` for `q > 2d`, for the underlying abelian sheaf.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

section Lattice

/-- The compact subgroup `span_{ℚ_ℓ}(s) ∩ {‖x‖ ≤ ℓⁿ}` of `ℚ̄_ℓ`, for `k = (s, n)`. -/
noncomputable def adicLattice (k : Finset (PadicAlgCl l) × ℕ) : AddSubgroup (PadicAlgCl l) :=
  (Submodule.span ℚ_[l] (k.1 : Set (PadicAlgCl l))).toAddSubgroup ⊓
    (IsUltrametricDist.closedBall_openAddSubgroup (PadicAlgCl l)
      (r := (l : ℝ) ^ k.2) (by have := (Fact.out : l.Prime).pos; positivity)).toAddSubgroup

variable {l}

lemma mem_adicLattice {k : Finset (PadicAlgCl l) × ℕ} {x : PadicAlgCl l} :
    x ∈ adicLattice l k ↔
      x ∈ Submodule.span ℚ_[l] (k.1 : Set (PadicAlgCl l)) ∧ ‖x‖ ≤ (l : ℝ) ^ k.2 := by
  simp [adicLattice, IsUltrametricDist.closedBall_openAddSubgroup]

lemma one_le_l : (1 : ℝ) ≤ l := by
  exact_mod_cast (Fact.out : l.Prime).one_lt.le

lemma adicLattice_mono {k k' : Finset (PadicAlgCl l) × ℕ} (h : k ≤ k') :
    adicLattice l k ≤ adicLattice l k' := fun x hx ↦ by
  rw [mem_adicLattice] at hx ⊢
  exact ⟨Submodule.span_mono (Finset.coe_subset.2 h.1) hx.1,
    hx.2.trans (pow_le_pow_right₀ one_le_l h.2)⟩

instance (k : Finset (PadicAlgCl l) × ℕ) : CompactSpace (adicLattice l k) := by
  refine (isCompact_iff_compactSpace (s := (adicLattice l k : Set (PadicAlgCl l)))).mp ?_
  let V := Submodule.span ℚ_[l] (k.1 : Set (PadicAlgCl l))
  have : FiniteDimensional ℚ_[l] V := FiniteDimensional.span_finset _ _
  have : ProperSpace V := FiniteDimensional.proper ℚ_[l] V
  convert (isCompact_closedBall (0 : V) ((l : ℝ) ^ k.2)).image continuous_subtype_val using 1
  ext x
  simp only [SetLike.mem_coe, mem_adicLattice, Set.mem_image, Metric.mem_closedBall,
    dist_zero_right]
  exact ⟨fun h ↦ ⟨⟨x, h.1⟩, h.2, rfl⟩, by rintro ⟨y, hy, rfl⟩; exact ⟨y.2, hy⟩⟩

/-- The open subgroups `L ∩ {‖x‖ ≤ ℓ⁻ᵐ}` of the lattice `L`. -/
noncomputable def adicLatticeNbhd (k : Finset (PadicAlgCl l) × ℕ) (m : ℕ) :
    AddSubgroup (adicLattice l k) :=
  (IsUltrametricDist.closedBall_openAddSubgroup (PadicAlgCl l)
    (r := ((l : ℝ) ^ m)⁻¹) (by have := (Fact.out : l.Prime).pos; positivity)).toAddSubgroup.comap
      (adicLattice l k).subtype

lemma mem_adicLatticeNbhd {k : Finset (PadicAlgCl l) × ℕ} {m : ℕ} {x : adicLattice l k} :
    x ∈ adicLatticeNbhd k m ↔ ‖(x : PadicAlgCl l)‖ ≤ ((l : ℝ) ^ m)⁻¹ := by
  change (x : PadicAlgCl l) ∈ Metric.closedBall 0 _ ↔ _
  simp

lemma antitone_adicLatticeNbhd (k : Finset (PadicAlgCl l) × ℕ) :
    Antitone (adicLatticeNbhd k) := fun m m' h x hx ↦ by
  rw [mem_adicLatticeNbhd] at hx ⊢
  exact hx.trans (inv_anti₀ (by have := (Fact.out : l.Prime).pos; positivity)
    (pow_le_pow_right₀ one_le_l h))

lemma isOpen_adicLatticeNbhd (k : Finset (PadicAlgCl l) × ℕ) (m : ℕ) :
    IsOpen (adicLatticeNbhd k m : Set (adicLattice l k)) :=
  (IsUltrametricDist.closedBall_openAddSubgroup (PadicAlgCl l)
    (r := ((l : ℝ) ^ m)⁻¹) (by have := (Fact.out : l.Prime).pos; positivity)).isOpen.preimage
      continuous_subtype_val

lemma eq_zero_of_forall_mem_adicLatticeNbhd {k : Finset (PadicAlgCl l) × ℕ}
    (x : adicLattice l k) (hx : ∀ m, x ∈ adicLatticeNbhd k m) : x = 0 := by
  by_contra h
  have hpos : 0 < ‖(x : PadicAlgCl l)‖ :=
    norm_pos_iff.2 fun h' ↦ h (Subtype.ext h')
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos
    (inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt :
      (1 : ℝ) < l))
  have := mem_adicLatticeNbhd.1 (hx m)
  rw [inv_pow] at hm
  linarith

end Lattice
section DirectedUnion

variable {S : Scheme.{u}}

/-- **Filtered unions of subsheaves.** A cocone of a `u + 1`-small filtered diagram of abelian
pro-étale sheaves whose legs are monomorphisms is a colimit cocone as soon as every section of
the cocone point is locally in the image of some leg: the comparison map from the colimit is a
monomorphism since filtered colimits are exact, and an epimorphism since it is locally
surjective. -/
noncomputable def isColimitOfMonoOfLocallySurjective {K : Type (u + 1)} [SmallCategory K]
    [IsFiltered K] {D : K ⥤ Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}}
    (c : Cocone D) [∀ k, Mono (c.ι.app k)]
    (h : ∀ (V : S.ProEt) (s : c.pt.obj.obj (op V)), ∃ R ∈ Scheme.ProEt.topology S V,
      ∀ ⦃W : S.ProEt⦄ (g : W ⟶ V), R g →
        ∃ (k : K) (t : (D.obj k).obj.obj (op W)),
          (c.ι.app k).hom.app (op W) t = c.pt.obj.map g.op s) :
    IsColimit c := by
  have : IsConnected K := IsFiltered.isConnected _
  let φ := colimit.desc D c
  have hmono : Mono φ := by
    let α : D ⟶ (Functor.const _).obj c.pt := { app k := c.ι.app k }
    have : Mono α := NatTrans.mono_of_mono_app _
    have : Mono (colim.map α) := inferInstance
    let e := (colimit.isColimit ((Functor.const K).obj c.pt)).coconePointUniqueUpToIso
      (isColimitConstCocone K c.pt)
    have : φ = colim.map α ≫ e.hom := by
      refine colimit.hom_ext fun k ↦ ?_
      simp [φ, e, α]
    rw [this]
    infer_instance
  have hepi : Epi φ := by
    have : Sheaf.IsLocallySurjective φ := by
      refine ⟨fun {V} s ↦ ?_⟩
      obtain ⟨R, hR, hRs⟩ := h V s
      refine (Scheme.ProEt.topology S).superset_covering ?_ hR
      intro W g hg
      obtain ⟨k, t, ht⟩ := hRs g hg
      refine ⟨(colimit.ι D k).hom.app (op W) t, ?_⟩
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
        ← ObjectProperty.FullSubcategory.comp_hom, colimit.ι_desc]
      exact ht
    exact Sheaf.epi_of_isLocallySurjective _
  have : IsIso ((colimit.isColimit D).desc c) := isIso_of_mono_of_epi φ
  exact IsColimit.ofPointIso (colimit.isColimit D)

end DirectedUnion

section Diagram

variable (S : Scheme.{u})

/-- The index category of the lattices `adicLattice l k`, lifted to `Type (u + 1)`. -/
abbrev LatticeIndex := ULift.{u + 1} (Finset (PadicAlgCl l) × ℕ)

instance : IsDirected (LatticeIndex.{u} l) (· ≤ ·) := by
  classical exact
  ⟨fun a b ↦ ⟨⟨(a.down.1 ∪ b.down.1, max a.down.2 b.down.2)⟩,
    ⟨Finset.subset_union_left, le_max_left _ _⟩, ⟨Finset.subset_union_right, le_max_right _ _⟩⟩⟩

instance : IsFiltered (LatticeIndex.{u} l) := isFiltered_of_directed_le_nonempty _

variable {l} in
/-- The inclusion of lattices, as a continuous homomorphism. -/
noncomputable def adicLatticeInclusion {k k' : Finset (PadicAlgCl l) × ℕ} (h : k ≤ k') :
    ContinuousAddMonoidHom (adicLattice l k) (adicLattice l k') :=
  ⟨AddSubgroup.inclusion (adicLattice_mono h), continuous_subtype_val.subtype_mk _⟩

/-- The diagram of the sheaves `U ↦ C(U, L)` for the lattices `L = adicLattice l k`. -/
noncomputable def adicLatticeDiagram :
    LatticeIndex.{u} l ⥤ Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1} where
  obj k := continuousSheaf S (adicLattice l k.down)
  map {X Y} f := continuousSheafMap S (adicLatticeInclusion (by
    have h : X ≤ Y := leOfHom f
    exact h))
  map_id _ := by
    apply Sheaf.hom_ext
    ext U f
    rfl
  map_comp _ _ := by
    apply Sheaf.hom_ext
    ext U f
    rfl

/-- The underlying abelian sheaf of the constant `ℓ`-adic sheaf `ℚ̄_ℓ,S`. -/
noncomputable abbrev adicConstantSheafAb : Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1} :=
  (sheafForget₂ (ULift.{u + 1} (PadicAlgCl l)) S).obj (adicConstantSheaf l S)

variable {l S} in
/-- A continuous function with values in a lattice, as a section of `ℚ̄_ℓ,S`. -/
noncomputable def latticeFunctionToAdic (k : Finset (PadicAlgCl l) × ℕ) (U : S.ProEt) :
    ULift.{u + 1} C(U.left, adicLattice l k) →+ (adicConstantSheafAb l S).obj.obj (op U) where
  toFun f := ULift.up ⟨⟨fun t ↦ (f.down t : PadicAlgCl l), by fun_prop⟩,
    PadicAlgCl.mem_locallyFiniteFunctions_of_finiteDimensional <|
      have : FiniteDimensional ℚ_[l] (Submodule.span ℚ_[l] (k.1 : Set (PadicAlgCl l))) :=
        FiniteDimensional.span_finset _ _
      Submodule.finiteDimensional_of_le
        (S₂ := Submodule.span ℚ_[l] (k.1 : Set (PadicAlgCl l))) (Submodule.span_le.2 (by
        rintro _ ⟨t, rfl⟩
        exact (mem_adicLattice.1 (f.down t).2).1))⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The cocone of the inclusions `C(-, L) ⟶ ℚ̄_ℓ,S`. -/
noncomputable def adicLatticeCocone : Cocone (adicLatticeDiagram l S) where
  pt := adicConstantSheafAb l S
  ι :=
    { app k := ⟨{ app U := AddCommGrpCat.ofHom (latticeFunctionToAdic k.down U.unop)
                  naturality _ _ _ := rfl }⟩
      naturality k k' f := by
        apply Sheaf.hom_ext
        ext U f
        rfl }

instance (k : LatticeIndex.{u} l) : Mono ((adicLatticeCocone l S).ι.app k) := by
  have : Mono ((sheafToPresheaf _ _).map ((adicLatticeCocone l S).ι.app k)) := by
    rw [NatTrans.mono_iff_mono_app]
    intro U
    rw [AddCommGrpCat.mono_iff_injective]
    intro f g h
    exact ULift.ext _ _ (ContinuousMap.ext fun t ↦ Subtype.ext (congrArg
      (fun x : ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l U.unop.left) ↦ x.down.1 t) h))
  exact (sheafToPresheaf _ _).mono_of_mono_map this

/-- Every section of `ℚ̄_ℓ,S` is locally a continuous function with values in a lattice: on an
affine open neighbourhood of a point, a locally finite function has compact image in a
finite-dimensional subspace. -/
lemma exists_adicLattice_section (V : S.ProEt) (s : (adicConstantSheafAb l S).obj.obj (op V)) :
    ∃ R ∈ Scheme.ProEt.topology S V, ∀ ⦃W : S.ProEt⦄ (g : W ⟶ V), R g →
      ∃ (k : LatticeIndex.{u} l) (t : ((adicLatticeDiagram l S).obj k).obj.obj (op W)),
        ((adicLatticeCocone l S).ι.app k).hom.app (op W) t =
          (adicLatticeCocone l S).pt.obj.map g.op s := by
  let D := adicLatticeDiagram l S
  let c := adicLatticeCocone l S
  let R : Sieve V :=
    { arrows W g := ∃ (k : LatticeIndex.{u} l) (t : (D.obj k).obj.obj (op W)),
        (c.ι.app k).hom.app (op W) t = c.pt.obj.map g.op s
      downward_closed := by
        rintro W W' g ⟨k, t, ht⟩ h
        refine ⟨k, (D.obj k).obj.map h.op t, ?_⟩
        rw [NatTrans.naturality_apply, ht]
        change _ = c.pt.obj.map (g.op ≫ h.op) s
        rw [Functor.map_comp]
        rfl }
  refine ⟨R, ?_, fun W g hg ↦ hg⟩
  let f : C(V.left, PadicAlgCl l) := s.down.1
  have hf : f ∈ PadicAlgCl.locallyFiniteFunctions l V.left := s.down.2
  have key (x : V.left) : ∃ W : V.left.Opens, x ∈ W ∧ R (Scheme.ProEt.ofOpenImmersionHom V W.ι) := by
    obtain ⟨N, hN, hfin⟩ := hf x
    obtain ⟨_, ⟨W₀, hW, rfl⟩, hxW, hWN⟩ := V.left.isBasis_affineOpens.exists_subset_of_mem_open
      (mem_interior_iff_mem_nhds.2 hN) isOpen_interior
    let W : V.left.Opens := W₀
    obtain ⟨B, hB⟩ := (hW.isCompact.image f.continuous).isBounded.exists_norm_le
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B
      (by exact_mod_cast (Fact.out : l.Prime).one_lt : (1 : ℝ) < l)
    obtain ⟨s', hs'⟩ := Module.Finite.iff_fg.1 hfin
    have hmem (y : W.toScheme) : f (W.ι y) ∈ adicLattice l (s', n) := by
      rw [mem_adicLattice, hs']
      have hy : W.ι y ∈ (W : Set V.left) := by simp
      exact ⟨Submodule.subset_span ⟨_, interior_subset (hWN hy), rfl⟩,
        (hB _ ⟨_, hy, rfl⟩).trans hn.le⟩
    refine ⟨W, hxW, ⟨⟨(s', n)⟩, ULift.up ⟨fun y ↦ ⟨f (W.ι y), hmem y⟩,
      (f.continuous.comp W.ι.continuous).subtype_mk _⟩, ?_⟩⟩
    exact ULift.ext _ _ (Subtype.ext (ContinuousMap.ext fun y ↦ rfl))
  choose W hxW hR using key
  exact Scheme.ProEt.mem_topology_of_openImmersion R (fun x ↦ (W x).ι)
    (fun x ↦ ⟨x, ⟨x, hxW x⟩, Scheme.Opens.ι_apply _ _⟩) hR

/-- `ℚ̄_ℓ,S` is the filtered union of the subsheaves `U ↦ C(U, L)` of continuous functions with
values in the lattices `L = adicLattice l k`. -/
noncomputable def isColimitAdicLatticeCocone : IsColimit (adicLatticeCocone l S) :=
  isColimitOfMonoOfLocallySurjective _ (exists_adicLattice_section l S)

end Diagram

/-- **Cohomological dimension of the constant `ℓ`-adic sheaf.** Let `S` be a quasi-compact
quasi-separated scheme of finite type and of dimension at most `d` over a separably closed
field. Then `Hᵠ(S_proét, ℚ̄_ℓ) = 0` for `q > 2d`, for the underlying abelian sheaf of the
constant `ℓ`-adic sheaf. -/
theorem subsingleton_H_adicConstantSheaf_of_two_mul_lt {S : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] {K : Type u} [Field K] [IsSepClosed K] (a : S ⟶ Spec (.of K))
    [LocallyOfFiniteType a] [QuasiCompact a] (d : ℕ)
    (hS : topologicalKrullDim S ≤ (d : WithBot ℕ∞)) (q : ℕ) (hq : 2 * d < q) :
    Subsingleton (Sheaf.H (adicConstantSheafAb l S) q) :=
  Scheme.ProEt.subsingleton_H_of_isColimit_of_isFiltered S (isColimitAdicLatticeCocone l S) q
    fun k ↦ subsingleton_H_continuousSheaf_of_two_mul_lt_of_compact S
      (antitone_adicLatticeNbhd k.down) (isOpen_adicLatticeNbhd k.down)
      eq_zero_of_forall_mem_adicLatticeNbhd a d hS q hq

end AlgebraicGeometry.ProEtale
