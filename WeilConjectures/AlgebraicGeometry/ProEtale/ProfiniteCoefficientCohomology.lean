/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Topology.Algebra.Group.Quotient
public import WeilConjectures.AlgebraicGeometry.ProEtale.CohomologyTowerLimit
public import WeilConjectures.AlgebraicGeometry.ProEtale.FiniteCoefficientCohomology

/-!
# Pro-étale cohomology with profinite coefficients

Let `L` be a compact Hausdorff topological abelian group with a decreasing sequence of open
subgroups `Uₘ` with trivial intersection, e.g. a lattice `ℤ_ℓⁿ` with `Uₘ = ℓᵐ ℤ_ℓⁿ`. The sheaf
`U ↦ C(U, L)` on `S_proét` is the limit of the tower of the sheaves `U ↦ C(U, L/Uₘ)` of
continuous functions to the finite discrete groups `L/Uₘ`, whose transition maps are
epimorphisms. By repleteness of the pro-étale topos
(`AlgebraicGeometry.Scheme.ProEt.subsingleton_H_of_isLimit_tower`), the vanishing of
`Hᵠ(S_proét, L/Uₘ)` for `q > 2d`
(`AlgebraicGeometry.ProEtale.subsingleton_H_continuousSheaf_of_two_mul_lt`)
passes to `L`: the transition maps are surjective on `H^{2d}`, the kernels `Uₘ/Uₘ₊₁` having
no `H^{2d+1}`.

## Main statements

- `AlgebraicGeometry.ProEtale.epi_continuousSheafMap`: a surjection onto a discrete group
  induces an epimorphism of sheaves of continuous functions.
- `AlgebraicGeometry.ProEtale.surjective_H_map_continuousSheafMap`: right exactness of the top
  cohomology for such a surjection with finite discrete kernel.
- `AlgebraicGeometry.ProEtale.subsingleton_H_continuousSheaf_of_two_mul_lt_of_compact`:
  `Hᵠ(S_proét, L) = 0` for `q > 2d`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (S : Scheme.{u})

section Exact

variable {A B : Type} [TopologicalSpace A] [AddCommGroup A] [IsTopologicalAddGroup A]
  [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B]

/-- A surjective continuous homomorphism onto a discrete group induces an epimorphism of
pro-étale sheaves of continuous functions: a continuous function to the discrete group is
constant on the open fibres, which form a Zariski cover, and constants lift. -/
lemma epi_continuousSheafMap [DiscreteTopology B] (φ : ContinuousAddMonoidHom A B)
    (hφ : Function.Surjective φ) : Epi (continuousSheafMap S φ) := by
  have : Presheaf.IsLocallySurjective (ProEt.topology S) (continuousSheafMap S φ).hom := by
    refine ⟨fun {U} s₀ ↦ ?_⟩
    let s : C(U.left, B) := s₀.down
    choose a ha using hφ
    refine ProEt.mem_topology_of_openImmersion _
      (fun x : U.left ↦ (U.left.fiberOpens s (s x)).ι)
      (fun x ↦ ⟨x, ⟨x, rfl⟩, Scheme.Opens.ι_apply _ _⟩)
      fun x ↦ ⟨ULift.up (ContinuousMap.const _ (a (s x))), ?_⟩
    exact congrArg ULift.up (ContinuousMap.ext fun y ↦ (ha (s x)).trans y.2.symm)
  exact (Sheaf.isLocallySurjective_iff_epi' _ _).1 this

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- A short complex of abelian sheaves which is left exact on sections and whose second map is
an epimorphism of sheaves is short exact. -/
lemma shortExact_of_sections (T : ShortComplex (Sheaf J AddCommGrpCat.{u + 1}))
    (hf : ∀ U, Function.Injective (T.f.hom.app U))
    (hex : ∀ U y, T.g.hom.app U y = 0 → ∃ x, T.f.hom.app U x = y) [Epi T.g] :
    T.ShortExact := by
  let P := T.map (sheafToPresheaf J AddCommGrpCat.{u + 1})
  have hP : P.Exact := by
    rw [ShortComplex.exact_iff_evaluation]
    intro U
    rw [ShortComplex.ab_exact_iff]
    exact hex U
  have hT : T.Exact := ShortComplex.exact_of_iso
    (ShortComplex.mapNatIso T (sheafificationNatIso J _)).symm
    (hP.map (presheafToSheaf J AddCommGrpCat.{u + 1}))
  have : Mono T.f := by
    have : Mono ((sheafToPresheaf J AddCommGrpCat.{u + 1}).map T.f) := by
      rw [NatTrans.mono_iff_mono_app]
      intro U
      exact (AddCommGrpCat.mono_iff_injective _).2 (hf U)
    exact (sheafToPresheaf J _).mono_of_mono_map this
  exact ShortComplex.ShortExact.mk' hT inferInstance inferInstance

variable [DiscreteTopology B]

/-- The inclusion of the kernel of a continuous homomorphism, as a continuous homomorphism. -/
def kerSubtype (φ : ContinuousAddMonoidHom A B) :
    ContinuousAddMonoidHom (φ.toAddMonoidHom.ker) A :=
  ⟨φ.toAddMonoidHom.ker.subtype, continuous_subtype_val⟩

/-- The short exact sequence `0 ⟶ C(-, ker φ) ⟶ C(-, A) ⟶ C(-, B) ⟶ 0` of pro-étale sheaves of a
surjection `φ : A ⟶ B` of discrete groups. -/
lemma shortExact_continuousSheafMap (φ : ContinuousAddMonoidHom A B)
    (hφ : Function.Surjective φ) :
    (ShortComplex.mk (continuousSheafMap S (kerSubtype φ)) (continuousSheafMap S φ) (by
      apply Sheaf.hom_ext
      ext U f
      let f' : C(U.unop.left, φ.toAddMonoidHom.ker) := f.down
      exact ULift.ext _ _ (ContinuousMap.ext fun t ↦ (f' t).2))).ShortExact := by
  have := epi_continuousSheafMap S φ hφ
  refine shortExact_of_sections _ (fun U x y h ↦ ?_) (fun U y hy ↦ ?_)
  · exact ULift.ext _ _ (ContinuousMap.ext fun t ↦ Subtype.ext
      (congrArg (fun f : ULift.{u + 1} C(U.unop.left, A) ↦ f.down t) h))
  · let y' : C(U.unop.left, A) := y.down
    have hy' (t : U.unop.left) : φ (y' t) = 0 :=
      congrArg (fun f : ULift.{u + 1} C(U.unop.left, B) ↦ f.down t) hy
    exact ⟨ULift.up ⟨fun t ↦ ⟨y' t, hy' t⟩, by fun_prop⟩, rfl⟩

/-- **Right exactness of the top cohomology.** For a surjection `φ : A ⟶ B` of discrete
groups whose kernel has no cohomology in degree `N + 1`, the map
`H^N(S_proét, A) ⟶ H^N(S_proét, B)` is surjective. -/
lemma surjective_H_map_continuousSheafMap (φ : ContinuousAddMonoidHom A B)
    (hφ : Function.Surjective φ) (N : ℕ)
    (h : Subsingleton (Sheaf.H (continuousSheaf S φ.toAddMonoidHom.ker) (N + 1))) :
    Function.Surjective (Sheaf.H.map (continuousSheafMap S φ) N) := fun y ↦
  ((Sheaf.H.exact_map_δSucc (shortExact_continuousSheafMap S φ hφ) N) y).1
    (Subsingleton.elim _ _)

end Exact
section Profinite

variable {L : Type} [TopologicalSpace L] [AddCommGroup L] [IsTopologicalAddGroup L]
  (U : ℕ → AddSubgroup L)

/-- The projection `L ⟶ L/Uₘ`, as a continuous homomorphism. -/
def quotientMk (m : ℕ) : ContinuousAddMonoidHom L (L ⧸ U m) :=
  ⟨QuotientAddGroup.mk' (U m), continuous_quot_mk⟩

variable {U} in
/-- The transition map `L/Uₘ₊₁ ⟶ L/Uₘ`, as a continuous homomorphism. -/
def quotientTransition (hU : Antitone U) (m : ℕ) :
    ContinuousAddMonoidHom (L ⧸ U (m + 1)) (L ⧸ U m) :=
  ⟨QuotientAddGroup.map _ _ (AddMonoidHom.id L) (hU m.le_succ),
    (QuotientAddGroup.isQuotientMap_mk (U (m + 1))).continuous_iff.2 continuous_quot_mk⟩

omit [IsTopologicalAddGroup L] in
lemma quotientTransition_mk (hU : Antitone U) (m : ℕ) (x : L) :
    quotientTransition hU m (x : L ⧸ U (m + 1)) = (x : L ⧸ U m) :=
  rfl

omit [IsTopologicalAddGroup L] in
lemma surjective_quotientTransition (hU : Antitone U) (m : ℕ) :
    Function.Surjective (quotientTransition hU m) := by
  rintro ⟨x⟩
  exact ⟨(x : L ⧸ U (m + 1)), rfl⟩

variable [CompactSpace L] {U} (hU : Antitone U) (hopen : ∀ m, IsOpen (U m : Set L))
  (hbot : ∀ x : L, (∀ m, x ∈ U m) → x = 0)

include hU hopen hbot in
/-- In a compact group, a decreasing sequence of open subgroups with trivial intersection is
a basis of neighbourhoods of `0`. -/
lemma exists_subset_of_mem_nhds_zero {V : Set L} (hV : V ∈ nhds (0 : L)) :
    ∃ m, (U m : Set L) ⊆ V := by
  by_contra! h
  let t (m : ℕ) : Set L := (U m : Set L) ∩ (interior V)ᶜ
  have hcl (m : ℕ) : IsClosed (t m) :=
    (AddSubgroup.isClosed_of_isOpen _ (hopen m)).inter isOpen_interior.isClosed_compl
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t
    (fun m ↦ Set.inter_subset_inter_left _ (hU m.le_succ))
    (fun m ↦ by
      obtain ⟨y, hyU, hyV⟩ := Set.not_subset.1 (h m)
      exact ⟨y, hyU, fun hy ↦ hyV (interior_subset hy)⟩)
    (hcl 0).isCompact hcl
  have hx' := Set.mem_iInter.1 hx
  obtain rfl := hbot x fun m ↦ (hx' m).1
  exact (hx' 0).2 (mem_interior_iff_mem_nhds.2 hV)

include hU hopen hbot in
/-- A compatible family of elements of the quotients `L/Uₘ` comes from a unique element of
`L`. -/
lemma existsUnique_of_compatible (f : ∀ m, L ⧸ U m)
    (hf : ∀ m, quotientTransition hU m (f (m + 1)) = f m) :
    ∃! x : L, ∀ m, (x : L ⧸ U m) = f m := by
  have hdisc (m : ℕ) : DiscreteTopology (L ⧸ U m) := QuotientAddGroup.discreteTopology (hopen m)
  refine existsUnique_of_exists_of_unique ?_ fun x y hx hy ↦ ?_
  · let t (m : ℕ) : Set L := (QuotientAddGroup.mk : L → L ⧸ U m) ⁻¹' {f m}
    have hcl (m : ℕ) : IsClosed (t m) := by
      have := hdisc m
      exact (isClosed_discrete ({f m} : Set (L ⧸ U m))).preimage
        (QuotientAddGroup.continuous_mk (N := U m))
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t
      (fun m y hy ↦ by
        change (y : L ⧸ U m) = f m
        rw [← quotientTransition_mk U hU m y, ← hf m]
        exact congrArg _ hy)
      (fun m ↦ (QuotientAddGroup.mk_surjective (f m)).imp fun _ h ↦ h)
      (hcl 0).isCompact hcl
    exact ⟨x, fun m ↦ Set.mem_iInter.1 hx m⟩
  · have h := hbot (-x + y) fun m ↦ QuotientAddGroup.eq.1 ((hx m).trans (hy m).symm)
    rw [neg_add_eq_zero] at h
    exact h

include hU hopen hbot in
/-- **Continuous maps to `L = lim L/Uₘ`.** A compatible family of continuous maps `X ⟶ L/Uₘ`
comes from a unique continuous map `X ⟶ L`. -/
lemma existsUnique_continuousMap_of_compatible {X : Type*} [TopologicalSpace X]
    (f : ∀ m, C(X, L ⧸ U m)) (hf : ∀ m t, quotientTransition hU m (f (m + 1) t) = f m t) :
    ∃! g : C(X, L), ∀ m t, (g t : L ⧸ U m) = f m t := by
  have hdisc (m : ℕ) : DiscreteTopology (L ⧸ U m) := QuotientAddGroup.discreteTopology (hopen m)
  choose g hg hgu using fun t ↦
    existsUnique_of_compatible hU hopen hbot (fun m ↦ f m t) (fun m ↦ hf m t)
  refine ⟨⟨g, continuous_iff_continuousAt.2 fun t W hW ↦ ?_⟩, fun m t ↦ hg t m,
    fun g' hg' ↦ ContinuousMap.ext fun t ↦ hgu t (g' t) fun m ↦ hg' m t⟩
  have hV : (fun z ↦ g t + z) ⁻¹' W ∈ nhds (0 : L) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hW)
  obtain ⟨m, hm⟩ := exists_subset_of_mem_nhds_zero hU hopen hbot hV
  have hO : (f m) ⁻¹' {f m t} ∈ nhds t :=
    ((isOpen_discrete _).preimage (f m).continuous).mem_nhds rfl
  refine Filter.mem_map.2 (Filter.mem_of_superset hO fun z hz ↦ ?_)
  have hz' : (g t : L ⧸ U m) = g z := (hg t m).trans ((Set.mem_singleton_iff.1 hz).symm.trans
    (hg z m).symm)
  have := hm (QuotientAddGroup.eq.1 hz')
  simpa using this

variable (U) in
/-- The tower of sheaves `U ↦ C(U, L/Uₘ)` on `S_proét`. -/
noncomputable def continuousSheafTower : ℕᵒᵖ ⥤ Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1} :=
  Functor.ofOpSequence (X := fun m ↦ continuousSheaf S (L ⧸ U m))
    fun m ↦ continuousSheafMap S (quotientTransition hU m)

variable (U) in
/-- The cone `C(-, L) ⟶ C(-, L/Uₘ)` over the tower of the sheaves `U ↦ C(U, L/Uₘ)`. -/
noncomputable def continuousSheafTowerCone : Cone (continuousSheafTower S U hU) where
  pt := continuousSheaf S L
  π := NatTrans.ofOpSequence (fun m ↦ continuousSheafMap S (quotientMk U m)) fun m ↦ by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
      continuousSheafTower, Functor.ofOpSequence_map_homOfLE_succ]
    rw [← continuousSheafMap_comp]
    rfl

include hopen hbot in
/-- The sheaf `U ↦ C(U, L)` is the limit of the tower of the sheaves `U ↦ C(U, L/Uₘ)`. -/
noncomputable def isLimitContinuousSheafTowerCone :
    IsLimit (continuousSheafTowerCone S U hU) := by
  refine isLimitOfReflects (sheafToPresheaf _ _)
    (evaluationJointlyReflectsLimits _ fun V ↦ ?_)
  refine isLimitOfReflects (forget AddCommGrpCat.{u + 1})
    (Classical.choice ((Types.isLimit_iff _).2 fun s hs ↦ ?_))
  let fm (m : ℕ) : C(V.unop.left, L ⧸ U m) := (s (op m)).down
  have hfm (m : ℕ) (t : V.unop.left) : quotientTransition hU m (fm (m + 1) t) = fm m t := by
    have h := hs (homOfLE m.le_succ).op
    simp only [continuousSheafTower, Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ]
      at h
    exact congrArg (fun x : ULift.{u + 1} C(V.unop.left, L ⧸ U m) ↦ x.down t) h
  obtain ⟨g, hg, hgu⟩ := existsUnique_continuousMap_of_compatible hU hopen hbot fm hfm
  refine ⟨ULift.up g, fun j ↦ ?_, fun x hx ↦ ?_⟩
  · exact ULift.ext _ _ (ContinuousMap.ext fun t ↦ hg j.unop t)
  · exact ULift.ext _ _ (hgu x.down fun m t ↦
      congrArg (fun y : ULift.{u + 1} C(V.unop.left, L ⧸ U m) ↦ y.down t) (hx (op m)))

end Profinite

end AlgebraicGeometry.ProEtale
