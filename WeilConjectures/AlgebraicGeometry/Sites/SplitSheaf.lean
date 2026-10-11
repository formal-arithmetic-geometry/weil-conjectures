/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.GenericRestriction
public import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-!
# Sheaves on a field split by a Galois extension

Let `F` be a field and `L / F` a finite Galois extension. An abelian étale sheaf `N` on `Spec F`
is *split by* `L` (`AlgebraicGeometry.Scheme.IsSplitBy`) if it becomes constant over `Spec L`:
restriction from `Spec L` to every one-point étale scheme over `Spec L` is bijective.

Two morphisms from a one-point étale `F`-scheme to `Spec L` differ by an element of
`Gal(L / F)`, so the global sections of `N` are the Galois invariant sections over `Spec L`
(Galois descent). If `Gal(L / F)` is an `ℓ`-group and the sections of `N` over `Spec L` form a
finite `ℓ`-group, then the number of invariant sections is divisible by `ℓ`, so `N` has a global
section of order `ℓ`, that is a monomorphism `ℤ/ℓ ⟶ N`, whose cokernel is again split by `L`, with
fewer sections over `Spec L`. By induction `N` is filtered by constant sheaves `ℤ/ℓ`
(`AlgebraicGeometry.Scheme.IsSplitBy.induction`). This is the sheaf form of the Sylow reduction of
a finite `ℓ`-primary Galois module (blueprint `lem-sc-sylow-module-filtration`).

## Main statements

- `AlgebraicGeometry.Scheme.exists_map_eq_of_forall_map_etaleSpecMap_eq`: Galois descent of
  sections.
- `AlgebraicGeometry.Scheme.IsSplitBy.induction`: the filtration by constant sheaves `ℤ/ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

open GaloisCech

variable {F : Type u} [Field F]
  (N : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1})

/-- Restriction to a nonempty étale scheme over a one-point étale scheme over a field is
injective. -/
lemma injective_map_of_subsingleton {Z Z' : (Spec (.of F)).Etale} [Subsingleton Z.left]
    [Nonempty Z'.left] (g : Z' ⟶ Z) : Function.Injective (N.obj.map g.op) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  refine (isSheafFor_ofArrows N (fun _ : Unit ↦ g) ?_).isSeparatedFor.ext fun _ _ ⟨_⟩ ↦ ?_
  · refine Set.eq_univ_of_forall fun z ↦ Set.mem_iUnion.2 ⟨(), Classical.arbitrary _, ?_⟩
    exact Subsingleton.elim _ _
  · exact show N.obj.map g.op x = N.obj.map g.op 0 from hx.trans (map_zero _).symm

variable {N} (L : Type u) [Field L] [Algebra F L] [Algebra.Etale F L]

/-- **Two morphisms from a one-point scheme to `Spec L` differ by a Galois automorphism** when
`L / F` is normal. -/
lemma exists_eq_comp_etaleSpecMap [Normal F L] {Z : (Spec (.of F)).Etale} [Subsingleton Z.left]
    [Nonempty Z.left] (p q : Z ⟶ etaleSpec F L) :
    ∃ σ : L ≃ₐ[F] L, q = p ≫ etaleSpecMap σ.toAlgHom := by
  let := (isField_of_etale_of_subsingleton Z).toField
  let E := Γ(Z.left, ⊤)
  let : Algebra F E := (toRing Z.hom).toAlgebra
  have hp (r : Z ⟶ etaleSpec F L) : (toRing r.left).comp (algebraMap F L) = algebraMap F E := by
    exact (toRing_comp_specMap r.left (CommRingCat.ofHom (algebraMap F L))).symm.trans
      (congrArg toRing (MorphismProperty.Over.w r))
  let φ (r : Z ⟶ etaleSpec F L) : L →ₐ[F] E :=
    { toRingHom := toRing r.left
      commutes' x := congrArg (fun ψ : F →+* E ↦ ψ x) (hp r) }
  let : Algebra L E := (φ p).toRingHom.toAlgebra
  have : IsScalarTower F L E := IsScalarTower.of_algebraMap_eq fun x ↦ ((φ p).commutes x).symm
  let σ := (φ q).restrictNormal' L
  refine ⟨σ, ?_⟩
  refine MorphismProperty.Over.Hom.ext (eq_of_toRing_eq ?_)
  change toRing q.left = toRing (p.left ≫ Spec.map _)
  rw [toRing_comp_specMap]
  ext x
  exact ((φ q).restrictNormal_commutes L x).symm

variable {L}

section Points

variable (V : (Spec (.of F)).Etale)

instance : DiscreteTopology V.left := discreteTopology_of_etale_of_unique V

/-- The open point `{v}` of an étale scheme `V` over a field. -/
noncomputable def pointOpens (v : V.left) : V.left.Opens := ⟨{v}, isOpen_discrete _⟩

/-- The open point `{v}` of an étale scheme `V` over a field, as an étale scheme. -/
noncomputable abbrev pointObj (v : V.left) : (Spec (.of F)).Etale :=
  Etale.ofOpens V (pointOpens V v)

/-- The inclusion of the open point `{v}`. -/
noncomputable abbrev pointι (v : V.left) : pointObj V v ⟶ V :=
  Etale.ofOpensι V (pointOpens V v)

instance (v : V.left) : Subsingleton (pointObj V v).left :=
  inferInstanceAs (Subsingleton ({v} : Set V.left))

instance (v : V.left) : Nonempty (pointObj V v).left :=
  ⟨⟨v, rfl⟩⟩

lemma iUnion_range_pointι : ⋃ v, Set.range (pointι V v).left = Set.univ :=
  Set.eq_univ_of_forall fun v ↦ Set.mem_iUnion.2 ⟨v, ⟨⟨v, rfl⟩, rfl⟩⟩

variable {V} (N) in
/-- Sections over an étale scheme over a field are determined by their restrictions to the open
points. -/
lemma ext_of_pointι {x y : N.obj.obj (op V)}
    (h : ∀ v, N.obj.map (pointι V v).op x = N.obj.map (pointι V v).op y) : x = y :=
  (isSheafFor_ofArrows N (pointι V) (iUnion_range_pointι V)).isSeparatedFor.ext
    fun _ _ ⟨v⟩ ↦ h v

end Points

/-- **Galois descent, compatibility.** A section over `Spec L`, for `L / F` Galois, which is
invariant under `Gal(L / F)` has the same pullback along any two morphisms to `Spec L`. -/
lemma map_eq_map_of_forall_map_etaleSpecMap_eq [IsGalois F L]
    (x : N.obj.obj (op (etaleSpec F L)))
    (hx : ∀ σ : L ≃ₐ[F] L, N.obj.map (etaleSpecMap σ.toAlgHom).op x = x)
    {Z : (Spec (.of F)).Etale} (g₁ g₂ : Z ⟶ etaleSpec F L) :
    N.obj.map g₁.op x = N.obj.map g₂.op x := by
  refine ext_of_pointι N fun v ↦ ?_
  obtain ⟨σ, hσ⟩ := exists_eq_comp_etaleSpecMap L (pointι Z v ≫ g₁) (pointι Z v ≫ g₂)
  refine (FieldTrace.map_map_apply N.obj _ _ x).trans ?_
  rw [FieldTrace.map_map_apply N.obj (pointι Z v) g₂, hσ,
    ← FieldTrace.map_map_apply N.obj (pointι Z v ≫ g₁), hx]

variable (F) in
/-- The terminal object `Spec F` of the small étale site of `Spec F`. -/
noncomputable abbrev etaleTerminal : (Spec (.of F)).Etale :=
  MorphismProperty.Over.mk ⊤ (𝟙 (Spec (.of F)))
    (MorphismProperty.id_mem @AlgebraicGeometry.Etale (Spec (CommRingCat.of F)))

/-- The morphism `Spec L ⟶ Spec F` to the terminal object. -/
noncomputable abbrev etaleSpecToTerminal (L : Type u) [Field L] [Algebra F L]
    [Algebra.Etale F L] : etaleSpec F L ⟶ etaleTerminal F :=
  GaloisCech.isTerminal.from _

/-- **Galois descent.** A section over `Spec L`, for `L / F` Galois, which is invariant under
`Gal(L / F)` comes from a global section. -/
lemma exists_map_eq_of_forall_map_etaleSpecMap_eq [IsGalois F L]
    (x : N.obj.obj (op (etaleSpec F L)))
    (hx : ∀ σ : L ≃ₐ[F] L, N.obj.map (etaleSpecMap σ.toAlgHom).op x = x) :
    ∃ y, N.obj.map (etaleSpecToTerminal L).op y = x := by
  have hcov : Sieve.ofArrows _ (fun _ : Unit ↦ etaleSpecToTerminal (F := F) L) ∈
      (Spec (.of F)).smallEtaleTopology _ := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨(), (default : Spec (.of L)), @Subsingleton.elim (Spec (.of F)) _ _ _⟩
  have hsheaf : Presieve.IsSheafFor (N.obj ⋙ CategoryTheory.forget _)
      (Presieve.singleton (etaleSpecToTerminal (F := F) L)) := by
    have := (isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_comp_of_isSheaf _ N.obj (CategoryTheory.forget AddCommGrpCat) N.property)
    rw [← Presieve.ofArrows_pUnit.{0}, Presieve.isSheafFor_iff_generate]
    exact this _ hcov
  obtain ⟨y, hy, -⟩ := Presieve.isSheafFor_singleton.mp hsheaf x
    (fun g₁ g₂ _ ↦ map_eq_map_of_forall_map_etaleSpecMap_eq x hx g₁ g₂)
  exact ⟨y, hy⟩

section Constant

variable (B : AddCommGrpCat.{u + 1})

/-- Over a one-point étale scheme over a field, the sections of a constant sheaf are the constant
value. -/
lemma bijective_toSheafify_app_of_subsingleton (W : (Spec (.of F)).Etale)
    [Subsingleton W.left] [Nonempty W.left] :
    Function.Bijective ((CategoryTheory.toSheafify (Spec (.of F)).smallEtaleTopology
      ((Functor.const _).obj B)).app (op W)) := by
  have := isIso_constantSheafToPointFunctionSheaf (X := Spec (.of F)) (M := B)
    (fun V ↦ discreteTopology_of_etale_of_unique V)
  have hψ : Function.Bijective
      (((Spec (.of F)).constantSheafToPointFunctionSheaf B).hom.app (op W)) :=
    (ConcreteCategory.isIso_iff_bijective _).1 (inferInstanceAs (IsIso
      (((sheafToPresheaf _ _).map ((Spec (.of F)).constantSheafToPointFunctionSheaf B)).app
        (op W))))
  have hc : Function.Bijective (fun (m : B) (_ : W.left) ↦ m) :=
    ⟨fun m m' h ↦ congrFun h (Classical.arbitrary _),
      fun D ↦ ⟨D (Classical.arbitrary _), funext fun w ↦ congrArg D (Subsingleton.elim _ _)⟩⟩
  have h : (((Spec (.of F)).constantSheafToPointFunctionSheaf B).hom.app (op W)) ∘
      ((CategoryTheory.toSheafify (Spec (.of F)).smallEtaleTopology
        ((Functor.const _).obj B)).app (op W)) = fun (m : B) (_ : W.left) ↦ m :=
    funext fun m ↦ constantSheafToPointFunctionSheaf_app_toSheafify _ B W m
  rw [← h] at hc
  exact (Function.Bijective.of_comp_iff' hψ _).1 hc

end Constant

section Split

variable (N L)

/-- A sheaf `N` on `Spec F` *is split by* `L` if it becomes constant over `Spec L`: restriction
from `Spec L` to every one-point étale scheme over `Spec L` is bijective. -/
def IsSplitBy : Prop :=
  ∀ (Z : (Spec (.of F)).Etale) [Subsingleton Z.left] [Nonempty Z.left] (t : Z ⟶ etaleSpec F L),
    Function.Bijective (N.obj.map t.op)

variable {N L}

instance : Subsingleton (etaleTerminal F : (Spec (.of F)).Etale).left :=
  inferInstanceAs (Subsingleton (PrimeSpectrum F))

instance : Nonempty (etaleTerminal F : (Spec (.of F)).Etale).left :=
  inferInstanceAs (Nonempty (PrimeSpectrum F))

instance : Subsingleton (etaleSpec F L).left :=
  inferInstanceAs (Subsingleton (PrimeSpectrum L))

instance : Nonempty (etaleSpec F L).left :=
  inferInstanceAs (Nonempty (PrimeSpectrum L))

variable (ℓ : ℕ) {z : N.obj.obj (op (etaleTerminal F))} (hz : (ℓ : ℤ) • z = 0)

/-- The morphism `ℤ/ℓ → N(Spec F)` sending `1` to `z`. -/
noncomputable def zmodHom :
    AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)) ⟶ N.obj.obj (op (etaleTerminal F)) :=
  AddCommGrpCat.ofHom ((ZMod.lift ℓ ⟨zmultiplesHom _ z, by simpa using hz⟩).comp
    AddEquiv.ulift.toAddMonoidHom)

lemma zmodHom_apply (n : ℤ) : (zmodHom ℓ hz).hom (ULift.up (n : ZMod ℓ)) = n • z := by
  change ZMod.lift ℓ ⟨zmultiplesHom _ z, by simpa using hz⟩ (n : ZMod ℓ) = _
  rw [ZMod.lift_coe]
  rfl

lemma range_zmodHom : AddMonoidHom.range (zmodHom ℓ hz).hom = AddSubgroup.zmultiples z := by
  ext x
  constructor
  · rintro ⟨⟨c⟩, rfl⟩
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective c
    exact ⟨n, (zmodHom_apply ℓ hz n).symm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨⟨(n : ZMod ℓ)⟩, zmodHom_apply ℓ hz n⟩

lemma injective_zmodHom (hℓ : addOrderOf z = ℓ) : Function.Injective (zmodHom ℓ hz).hom := by
  refine (injective_iff_map_eq_zero _).2 fun ⟨c⟩ hc ↦ ?_
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective c
  have : n • z = 0 := (zmodHom_apply ℓ hz n).symm.trans hc
  have hd := addOrderOf_dvd_iff_zsmul_eq_zero.2 this
  rw [hℓ] at hd
  exact ULift.ext _ _ ((ZMod.intCast_zmod_eq_zero_iff_dvd n ℓ).2 hd)

/-- The morphism `ℤ/ℓ ⟶ N` of sheaves sending `1` to the global section `z`. -/
noncomputable def constantZModHom : (Spec (.of F)).constantZMod ℓ ⟶ N :=
  ((constantSheafAdj (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1}
    GaloisCech.isTerminal).homEquiv _ _).symm
    (zmodHom ℓ hz)

lemma constantZModHom_app_toSheafify (W : (Spec (.of F)).Etale) (b : ULift.{u + 1} (ZMod ℓ)) :
    (constantZModHom ℓ hz).hom.app (op W) ((CategoryTheory.toSheafify _
      ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))).app (op W) b) =
      N.obj.map (GaloisCech.isTerminal.from W).op (zmodHom ℓ hz b) := by
  have h := constantSheafAdj_homEquiv_apply (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1}
    GaloisCech.isTerminal
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))) N (constantZModHom ℓ hz)
  rw [constantZModHom, Equiv.apply_symm_apply] at h
  have h₁ := NatTrans.naturality_apply (CategoryTheory.toSheafify (Spec (.of F)).smallEtaleTopology
    ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))))
      (GaloisCech.isTerminal.from W).op b
  refine (congrArg _ h₁).trans ?_
  exact (NatTrans.naturality_apply (constantZModHom ℓ hz).hom _ _).trans
    (congrArg _ (ConcreteCategory.congr_hom h b).symm)


lemma exists_toSheafify_app_eq (W : (Spec (.of F)).Etale) [Subsingleton W.left]
    [Nonempty W.left] (c : ((Spec (.of F)).constantZMod ℓ).obj.obj (op W)) :
    ∃ b, (CategoryTheory.toSheafify _ ((Functor.const _).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))).app (op W) b = c :=
  (bijective_toSheafify_app_of_subsingleton _ W).2 c

/-- The morphism `ℤ/ℓ ⟶ N` attached to a global section of order `ℓ` is a monomorphism. -/
lemma mono_constantZModHom (hℓ : addOrderOf z = ℓ) : Mono (constantZModHom ℓ hz) := by
  have (V : (Spec (.of F)).Etaleᵒᵖ) : Mono ((constantZModHom ℓ hz).hom.app V) := by
    refine (AddCommGrpCat.mono_iff_injective _).2 ((injective_iff_map_eq_zero _).2 fun s hs ↦ ?_)
    refine ext_of_pointι _ fun v ↦ ?_
    obtain ⟨b, hb⟩ := exists_toSheafify_app_eq ℓ (pointObj V.unop v)
      (((Spec (.of F)).constantZMod ℓ).obj.map (pointι V.unop v).op s)
    have h := NatTrans.naturality_apply (constantZModHom ℓ hz).hom (pointι V.unop v).op s
    rw [hs, map_zero, ← hb, constantZModHom_app_toSheafify] at h
    have hb0 : b = 0 := injective_zmodHom ℓ hz hℓ
      ((injective_map_of_subsingleton N _ (h.trans (map_zero _).symm)).trans (map_zero _).symm)
    rw [map_zero, ← hb, hb0, map_zero]
  have : Mono (constantZModHom ℓ hz).hom := NatTrans.mono_of_mono_app _
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ _

/-- The constant sheaf `ℤ/ℓ` is split by every `L`. -/
lemma isSplitBy_constantZMod : IsSplitBy ((Spec (.of F)).constantZMod ℓ) L := by
  intro Z _ _ t
  have h := (bijective_toSheafify_app_of_subsingleton
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))) (etaleSpec F L))
  have h' := (bijective_toSheafify_app_of_subsingleton
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))) Z)
  have hc : (((Spec (.of F)).constantZMod ℓ).obj.map t.op) ∘ ((CategoryTheory.toSheafify _
      ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))).app
        (op (etaleSpec F L))) = ((CategoryTheory.toSheafify _
      ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))).app (op Z)) :=
    funext fun b ↦ (NatTrans.naturality_apply (CategoryTheory.toSheafify _
      ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))) t.op b).symm
  exact (Function.Bijective.of_comp_iff _ h).1 (hc ▸ h')

section Cokernel

variable {A : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1}} (f : A ⟶ N) [Mono f]

/-- Exactness of `A ⟶ N ⟶ coker f` on sections, for a monomorphism `f`. -/
lemma exists_app_eq_of_cokernel_π_app_eq_zero {W : (Spec (.of F)).Etale} (n : N.obj.obj (op W))
    (hn : (cokernel.π f).hom.app (op W) n = 0) : ∃ a, f.hom.app (op W) a = n := by
  obtain ⟨t, ht⟩ := Etale.exists_kernel_ι_app_eq (cokernel.π f) n hn
  have hl := Abelian.monoIsKernelOfCokernel _ (colimit.isColimit (parallelPair f 0))
  let k := hl.lift (KernelFork.ofι (kernel.ι (cokernel.π f)) (kernel.condition _))
  have hk : k ≫ f = kernel.ι (cokernel.π f) :=
    hl.fac (KernelFork.ofι (kernel.ι (cokernel.π f)) (kernel.condition _)) WalkingParallelPair.zero
  exact ⟨k.hom.app (op W) t, (ConcreteCategory.congr_hom
    (congrArg (fun φ ↦ φ.hom.app (op W)) hk) t).trans ht⟩

omit [Mono f] in
/-- Over a one-point scheme over `Spec L`, every section of `coker f` lifts to `N`, when `N` is
split by `L`. -/
lemma surjective_cokernel_π_app (hN : IsSplitBy N L) (W : (Spec (.of F)).Etale)
    [Subsingleton W.left] [Nonempty W.left] (t : W ⟶ etaleSpec F L) :
    Function.Surjective ((cokernel.π f).hom.app (op W)) := by
  intro q
  have : Sheaf.IsLocallySurjective (cokernel.π f) :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := cokernel.π f)).2 inferInstance
  obtain ⟨W', g, w', hg, -⟩ := exists_of_mem_smallEtaleTopology
    (Presheaf.imageSieve_mem (Spec (.of F)).smallEtaleTopology (cokernel.π f).hom q)
    (Classical.arbitrary W.left)
  let g'' := pointι W' w' ≫ g
  obtain ⟨n, hn⟩ := (Presheaf.imageSieve _ _).downward_closed hg (pointι W' w')
  obtain ⟨m, rfl⟩ := (hN _ (g'' ≫ t)).2 n
  refine ⟨N.obj.map t.op m, injective_map_of_subsingleton _ g'' ?_⟩
  rw [← NatTrans.naturality_apply, FieldTrace.map_map_apply]
  exact hn

/-- **The cokernel of a monomorphism of split sheaves is split.** -/
lemma isSplitBy_cokernel (hA : IsSplitBy A L) (hN : IsSplitBy N L) :
    IsSplitBy (cokernel f) L := by
  intro Z _ _ t
  have hsL := surjective_cokernel_π_app f hN (etaleSpec F L) (𝟙 _)
  refine ⟨(injective_iff_map_eq_zero _).2 fun q hq ↦ ?_, fun q ↦ ?_⟩
  · obtain ⟨m, rfl⟩ := hsL q
    rw [← NatTrans.naturality_apply] at hq
    obtain ⟨a, ha⟩ := exists_app_eq_of_cokernel_π_app_eq_zero f _ hq
    obtain ⟨a', rfl⟩ := (hA Z t).2 a
    rw [NatTrans.naturality_apply] at ha
    rw [← (hN Z t).1 ha]
    exact ConcreteCategory.congr_hom
      (congrArg (fun φ ↦ φ.hom.app (op (etaleSpec F L))) (cokernel.condition f)) a'
  · obtain ⟨n, rfl⟩ := surjective_cokernel_π_app f hN Z t q
    obtain ⟨m, rfl⟩ := (hN Z t).2 n
    exact ⟨_, (NatTrans.naturality_apply (cokernel.π f).hom t.op m).symm⟩

omit [Mono f] in
/-- Passing to the cokernel of a nonzero monomorphism of split sheaves decreases the size of
the sections over `Spec L`. -/
lemma card_cokernel_lt [Finite (N.obj.obj (op (etaleSpec F L)))] (hN : IsSplitBy N L)
    (a : A.obj.obj (op (etaleSpec F L))) (ha : f.hom.app _ a ≠ 0) :
    Nat.card ((cokernel f).obj.obj (op (etaleSpec F L))) <
      Nat.card (N.obj.obj (op (etaleSpec F L))) := by
  have hs := surjective_cokernel_π_app f hN (etaleSpec F L) (𝟙 _)
  have := Finite.of_surjective _ hs
  have := Fintype.ofFinite (N.obj.obj (op (etaleSpec F L)))
  have := Fintype.ofFinite ((cokernel f).obj.obj (op (etaleSpec F L)))
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  refine Fintype.card_lt_of_surjective_not_injective _ hs fun hi ↦ ha (hi ?_)
  rw [map_zero]
  exact ConcreteCategory.congr_hom
    (congrArg (fun φ ↦ φ.hom.app (op (etaleSpec F L))) (cokernel.condition f)) a

end Cokernel

variable (L) in
/-- A section vanishes if it vanishes on every one-point étale scheme admitting a morphism to
`Spec L`. -/
lemma eq_zero_of_forall_map_eq_zero {V : (Spec (.of F)).Etale} (s : N.obj.obj (op V))
    (h : ∀ (Z : (Spec (.of F)).Etale) [Subsingleton Z.left] [Nonempty Z.left] (g : Z ⟶ V),
      (Z ⟶ etaleSpec F L) → N.obj.map g.op s = 0) : s = 0 := by
    let c := FieldTrace.counitMor F L V
    let τ : (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale
        (FieldTrace.f F L))).obj ((FieldTrace.f F L).Etale.obj V) ⟶ etaleSpec F L :=
      MorphismProperty.Over.homMk (pullback.snd V.hom (FieldTrace.f F L)) rfl trivial
    have hc : ⋃ _ : Unit, Set.range c.left = Set.univ := by
      refine Set.eq_univ_of_forall fun v ↦ Set.mem_iUnion.2 ⟨(), ?_⟩
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := V.hom)
        (g := FieldTrace.f F L) v (Classical.arbitrary _)
        (Subsingleton.elim (α := Spec (.of F)) _ _)
      exact ⟨w, hw⟩
    refine (isSheafFor_ofArrows N (fun _ : Unit ↦ c) hc).isSeparatedFor.ext
      fun _ _ ⟨_⟩ ↦ show N.obj.map c.op s = N.obj.map c.op 0 from ?_
    rw [map_zero]
    refine ext_of_pointι N fun z ↦ ?_
    rw [map_zero, FieldTrace.map_map_apply]
    exact h _ _ (pointι _ z ≫ τ)

/-- A sheaf split by `L` with no sections over `Spec L` vanishes. -/
lemma isZero_of_isSplitBy (hN : IsSplitBy N L) (h : ∀ x : N.obj.obj (op (etaleSpec F L)), x = 0) :
    IsZero N := by
  rw [IsZero.iff_id_eq_zero]
  apply Sheaf.hom_ext
  ext V s
  refine eq_zero_of_forall_map_eq_zero L s fun Z _ _ g t ↦ ?_
  obtain ⟨m, hm⟩ := (hN _ t).2 (N.obj.map g.op s)
  rw [← hm, h m, map_zero]

/-- A sheaf split by `L` whose sections over `Spec L` are killed by `n` is killed by `n`. -/
lemma nsmul_id_eq_zero_of_isSplitBy (hN : IsSplitBy N L) (n : ℕ)
    (h : ∀ x : N.obj.obj (op (etaleSpec F L)), n • x = 0) : n • 𝟙 N = 0 := by
  apply Sheaf.hom_ext
  ext V s
  change n • s = 0
  refine eq_zero_of_forall_map_eq_zero L _ fun Z _ _ g t ↦ ?_
  obtain ⟨m, hm⟩ := (hN _ t).2 (N.obj.map g.op s)
  rw [map_nsmul, ← hm, ← map_nsmul, h m, map_zero]

section FixedPoints

variable [IsGalois F L] (ℓ : ℕ) [Fact ℓ.Prime]

/-- The action of `Gal(L / F)` on the sections over `Spec L`. -/
noncomputable abbrev galAction : MulAction (L ≃ₐ[F] L) (N.obj.obj (op (etaleSpec F L))) where
  smul σ x := N.obj.map (etaleSpecMap σ.toAlgHom).op x
  one_smul x := by
    change N.obj.map (etaleSpecMap (AlgHom.id F L)).op x = x
    rw [etaleSpecMap_id, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  mul_smul σ τ x := by
    change N.obj.map (etaleSpecMap (σ.toAlgHom.comp τ.toAlgHom)).op x = _
    rw [← etaleSpecMap_comp]
    exact (FieldTrace.map_map_apply N.obj _ _ x).symm

/-- **A nonzero global section of order `ℓ`.** If `Gal(L / F)` is an `ℓ`-group and `N` has
nonzero finite `ℓ`-primary sections over `Spec L`, then `N` has a global section of order `ℓ`:
the number of Galois invariant sections over `Spec L` is divisible by `ℓ`, so there is an
invariant section of order `ℓ`, which descends to `Spec F`. -/
lemma exists_addOrderOf_eq (hP : IsPGroup ℓ (L ≃ₐ[F] L))
    [Finite (N.obj.obj (op (etaleSpec F L)))]
    (hN : ∀ x : N.obj.obj (op (etaleSpec F L)), ∃ k : ℕ, ℓ ^ k • x = 0)
    (x₀ : N.obj.obj (op (etaleSpec F L))) (hx₀ : x₀ ≠ 0) :
    ∃ z : N.obj.obj (op (etaleTerminal F)), addOrderOf z = ℓ := by
  let := galAction (N := N) (L := L)
  let S : AddSubgroup (N.obj.obj (op (etaleSpec F L))) :=
    { carrier := MulAction.fixedPoints (L ≃ₐ[F] L) _
      add_mem' {a b} ha hb σ := by
        change N.obj.map _ (a + b) = a + b
        rw [map_add]
        exact congrArg₂ (· + ·) (ha σ) (hb σ)
      zero_mem' σ := map_zero _
      neg_mem' {a} ha σ := by
        change N.obj.map _ (-a) = -a
        rw [map_neg]
        exact congrArg _ (ha σ) }
  have := Fact.out (p := ℓ.Prime)
  -- `ℓ` divides the number of sections over `Spec L`
  have h₁ : ℓ ∣ Nat.card (N.obj.obj (op (etaleSpec F L))) := by
    obtain ⟨k, hk⟩ := hN x₀
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow this).1 (addOrderOf_dvd_of_nsmul_eq_zero hk)
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hx₀ (AddMonoid.addOrderOf_eq_one_iff.1 (hj'.trans (pow_zero _)))
    exact (dvd_pow_self ℓ hj0).trans (hj' ▸ addOrderOf_dvd_natCard x₀)
  have h₂ : ℓ ∣ Nat.card S := by
    have := hP.card_modEq_card_fixedPoints (N.obj.obj (op (etaleSpec F L)))
    exact (Nat.modEq_zero_iff_dvd.1 (this.symm.trans (Nat.modEq_zero_iff_dvd.2 h₁)))
  obtain ⟨⟨y, hy⟩, hyℓ⟩ := exists_prime_addOrderOf_dvd_card' ℓ h₂
  obtain ⟨z, rfl⟩ := exists_map_eq_of_forall_map_etaleSpecMap_eq y fun σ ↦ hy σ
  refine ⟨z, ?_⟩
  rw [← hyℓ, AddSubgroup.addOrderOf_mk]
  exact (addOrderOf_injective (N.obj.map (etaleSpecToTerminal L).op).hom
    (injective_map_of_subsingleton N _) z).symm


/-- **Filtration of a split `ℓ`-primary sheaf by constant sheaves `ℤ/ℓ`.** Let `L / F` be a
finite Galois extension whose Galois group is an `ℓ`-group. A property of sheaves on `Spec F`
which holds for the zero sheaf, and passes from the cokernel of a monomorphism `ℤ/ℓ ⟶ N` to `N`,
holds for every sheaf split by `L` with finite `ℓ`-primary sections over `Spec L`: by induction on
the number of these sections, using a global section of order `ℓ`
(`AlgebraicGeometry.Scheme.exists_addOrderOf_eq`). -/
theorem IsSplitBy.induction (hP : IsPGroup ℓ (L ≃ₐ[F] L))
    (P : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1} → Prop)
    (h₀ : ∀ N, IsZero N → P N)
    (h₁ : ∀ (N : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (z : N.obj.obj (op (etaleTerminal F))) (hz : (ℓ : ℤ) • z = 0), addOrderOf z = ℓ →
        P (cokernel (constantZModHom ℓ hz)) → P N)
    (hN : IsSplitBy N L) [Finite (N.obj.obj (op (etaleSpec F L)))]
    (hNℓ : ∀ x : N.obj.obj (op (etaleSpec F L)), ∃ k : ℕ, ℓ ^ k • x = 0) : P N := by
  suffices H : ∀ n (N : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1}),
      IsSplitBy N L → Finite (N.obj.obj (op (etaleSpec F L))) →
        (∀ x : N.obj.obj (op (etaleSpec F L)), ∃ k : ℕ, ℓ ^ k • x = 0) →
          Nat.card (N.obj.obj (op (etaleSpec F L))) = n → P N from
    H _ N hN inferInstance hNℓ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N hN _ hNℓ hcard
  by_cases hall : ∀ x : N.obj.obj (op (etaleSpec F L)), x = 0
  · exact h₀ N (isZero_of_isSplitBy hN hall)
  push Not at hall
  obtain ⟨x₀, hx₀⟩ := hall
  obtain ⟨z, hz⟩ := exists_addOrderOf_eq ℓ hP hNℓ x₀ hx₀
  have hzℓ : (ℓ : ℤ) • z = 0 := by
    rw [natCast_zsmul, ← hz]
    exact addOrderOf_nsmul_eq_zero z
  have := mono_constantZModHom ℓ hzℓ hz
  let ι := constantZModHom ℓ hzℓ
  have hs := surjective_cokernel_π_app ι hN (etaleSpec F L) (𝟙 _)
  have : Finite ((cokernel ι).obj.obj (op (etaleSpec F L))) := Finite.of_surjective _ hs
  refine h₁ N z hzℓ hz (ih _ ?_ _ (isSplitBy_cokernel ι (isSplitBy_constantZMod ℓ) hN)
    inferInstance (fun x ↦ ?_) rfl)
  · rw [← hcard]
    refine card_cokernel_lt ι hN ((CategoryTheory.toSheafify _ ((Functor.const _).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))).app _ (ULift.up ((1 : ℤ) : ZMod ℓ))) ?_
    change (constantZModHom ℓ hzℓ).hom.app _ _ ≠ 0
    rw [constantZModHom_app_toSheafify, zmodHom_apply, one_zsmul]
    intro h0
    have := (injective_map_of_subsingleton N (GaloisCech.isTerminal.from (etaleSpec F L)))
      (h0.trans (map_zero _).symm)
    rw [this, addOrderOf_zero] at hz
    exact (Fact.out (p := ℓ.Prime)).one_lt.ne hz
  · obtain ⟨m, rfl⟩ := hs x
    obtain ⟨k, hk⟩ := hNℓ m
    exact ⟨k, by rw [← map_nsmul, hk, map_zero]⟩

end FixedPoints

section Restriction

variable {F' : Type u} [Field F'] [Algebra F F'] [Algebra.Etale F F'] [Algebra F' L]
  [IsScalarTower F F' L] [Algebra.Etale F' L]

variable (F' L) in
/-- `Spec L` over `Spec F'`, viewed over `Spec F`, is `Spec L` over `Spec F`. -/
noncomputable def overMapEtaleSpecIso :
    (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale (FieldTrace.f F F'))).obj
      (etaleSpec F' L) ≅ etaleSpec F L :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])

lemma bijective_map_overMapEtaleSpecIso_inv :
    Function.Bijective (N.obj.map (overMapEtaleSpecIso L F').inv.op) :=
  ConcreteCategory.bijective_of_isIso _

/-- **Restriction of a split sheaf.** If `N` is split by `L`, so is its restriction to an
intermediate field `F'`. -/
lemma IsSplitBy.res (hN : IsSplitBy N L) : IsSplitBy (FieldTrace.res F F' N) L := by
  intro Z _ _ t
  have : Subsingleton ((MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale
      (FieldTrace.f F F'))).obj Z).left := ‹Subsingleton Z.left›
  have : Nonempty ((MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale
      (FieldTrace.f F F'))).obj Z).left := ‹Nonempty Z.left›
  let t' := (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale
    (FieldTrace.f F F'))).map t ≫ (overMapEtaleSpecIso L F').hom
  have h : ⇑((FieldTrace.res F F' N).obj.map t.op) =
      ⇑(N.obj.map t'.op) ∘ ⇑(N.obj.map (overMapEtaleSpecIso L F').inv.op) := by
    funext x
    refine Eq.trans ?_ (FieldTrace.map_map_apply N.obj _ _ x).symm
    simp [t']
    rfl
  exact h ▸ (hN _ t').comp bijective_map_overMapEtaleSpecIso_inv

end Restriction

end Split

end AlgebraicGeometry.Scheme
