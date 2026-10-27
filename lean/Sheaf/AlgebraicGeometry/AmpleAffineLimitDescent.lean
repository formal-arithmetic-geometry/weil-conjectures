/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q113
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.FinitePresentationAffineLimitDescent
import WeilConjectures.AlgebraicGeometry.AmpleFiniteAffineCover
import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.Modules.HomSection

/-!
# Descent of ampleness along affine inverse limits

Source: Stacks Project, Limits, Tag 09MT, lemma-limit-ample, in Situation 01YX
(situation-descent) (blueprint: lem-trf-ample-affine-limit-descent).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

private noncomputable def mapOpen {X : Scheme.{u}} {M N : X.Modules}
    (a : M ⟶ N) : X.Opens :=
  (Hom.zeroLocus a).support.compl

private theorem mapOpen_iso {X : Scheme.{u}} {M N M' N' : X.Modules}
    (a : M ⟶ N) (b : M' ⟶ N') (e : Arrow.mk a ≅ Arrow.mk b) :
    mapOpen a = mapOpen b := by
  unfold mapOpen
  rw [Hom.zeroLocus_eq_of_arrowIso a b e]

private theorem mapOpen_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} [M.IsInvertible] [N.IsInvertible] (a : M ⟶ N) :
    mapOpen ((tensorPullback f).map a) = f ⁻¹ᵁ mapOpen a := by
  have := IsInvertible.sheafOfModules_isInvertible M
  have := IsInvertible.sheafOfModules_isInvertible N
  let e := (nonempty_tensorPullbackAdjunction f).some.leftAdjointUniq
    (pullbackPushforwardAdjunction f)
  have hz : (Hom.zeroLocus a).comap f = Hom.zeroLocus ((tensorPullback f).map a) := by
    rw [Hom.comap_zeroLocus]
    exact Hom.zeroLocus_eq_of_arrowIso _ _
      (Arrow.isoMk (e.app M).symm (e.app N).symm (by
        change e.inv.app M ≫ (tensorPullback f).map a =
          (Scheme.Modules.pullback f).map a ≫ e.inv.app N
        exact (e.inv.naturality a).symm))
  unfold mapOpen
  rw [← hz, Scheme.IdealSheafData.support_comap]
  rfl

private theorem finitePresentation_of_invertible {X : Scheme.{u}}
    (M : X.Modules) [M.IsInvertible] : M.IsFinitePresentation := by
  have := IsInvertible.sheafOfModules_isInvertible M
  have := SheafOfModules.IsInvertible.isFiniteLocallyFree M
  infer_instance

private theorem isCompact_mapOpen {X : Scheme.{u}} [CompactSpace X]
    {M N : X.Modules} [M.IsInvertible] [N.IsInvertible] (a : M ⟶ N) :
    IsCompact (mapOpen a : Set X) := by
  classical
  have := IsInvertible.sheafOfModules_isInvertible M
  have := IsInvertible.sheafOfModules_isInvertible N
  have hlocal (x : X) : ∃ V : X.affineOpens, x ∈ V.1 ∧
      ∃ b : Γ(X, V.1), X.basicOpen b = V.1 ⊓ mapOpen a := by
    obtain ⟨V, hx, _, ⟨s, hs⟩, t, ht⟩ :=
      exists_isFreeGenerator₂ M N (TopologicalSpace.Opens.mem_top x)
    obtain ⟨b, hb⟩ := ht.exists_smul_eq (a.app V.1 s)
    refine ⟨V, hx, b, ?_⟩
    ext y
    have hz (hy : y ∈ V.1) : y ∈ (Hom.zeroLocus a).support ↔
        y ∉ X.basicOpen b := by
      rw [Scheme.IdealSheafData.mem_support_iff_of_mem hy,
        Hom.ideal_zeroLocus a V hs ht hb.symm, Scheme.zeroLocus_span,
        Scheme.mem_zeroLocus_iff]
      simp
    constructor
    · intro hy
      have hyV := X.basicOpen_le b hy
      exact ⟨hyV, fun h ↦ (hz hyV).mp h hy⟩
    · rintro ⟨hyV, hy⟩
      by_contra h
      exact hy ((hz hyV).mpr h)
  choose V hx b hb using hlocal
  obtain ⟨s, hcover⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ ((V x).1 : Set X)) (fun x ↦ (V x).1.isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
  have heq : (mapOpen a : Set X) = ⋃ x ∈ s, (X.basicOpen (b x) : Set X) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hxs, hyV⟩ := Set.mem_iUnion₂.mp (hcover (Set.mem_univ y))
      exact Set.mem_iUnion₂.mpr ⟨x, hxs, by rw [hb]; exact ⟨hyV, hy⟩⟩
    · intro hy
      obtain ⟨x, _, hy⟩ := Set.mem_iUnion₂.mp hy
      rw [hb] at hy
      exact hy.2
  rw [heq]
  exact s.finite_toSet.isCompact_biUnion (fun x _ ↦ ((V x).2.basicOpen (b x)).isCompact)

private noncomputable def powIso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) :
    ∀ n : ℕ, M.tensorPow n ≅ N.tensorPow n
  | 0 => Iso.refl _
  | n + 1 => e ⊗ᵢ powIso e n

private noncomputable def unitIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (tensorPullback f).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules :=
  ((nonempty_tensorPullbackAdjunction f).some.leftAdjointUniq
    (pullbackPushforwardAdjunction f)).app _ ≪≫ pullbackObjUnitIso f

private noncomputable def powerIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Y.Modules) (n : ℕ) :
    (tensorPullback f).obj (L.tensorPow n) ≅ ((tensorPullback f).obj L).tensorPow n :=
  let e := (nonempty_tensorPullbackAdjunction f).some.leftAdjointUniq
    (pullbackPushforwardAdjunction f)
  e.app _ ≪≫ (nonempty_pullback_tensorPow_iso f L n).some ≪≫ powIso (e.app L).symm n

private theorem exists_mapOpen_of_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Y.Modules) [L.IsInvertible] (n : ℕ)
    (s : Γ(((tensorPullback f).obj L).tensorPow n, ⊤)) :
    ∃ a : (tensorPullback f).obj (𝟙_ Y.Modules) ⟶
        (tensorPullback f).obj (L.tensorPow n),
      (mapOpen a : Set X) = nonvanishingLocus (((tensorPullback f).obj L).tensorPow n) s := by
  have := ((invertible_pullback_tensor f).1 L).2
  let b := homOfGlobalSection (((tensorPullback f).obj L).tensorPow n) s
  let a := (unitIso f).hom ≫ b ≫ (powerIso f L n).inv
  refine ⟨a, ?_⟩
  have he : mapOpen a = mapOpen b := mapOpen_iso a b
    (Arrow.isoMk (unitIso f) (powerIso f L n) (by simp [a]))
  rw [he, nonvanishingLocus_eq_compl_support_zeroLocus]
  rfl

private theorem exists_section_of_mapOpen {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Y.Modules) [L.IsInvertible] (n : ℕ)
    (a : (tensorPullback f).obj (𝟙_ Y.Modules) ⟶
      (tensorPullback f).obj (L.tensorPow n)) :
    ∃ s : Γ(((tensorPullback f).obj L).tensorPow n, ⊤),
      (mapOpen a : Set X) = nonvanishingLocus (((tensorPullback f).obj L).tensorPow n) s := by
  have := ((invertible_pullback_tensor f).1 L).2
  let b := (unitIso f).inv ≫ a ≫ (powerIso f L n).hom
  let s := b.app ⊤ (1 : Γ(X, ⊤))
  have hb : homOfGlobalSection _ s = b := by
    apply unit_hom_ext
    simp only [homOfGlobalSection_app_one]
    rw [presheaf_map_id_apply]
    rfl
  refine ⟨s, ?_⟩
  have he : mapOpen a = mapOpen b := mapOpen_iso a b
    (Arrow.isoMk (unitIso f) (powerIso f L n) (by simp [b]))
  rw [he, nonvanishingLocus_eq_compl_support_zeroLocus, hb]
  rfl

private theorem exists_affine_mapOpen {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] [Nonempty I] (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {M N : (D.obj (op i)).Modules} [M.IsInvertible] [N.IsInvertible]
    (a : M ⟶ N) (ha : IsAffineOpen (c.π.app (op i) ⁻¹ᵁ mapOpen a)) :
    ∃ (j : I) (hij : i ≤ j),
      IsAffineOpen (D.map (homOfLE hij).op ⁻¹ᵁ mapOpen a) := by
  let U := mapOpen a
  have hU : IsCompact (U : Set (D.obj (op i))) := isCompact_mapOpen a
  have (j : Over (op i)) : CompactSpace ((opensDiagram D (op i) U).obj j) :=
    isCompact_iff_compactSpace.mp
      (QuasiCompact.isCompact_preimage _ U.isOpen hU)
  have (j : Over (op i)) :
      QuasiSeparatedSpace ((opensDiagram D (op i) U).obj j) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map j.hom ⁻¹ᵁ U).isOpen).mp
      (.of_quasiSeparatedSpace _)
  have : IsAffine (opensCone D c (op i) U).pt := ha
  obtain ⟨j, hj⟩ := Scheme.exists_isAffine_of_isLimit
    (opensDiagram D (op i) U) (opensCone D c (op i) U)
    (isLimitOpensCone D c hc (op i) U)
  exact ⟨j.left.unop, leOfHom j.hom.unop, hj⟩

private theorem mapOpen_conjugate {X : Scheme.{u}} {M N M' N' : X.Modules}
    (a : M ⟶ N) (e : M' ≅ M) (f : N' ≅ N) :
    mapOpen (e.hom ≫ a ≫ f.inv) = mapOpen a := by
  exact mapOpen_iso _ _ (Arrow.isoMk e f (by simp))

private theorem mapOpen_limit_descent {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) {i j : I} (hij : i ≤ j)
    (M N : (D.obj (op i)).Modules) [M.IsInvertible] [N.IsInvertible]
    (a : (tensorPullback (c.π.app (op i))).obj M ⟶
      (tensorPullback (c.π.app (op i))).obj N)
    (b : (tensorPullback (D.map (homOfLE hij).op)).obj M ⟶
      (tensorPullback (D.map (homOfLE hij).op)).obj N)
    (h : (affineLimitTensorPullbackComparison D c hij M).inv ≫
        (tensorPullback (c.π.app (op j))).map b ≫
        (affineLimitTensorPullbackComparison D c hij N).hom = a) :
    c.π.app (op j) ⁻¹ᵁ mapOpen b = mapOpen a := by
  have := ((invertible_pullback_tensor (D.map (homOfLE hij).op)).1 M).2
  have := ((invertible_pullback_tensor (D.map (homOfLE hij).op)).1 N).2
  rw [← mapOpen_pullback, ← h]
  exact (mapOpen_conjugate _
    (affineLimitTensorPullbackComparison D c hij M).symm
    (affineLimitTensorPullbackComparison D c hij N).symm).symm

private theorem exists_mapOpen_stage {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) {i j k : I} (hij : i ≤ j) (hjk : j ≤ k)
    (L : (D.obj (op i)).Modules) [L.IsInvertible] (n : ℕ)
    (a : (tensorPullback (D.map (homOfLE hij).op)).obj (𝟙_ (D.obj (op i)).Modules) ⟶
      (tensorPullback (D.map (homOfLE hij).op)).obj (L.tensorPow n)) :
    ∃ b : (tensorPullback (D.map (homOfLE (hij.trans hjk)).op)).obj
        (𝟙_ (D.obj (op i)).Modules) ⟶
      (tensorPullback (D.map (homOfLE (hij.trans hjk)).op)).obj (L.tensorPow n),
      mapOpen b = D.map (homOfLE hjk).op ⁻¹ᵁ mapOpen a := by
  let f := D.map (homOfLE hjk).op
  let g := D.map (homOfLE hij).op
  let q := D.map (homOfLE (hij.trans hjk)).op
  have w : f ≫ g = q := by rw [← D.map_comp]; rfl
  let E := (nonempty_tensorPullbackComp f g).some
  let e (M : (D.obj (op i)).Modules) : (tensorPullback q).obj M ≅
      (tensorPullback f).obj ((tensorPullback g).obj M) :=
    eqToIso (congrArg (fun h ↦ (tensorPullback h).obj M) w.symm) ≪≫ E.app M
  refine ⟨(e _).hom ≫ (tensorPullback f).map a ≫ (e _).inv, ?_⟩
  rw [mapOpen_conjugate]
  have := ((invertible_pullback_tensor g).1 (𝟙_ (D.obj (op i)).Modules)).2
  have := ((invertible_pullback_tensor g).1 (L.tensorPow n)).2
  exact mapOpen_pullback f a

/-- Ampleness of the pullback of an invertible module along an affine inverse limit
descends to one stage of the inverse system.
(blueprint: lem-trf-ample-affine-limit-descent)

Source: Stacks Project, Limits, Tag 09MT, lemma-limit-ample, in Situation 01YX.

Proof:
1. Choose finitely many affine nonvanishing opens of positive tensor powers on the
   ample limit. Regard their sections as maps from the structure module to the powers.
2. Invertible modules are finitely presented. Descend these maps by the morphism
   clause of `finitePresentation_descent_affineLimit`. The complement of their zero
   schemes commutes with tensor pullback and is unchanged by isomorphisms of arrows.
3. Each descended nonvanishing open is quasi-compact: on a finite affine
   trivializing cover it is a principal open. Apply `Scheme.exists_isAffine_of_isLimit`
   to its restricted inverse system to make it affine after increasing the index.
4. Choose a common upper bound for these finitely many stages and the initial index.
   The affine transitions preserve affineness. The union of the resulting opens pulls
   back to the whole limit; `exists_map_eq_top` makes this union the whole of a later stage.
5. Convert the descended maps back to sections of the corresponding tensor powers.
   Their affine nonvanishing opens cover the quasi-compact stage, proving ampleness.

The index type lies in the schemes' universe, implementing the small directed
system in the node and in the affine-transition descent lemmas.
-/
theorem exists_stage_isAmple_of_limit_isAmple
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (c : Cone D) (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj (op i))]
    [∀ i : I, QuasiSeparatedSpace (D.obj (op i))]
    (haff : ∀ {i j : I} (h : i ≤ j), IsAffineHom (D.map (homOfLE h).op))
    (i₀ : I) (L₀ : (D.obj (op i₀)).Modules) [L₀.IsInvertible]
    (hL : ∃ h : ((tensorPullback (c.π.app (op i₀))).obj L₀).IsInvertible,
      @IsAmple c.pt ((tensorPullback (c.π.app (op i₀))).obj L₀) h)
    : ∃ (j : I) (hij : i₀ ≤ j),
      ∃ h : ((tensorPullback (D.map (homOfLE hij).op)).obj L₀).IsInvertible,
        @IsAmple (D.obj (op j)) ((tensorPullback (D.map (homOfLE hij).op)).obj L₀) h := by
  classical
  have (i : Iᵒᵖ) : CompactSpace (D.obj i) := inferInstanceAs
    (CompactSpace (D.obj (op i.unop)))
  have (i : Iᵒᵖ) : QuasiSeparatedSpace (D.obj i) := inferInstanceAs
    (QuasiSeparatedSpace (D.obj (op i.unop)))
  have {i j : Iᵒᵖ} (f : i ⟶ j) : IsAffineHom (D.map f) :=
    haff (leOfHom f.unop)
  obtain ⟨hInv, hample⟩ := hL
  have := hInv
  obtain ⟨m, n, s, U, hn, hU, hmem, hcover⟩ :=
    IsAmple.exists_finite_affine_cover c.pt _ hample
  have hdesc (t : Fin m) : ∃ (j : I) (hij : i₀ ≤ j)
      (a : (tensorPullback (D.map (homOfLE hij).op)).obj
          (𝟙_ (D.obj (op i₀)).Modules) ⟶
        (tensorPullback (D.map (homOfLE hij).op)).obj (L₀.tensorPow (n t))),
      IsAffineOpen (mapOpen a) ∧ c.π.app (op j) ⁻¹ᵁ mapOpen a = U t := by
    obtain ⟨a, ha⟩ := exists_mapOpen_of_section (c.π.app (op i₀)) L₀ (n t) (s t)
    obtain ⟨j, hij, b, hb⟩ := (finitePresentation_descent_affineLimit D c hc).2.1
      i₀ _ _ (finitePresentation_of_invertible _) (finitePresentation_of_invertible _) a
    have hp : c.π.app (op j) ⁻¹ᵁ mapOpen b = U t := by
      rw [mapOpen_limit_descent D c hij _ _ a b hb]
      apply SetLike.coe_injective
      exact ha.trans (Set.ext fun x ↦ (hmem t x).symm)
    have := ((invertible_pullback_tensor (D.map (homOfLE hij).op)).1
      (𝟙_ (D.obj (op i₀)).Modules)).2
    have := ((invertible_pullback_tensor (D.map (homOfLE hij).op)).1
      (L₀.tensorPow (n t))).2
    obtain ⟨k, hjk, hk⟩ := exists_affine_mapOpen D c hc j b (by rw [hp]; exact hU t)
    obtain ⟨b', hb'⟩ := exists_mapOpen_stage D hij hjk L₀ (n t) b
    refine ⟨k, hij.trans hjk, b', ?_, ?_⟩
    · rw [hb']; exact hk
    · rw [hb', ← Scheme.Hom.comp_preimage, c.w, hp]
  choose j hij a hAffine hpre using hdesc
  obtain ⟨k, hk⟩ := (insert i₀ (Finset.univ.image j)).exists_le
  have hik : i₀ ≤ k := hk _ (Finset.mem_insert_self ..)
  have hjk (t : Fin m) : j t ≤ k := hk _
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩))
  obtain ⟨b, hb⟩ := Classical.axiomOfChoice
    (fun t ↦ exists_mapOpen_stage D (hij t) (hjk t) L₀ (n t) (a t))
  have hbAffine (t : Fin m) : IsAffineOpen (mapOpen (b t)) := by
    rw [hb t]
    exact (hAffine t).preimage _
  have hbpre (t : Fin m) : c.π.app (op k) ⁻¹ᵁ mapOpen (b t) = U t := by
    rw [hb t, ← Scheme.Hom.comp_preimage, c.w, hpre t]
  have htop : c.π.app (op k) ⁻¹ᵁ (⨆ t, mapOpen (b t)) = ⊤ := by
    rw [Scheme.Hom.preimage_iSup]
    simp_rw [hbpre]
    apply top_unique
    intro x _
    obtain ⟨t, ht⟩ := hcover x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t, ht⟩
  obtain ⟨l, f, hf⟩ := exists_map_eq_top D c hc (⨆ t, mapOpen (b t)) htop
  let hkl : k ≤ l.unop := leOfHom f.unop
  obtain ⟨d, hd⟩ := Classical.axiomOfChoice
    (fun t ↦ exists_mapOpen_stage D hik hkl L₀ (n t) (b t))
  have hdAffine (t : Fin m) : IsAffineOpen (mapOpen (d t)) := by
    rw [hd t]
    exact (hbAffine t).preimage _
  have hdtop : (⨆ t, mapOpen (d t)) = ⊤ := by
    simp_rw [hd]
    rw [← Scheme.Hom.preimage_iSup]
    exact hf
  have hInv' := ((invertible_pullback_tensor
    (D.map (homOfLE (hik.trans hkl)).op)).1 L₀).2
  have := hInv'
  refine ⟨l.unop, hik.trans hkl, hInv', inferInstance, ?_⟩
  intro x
  have hx : x ∈ ⨆ t, mapOpen (d t) := by rw [hdtop]; trivial
  obtain ⟨t, ht⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨s', hs'⟩ := exists_section_of_mapOpen
    (D.map (homOfLE (hik.trans hkl)).op) L₀ (n t) (d t)
  refine ⟨n t, hn t, s', mapOpen (d t), ht, hdAffine t, ?_⟩
  intro y
  exact Set.ext_iff.mp hs' y

end AlgebraicGeometry
