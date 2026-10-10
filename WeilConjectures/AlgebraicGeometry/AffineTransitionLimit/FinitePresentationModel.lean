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
public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.Existence
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
# Finite presentation models of morphisms of finite type

A morphism of finite type `f : X ⟶ S` of quasi-compact quasi-separated schemes factors as an
immersion into a scheme of finite presentation over `S`
(`AlgebraicGeometry.Scheme.Hom.exists_isImmersion_locallyOfFinitePresentation`, Stacks Project
Tag 01ZE).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section FinitePresentationModel

/-!
## Immersing a finite type scheme into a scheme of finite presentation

Let `S` be a quasi-compact quasi-separated scheme and let `f : X ⟶ S` be a morphism locally of
finite type with `X` quasi-compact and quasi-separated. Then `X` immerses over `S` into a
scheme of finite presentation over `S`, see
`AlgebraicGeometry.Scheme.Hom.exists_isImmersion_locallyOfFinitePresentation` (Stacks Project
Tag 01ZE).

The model is built from an absolute Noetherian approximation `X = lim Xⱼ` of `X` itself
(`AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`): the model is `Xₖ ×_ℤ S` for a
suitable stage `k`, and the comparison morphism is `(πₖ, f)`. Since `Xₖ` is of finite type over
the Noetherian ring `ℤ`, the model is of finite presentation over `S`. The stage `k` has to be
chosen large enough for the comparison morphism to be an immersion: this needs finitely many
algebra generators of the charts of `X` over the charts of `S` to be defined at the stage `k`.
-/

set_option backward.defeqAttrib.useBackward true

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}

/-- A section over the preimage of an affine open `U` of a stage `D.obj i` comes from a
section over the preimage of `U` at some stage `D.obj j`. -/
lemma exists_appLE_π_app_eq [IsCofiltered I]
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] (hc : IsLimit c) (i : I)
    {U : (D.obj i).Opens} (hU : IsAffineOpen U) (s : Γ(c.pt, c.π.app i ⁻¹ᵁ U)) :
    ∃ (j : I) (g : j ⟶ i) (t : Γ(D.obj j, D.map g ⁻¹ᵁ U)),
      ∀ e : c.π.app i ⁻¹ᵁ U ≤ c.π.app j ⁻¹ᵁ (D.map g ⁻¹ᵁ U),
        (c.π.app j).appLE (D.map g ⁻¹ᵁ U) (c.π.app i ⁻¹ᵁ U) e t = s := by
  have haff : ∀ j : Over i, IsAffine ((opensDiagram D i U).obj j) :=
    fun j ↦ hU.preimage (D.map j.hom)
  obtain ⟨j, t, ht⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit (opensDiagram D i U)
    (opensCone D c i U) (isLimitOpensCone D c hc i U) ((c.π.app i ⁻¹ᵁ U).topIso.inv s)
  refine ⟨j.left, j.hom, (D.map j.hom ⁻¹ᵁ U).topIso.hom t, fun e ↦ ?_⟩
  rw [opensCone_π_app, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top] at ht
  have h2 := congrArg (c.π.app i ⁻¹ᵁ U).topIso.hom ht
  simp only [CommRingCat.comp_apply] at h2
  simpa [← CommRingCat.comp_apply] using h2

/-- Finitely many sections, each over the preimage of an affine open of a fixed stage
`D.obj i`, all descend to a common stage. -/
lemma exists_hom_forall_mem_range_appLE [IsCofiltered I]
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] (hc : IsLimit c) (i : I)
    {σ : Type*} [Finite σ] {U : σ → (D.obj i).Opens} (hU : ∀ a, IsAffineOpen (U a))
    (s : ∀ a, Γ(c.pt, c.π.app i ⁻¹ᵁ U a)) :
    ∃ (k : I) (g : k ⟶ i), ∀ (a : σ)
      (e : c.π.app i ⁻¹ᵁ U a ≤ c.π.app k ⁻¹ᵁ (D.map g ⁻¹ᵁ U a)),
      s a ∈ Set.range ((c.π.app k).appLE (D.map g ⁻¹ᵁ U a) (c.π.app i ⁻¹ᵁ U a) e) := by
  classical
  cases nonempty_fintype σ
  have hc' : IsLimit (c.whisker (Over.forget i)) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
  have haff : ∀ {j k : Over i} (g : j ⟶ k),
      IsAffineHom ((Over.forget i ⋙ D).map g) := fun g ↦ by dsimp; infer_instance
  have hA : ∀ a, ∃ (j : Over i) (g : j ⟶ Over.mk (𝟙 i))
      (t : Γ((Over.forget i ⋙ D).obj j, (Over.forget i ⋙ D).map g ⁻¹ᵁ U a)),
      ∀ e : (c.whisker (Over.forget i)).π.app (Over.mk (𝟙 i)) ⁻¹ᵁ U a ≤
        (c.whisker (Over.forget i)).π.app j ⁻¹ᵁ ((Over.forget i ⋙ D).map g ⁻¹ᵁ U a),
        ((c.whisker (Over.forget i)).π.app j).appLE ((Over.forget i ⋙ D).map g ⁻¹ᵁ U a)
          ((c.whisker (Over.forget i)).π.app (Over.mk (𝟙 i)) ⁻¹ᵁ U a) e t = s a :=
    fun a ↦ exists_appLE_π_app_eq hc' (Over.mk (𝟙 i)) (hU a) (s a)
  choose j g t ht using hA
  obtain ⟨k, fk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
  have ψ : ∀ a, k ⟶ j a := fun a ↦ (fk (by simp)).some
  refine ⟨k.left, k.hom, fun a e ↦ ?_⟩
  have hw : (ψ a).left ≫ (g a).left = k.hom := by
    simpa using Over.w (ψ a ≫ g a)
  have hRP : (D.map k.hom ⁻¹ᵁ U a : (D.obj k.left).Opens) ≤
      D.map (ψ a).left ⁻¹ᵁ (D.map (g a).left ⁻¹ᵁ U a) := by
    rw [← Scheme.Hom.comp_preimage, ← D.map_comp, hw]
  refine Scheme.Hom.range_appLE_subset_of_comp_eq (c.π.app k.left) (D.map (ψ a).left)
    (c.π.app (j a).left) (c.w (ψ a).left) hRP e ?_ ?_
  · rw [← Scheme.Hom.comp_preimage, c.w]
    exact le_rfl
  · exact ⟨t a, ht a _⟩

open TopologicalSpace in
/-- **Immersion into a scheme of finite presentation** (Stacks Project Tag 01ZE): a
quasi-compact quasi-separated scheme `X` that is locally of finite type over a quasi-compact
quasi-separated scheme `S` admits an immersion over `S` into a scheme of finite presentation
over `S`. (Blueprint: `lemma:nagata-immersion-into-fp-model`.) -/
@[stacks 01ZE]
theorem Scheme.Hom.exists_isImmersion_locallyOfFinitePresentation {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace S] [QuasiSeparatedSpace S]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ S) (i : X ⟶ Y), LocallyOfFinitePresentation p ∧ QuasiCompact p ∧
      QuasiSeparated p ∧ IsImmersion i ∧ i ≫ p = f := by
  classical
  obtain ⟨N⟩ := X.nonempty_noetherianApproximation
  have hπaff : ∀ j : N.I, IsAffineHom (N.π.app j) :=
    fun j ↦ isAffineHom_π_app N.D (Cone.mk X N.π) N.isLimit j
  -- an affine open cover of `X`, each member mapping into an affine open of `S`
  have key : ∀ x : X, ∃ (Wx : X.Opens) (Vx : S.Opens), IsAffineOpen Wx ∧ IsAffineOpen Vx ∧
      x ∈ Wx ∧ Wx ≤ f ⁻¹ᵁ Vx := by
    intro x
    obtain ⟨_, ⟨Vx, hVx, rfl⟩, hfx, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨Wx, hWx, rfl⟩, hxWx, hlex⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (f ⁻¹ᵁ Vx : X.Opens) from hfx)
        (f ⁻¹ᵁ Vx).isOpen
    exact ⟨Wx, Vx, hWx, hVx, hxWx, hlex⟩
  choose W V hW hV hxW hWV using key
  have hcov : IsOpenCover W := top_le_iff.mp fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxW x⟩
  obtain ⟨τ, hτ⟩ := hcov.exists_finite_of_compactSpace
  -- descend the cover to a stage
  obtain ⟨i, U, hUcov, hU⟩ := Scheme.exists_isOpenCover_and_isAffine_of_finite N.D
    (Cone.mk X N.π) N.isLimit (fun a : τ ↦ W a.1) hτ (fun a ↦ hW a.1)
  have haff : ∀ a : τ, IsAffineOpen (N.π.app i ⁻¹ᵁ U a) := fun a ↦ (hU a).1.preimage _
  have hle : ∀ a : τ, (N.π.app i ⁻¹ᵁ U a : X.Opens) ≤ f ⁻¹ᵁ V a.1 := by
    intro a
    rw [← (hU a).2]
    exact hWV a.1
  -- the sections of `X` over the members of the cover are finitely generated algebras
  have hft : ∀ a : τ, RingHom.FiniteType
      (f.appLE (V a.1) (N.π.app i ⁻¹ᵁ U a) (hle a)).hom :=
    fun a ↦ HasRingHomProperty.appLE (@LocallyOfFiniteType) f ‹LocallyOfFiniteType f›
      ⟨V a.1, hV a.1⟩ ⟨_, haff a⟩ (hle a)
  have hgen : ∀ a : τ, ∃ gens : Finset Γ(X, N.π.app i ⁻¹ᵁ U a),
      ∀ T : Subring Γ(X, N.π.app i ⁻¹ᵁ U a),
        (∀ r, (f.appLE (V a.1) (N.π.app i ⁻¹ᵁ U a) (hle a)).hom r ∈ T) →
        (∀ x ∈ gens, x ∈ T) → ∀ z, z ∈ T := by
    intro a
    let := (f.appLE (V a.1) (N.π.app i ⁻¹ᵁ U a) (hle a)).hom.toAlgebra
    obtain ⟨gens, hgens⟩ := (hft a).out
    refine ⟨gens, fun T h1 h2 z ↦ ?_⟩
    have hT : (⊤ : Subalgebra Γ(S, V a.1) Γ(X, N.π.app i ⁻¹ᵁ U a)) ≤
        (⟨T.toSubsemiring, h1⟩ : Subalgebra Γ(S, V a.1) Γ(X, N.π.app i ⁻¹ᵁ U a)) := by
      rw [← hgens]
      exact Algebra.adjoin_le (fun x hx ↦ h2 x (by simpa using hx))
    exact hT (Algebra.mem_top)
  choose gens hgens using hgen
  -- descend the generators to a common stage
  obtain ⟨k, gk, hk⟩ := exists_hom_forall_mem_range_appLE (D := N.D) (c := Cone.mk X N.π)
    N.isLimit i (σ := Σ a : τ, {x // x ∈ gens a}) (U := fun q ↦ U q.1)
    (fun q ↦ (hU q.1).1) (fun q ↦ q.2.1)
  -- the finite presentation model
  have : LocallyOfFinitePresentation (specULiftZIsTerminal.from (N.D.obj k)) := inferInstance
  have : QuasiCompact (specULiftZIsTerminal.from (N.D.obj k)) :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance
  have : QuasiSeparated (specULiftZIsTerminal.from (N.D.obj k)) :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated)).mpr inferInstance
  refine ⟨pullback (specULiftZIsTerminal.from (N.D.obj k)) (specULiftZIsTerminal.from S),
    pullback.snd _ _, pullback.lift (N.π.app k) f (specULiftZIsTerminal.hom_ext _ _),
    MorphismProperty.pullback_snd _ _ ‹_›, MorphismProperty.pullback_snd _ _ ‹_›,
    MorphismProperty.pullback_snd _ _ ‹_›, ?_, pullback.lift_snd _ _ _⟩
  set tZ := specULiftZIsTerminal.from (N.D.obj k) with htZ
  set tS := specULiftZIsTerminal.from S with htS
  set u : X ⟶ pullback tZ tS :=
    pullback.lift (N.π.app k) f (specULiftZIsTerminal.hom_ext _ _) with hu
  set A : τ → (N.D.obj k).Opens := fun a ↦ N.D.map gk ⁻¹ᵁ U a with hA
  set O : τ → (pullback tZ tS).Opens :=
    fun a ↦ pullback.fst tZ tS ⁻¹ᵁ A a ⊓ pullback.snd tZ tS ⁻¹ᵁ V a.1 with hO
  have hufst : u ≫ pullback.fst tZ tS = N.π.app k := pullback.lift_fst _ _ _
  have husnd : u ≫ pullback.snd tZ tS = f := pullback.lift_snd _ _ _
  have hpreA : ∀ a : τ, N.π.app k ⁻¹ᵁ A a = N.π.app i ⁻¹ᵁ U a := by
    intro a
    change N.π.app k ⁻¹ᵁ (N.D.map gk ⁻¹ᵁ U a) = _
    have hw : N.π.app k ≫ N.D.map gk = N.π.app i := (Cone.mk X N.π).w gk
    rw [← Scheme.Hom.comp_preimage, hw]
  have hupre : ∀ a : τ, u ⁻¹ᵁ O a = N.π.app i ⁻¹ᵁ U a := by
    intro a
    change u ⁻¹ᵁ (_ ⊓ _) = _
    simp only [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, hufst, husnd, hpreA a]
    exact inf_eq_left.mpr (hle a)
  refine IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsImmersion) O ?_ ?_
  · rintro _ ⟨x, rfl⟩
    have htop : (⨆ a : τ, N.π.app i ⁻¹ᵁ U a) = ⊤ := by
      rw [← Scheme.Hom.preimage_iSup, hUcov.iSup_eq_top]
      simp
    have hx : x ∈ (⨆ a : τ, N.π.app i ⁻¹ᵁ U a) := by rw [htop]; trivial
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hx
    rw [← hupre a] at ha
    exact SetLike.mem_coe.mpr (Opens.mem_iSup.mpr ⟨a, ha⟩)
  · intro a
    have hOaff : IsAffineOpen (O a) :=
      isAffineOpen_preimage_inf_preimage_pullback tZ tS ((hU a).1.preimage (N.D.map gk)) (hV a.1)
    have : IsAffine (O a).toScheme := hOaff
    have hsurj : ∀ (e : (N.π.app i ⁻¹ᵁ U a : X.Opens) ≤ u ⁻¹ᵁ O a),
        Function.Surjective (u.appLE (O a) (N.π.app i ⁻¹ᵁ U a) e) := by
      intro e z
      have hmem := hgens a ((u.appLE (O a) (N.π.app i ⁻¹ᵁ U a) e).hom.range) ?_ ?_ z
      · exact RingHom.mem_range.mp hmem
      · intro r
        exact Scheme.Hom.range_appLE_subset_of_comp_eq u (pullback.snd tZ tS) f husnd
          inf_le_right e (hle a) ⟨r, rfl⟩
      · intro x hx
        exact Scheme.Hom.range_appLE_subset_of_comp_eq u (pullback.fst tZ tS) (N.π.app k) hufst
          inf_le_left e (le_of_eq (hpreA a).symm) (hk ⟨a, ⟨x, hx⟩⟩ _)
    have hcl : ∀ (e : (N.π.app i ⁻¹ᵁ U a : X.Opens) ≤ u ⁻¹ᵁ O a),
        IsClosedImmersion (u.resLE (O a) (N.π.app i ⁻¹ᵁ U a) e) := by
      intro e
      rw [HasAffineProperty.iff_of_isAffine (P := @IsClosedImmersion)]
      exact ⟨haff a, Scheme.Hom.surjective_resLE_appTop u e (hsurj e)⟩
    rw [← Scheme.Hom.resLE_eq_morphismRestrict,
      Scheme.Hom.resLE_congr u _ rfl (hupre a) @IsImmersion]
    have := hcl (le_of_eq (hupre a).symm)
    infer_instance

end FinitePresentationModel

end AlgebraicGeometry
