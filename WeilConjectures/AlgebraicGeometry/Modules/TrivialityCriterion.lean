/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FibrewiseCriteria
public import WeilConjectures.AlgebraicGeometry.Modules.TrivialLineBundle

/-!
# The triviality criterion for a line bundle over a field

Let `K` be a field, let `X` be a proper geometrically integral `K`-scheme and let `L` be a line
bundle on `X`, with tensor inverse `N`. This file proves that `L` is trivial — isomorphic to the
structure sheaf — **if and only if** both `Γ(X, L)` and `Γ(X, N)` contain a non-zero global
section. The field `K` is not assumed algebraically closed, which is what makes the criterion
applicable at *every* point of a base scheme and not only at the rational ones.

The invertibility of `L` and of `N` is not a separate hypothesis: the criterion takes an
isomorphism `e : L ⊗ N ≅ 𝟙_ X.Modules`, from which `SheafOfModules.Invertible.left` and
`SheafOfModules.Invertible.right` recover `L.Invertible` and `N.Invertible`.

## The proof

If `L` is trivial then so is `N`, and both spaces of global sections are isomorphic to
`Γ(X, 𝒪ₓ)`, which is a field and in particular non-zero.

Conversely, let `s` and `v` be non-zero global sections of `L` and of `N`, and write
`σ : 𝒪ₓ ⟶ L` and `τ : 𝒪ₓ ⟶ N` for the morphisms they determine
(`AlgebraicGeometry.Scheme.Modules.homOfSectionTop`). On a reduced scheme a non-zero morphism of
line bundles is non-zero on *some* fibre
(`AlgebraicGeometry.Scheme.Modules.eq_zero_of_forall_fiberMap_eq_zero`), and by
`AlgebraicGeometry.Scheme.Modules.isClosed_setOf_fiberMap_eq_zero` the two loci where `σ` and `τ`
are non-zero on the fibre are open; since `X` is irreducible they meet, at a point `x₀` say. At
`x₀` both fibre maps are non-zero maps between one-dimensional `κ(x₀)`-vector spaces, hence
isomorphisms, hence so is their tensor product, hence so is the fibre at `x₀` of the composite
`𝒪ₓ ≅ 𝒪ₓ ⊗ 𝒪ₓ ⟶ L ⊗ N ≅ 𝒪ₓ`. That composite is multiplication by a global function `c`, which
therefore does not vanish at `x₀`; as `Γ(X, 𝒪ₓ)` is a field, `c` is a unit, so the composite is
an isomorphism and `σ` is non-zero on *every* fibre. The fibrewise criterion
`AlgebraicGeometry.Scheme.Modules.isIso_of_forall_fiberMap_ne_zero` then makes `σ` an
isomorphism.

## Main results

- `AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_iff_of_isField`: **the triviality
  criterion**, under the hypotheses that `X` is integral and that its ring of global functions is
  a field.
- `AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_iff_of_geometricallyIntegral`: the
  same criterion for `X` proper and geometrically integral over a field `K`, where those two
  hypotheses are automatic.

Along the way:

- `AlgebraicGeometry.Scheme.Modules.eq_zero_of_forall_exists_app_eq_zero`: a morphism of sheaves
  of modules vanishing on the sections over arbitrarily small open subsets is zero.
- `AlgebraicGeometry.Scheme.Modules.eq_zero_of_forall_fiberMap_eq_zero`: on a reduced scheme, a
  morphism of line bundles vanishing on every fibre is zero.
- `AlgebraicGeometry.Scheme.Modules.isIso_fiberMap_of_ne_zero`: a non-zero map between the fibres
  of two line bundles is an isomorphism.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules.eq_zero_of_forall_exists_app_eq_zero` is the additive companion
of `AlgebraicGeometry.Scheme.Modules.isIso_of_forall_exists_isIso_app` and belongs next to it in
the mirror file `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`; it is stated here
because that file is being edited by other work in flight.

## Blueprint

`lem:cube-triviality-criterion` of
`blueprint/src/version/detailed/curve_estimates/27_theorem_of_the_cube.tex`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SheafOfModules TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A morphism of sheaves of modules which vanishes on the sections over every small enough open
subset is zero. -/
theorem eq_zero_of_forall_exists_app_eq_zero {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧ ∀ V : X.Opens, V ≤ W → Hom.app φ V = 0) : φ = 0 := by
  choose W hxW hW using h
  have key : ∀ (V : X.Opens) (m : Γ(M, V)), Hom.app φ V m = 0 := by
    intro V m
    refine N.isSheaf.section_ext (U := .op V) (s := Hom.app φ V m) (t := 0) fun x hx ↦
      ⟨V ⊓ W x, inf_le_left, ⟨hx, hxW x⟩, ?_⟩
    have hnat := ConcreteCategory.congr_hom
      (φ.mapPresheaf.naturality (homOfLE (inf_le_left : V ⊓ W x ≤ V)).op) m
    simp only [mapPresheaf_app, ConcreteCategory.comp_apply] at hnat
    rw [← hnat, hW x (V ⊓ W x) inf_le_right]
    simp
  refine hom_ext _ _ fun V ↦ ?_
  rw [Hom.zero_app]
  ext m
  simpa using key V m

/-- **A morphism of line bundles which vanishes on every fibre is zero**, on a reduced scheme. -/
theorem eq_zero_of_forall_fiberMap_eq_zero [IsReduced X] {M N : X.Modules} (hM : M.Invertible)
    (hN : N.Invertible) (φ : M ⟶ N) (h : ∀ x : X, fiberMap φ x = 0) : φ = 0 := by
  refine eq_zero_of_forall_exists_app_eq_zero φ fun x ↦ ?_
  obtain ⟨W, hxW, a, eM, eN, hfac⟩ := exists_restrict_eq_homOfSectionTop hM hN φ x
  have ha : a = 0 := by
    rw [← basicOpen_eq_bot_iff, ← le_bot_iff]
    intro y hy
    exact absurd hy ((Scheme.Γevaluation_eq_zero_iff_notMem_basicOpen _ y a).1
      ((fiberMap_eq_zero_iff_evaluation_of_restrict_eq φ hfac y).1 (h (W.ι y))))
  have hzero : (restrictFunctor W.ι).map φ = 0 := by
    rw [hfac, ha, ← endSectionRingEquiv_symm_apply, map_zero]
    simp
  refine ⟨W, hxW, fun V hV ↦ ?_⟩
  obtain ⟨V', rfl⟩ : ∃ V' : W.toScheme.Opens, W.ι ''ᵁ V' = V :=
    ⟨W.ι ⁻¹ᵁ V, by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.2 hV]⟩
  have hz : Hom.app ((restrictFunctor W.ι).map φ) V' = 0 := by rw [hzero]; rfl
  exact hz

/-- **A non-zero map between the fibres of two line bundles is an isomorphism**: both fibres are
one-dimensional over the residue field. -/
theorem isIso_fiberMap_of_ne_zero {M N : X.Modules} (hM : M.Invertible) (hN : N.Invertible)
    (φ : M ⟶ N) {x : X} (hφ : fiberMap φ x ≠ 0) : IsIso (fiberMap φ x) := by
  have hM1 : Module.finrank (X.residueField x) (M.fiber x) = 1 := finrank_fiber_eq_one hM x
  have hN1 : Module.finrank (X.residueField x) (N.fiber x) = 1 := finrank_fiber_eq_one hN x
  have : FiniteDimensional (X.residueField x) (M.fiber x) :=
    Module.finite_of_finrank_pos (by rw [hM1]; norm_num)
  have : FiniteDimensional (X.residueField x) (N.fiber x) :=
    Module.finite_of_finrank_pos (by rw [hN1]; norm_num)
  have hsurj : Function.Surjective (ConcreteCategory.hom (fiberMap φ x)) :=
    surjective_of_nonzero_of_finrank_eq_one hN1 fun hz ↦ hφ (ModuleCat.hom_ext hz)
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (hM1.trans hN1.symm)).2 hsurj, hsurj⟩

/-- **A trivial line bundle has a non-zero global section**, as soon as the ring of global
functions of `X` is non-trivial: an isomorphism `M ≅ 𝒪ₓ` carries the unit function to one. -/
theorem exists_ne_zero_of_iso_tensorUnit [Nontrivial Γ(X, ⊤)] {M : X.Modules}
    (f : M ≅ 𝟙_ X.Modules) : ∃ m : Γ(M, ⊤), m ≠ 0 :=
  ⟨(sectionsEquivOfIsoUnit (f ≪≫ tensorUnitIso X.sheaf)).symm 1, fun hz ↦ one_ne_zero
    ((sectionsEquivOfIsoUnit (f ≪≫ tensorUnitIso X.sheaf)).symm.map_eq_zero_iff.1 hz)⟩

variable {L N : X.Modules}

/-- **The triviality criterion for a line bundle.** Let `X` be an integral scheme whose ring of
global functions is a field, and let `L` and `N` be `𝒪ₓ`-modules with `L ⊗ N ≅ 𝒪ₓ`. Then `L` is
isomorphic to the structure sheaf if and only if both `Γ(X, L)` and `Γ(X, N)` contain a non-zero
global section.

This is `lem:cube-triviality-criterion` of the blueprint, stated under the two hypotheses on `X`
that the proof actually uses; see
`AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_iff_of_geometricallyIntegral` for the
form the blueprint gives it. -/
theorem nonempty_iso_tensorUnit_iff_of_isField [IsIntegral X] (hfield : IsField Γ(X, ⊤))
    (e : L ⊗ N ≅ 𝟙_ X.Modules) :
    Nonempty (L ≅ 𝟙_ X.Modules) ↔ (∃ s : Γ(L, ⊤), s ≠ 0) ∧ (∃ v : Γ(N, ⊤), v ≠ 0) := by
  have hL : L.Invertible := SheafOfModules.Invertible.left (R := X.sheaf) e
  have hN : N.Invertible := SheafOfModules.Invertible.right (R := X.sheaf) e
  have hnt : Nontrivial Γ(X, ⊤) := ⟨hfield.exists_pair_ne⟩
  have hunit : X.structureModules.Invertible := SheafOfModules.invertible_unit X.sheaf
  constructor
  · rintro ⟨f⟩
    exact ⟨exists_ne_zero_of_iso_tensorUnit f,
      exists_ne_zero_of_iso_tensorUnit
        ((λ_ N).symm ≪≫ (f.symm ⊗ᵢ Iso.refl N) ≪≫ e)⟩
  · rintro ⟨⟨s, hs⟩, ⟨v, hv⟩⟩
    have key : ∀ (M : X.Modules), M.Invertible → ∀ m : Γ(M, ⊤), m ≠ 0 →
        ∃ x : X, fiberMap (homOfSectionTop M m) x ≠ 0 := by
      intro M hM m hm
      by_contra hcon
      simp only [ne_eq, not_exists, not_not] at hcon
      have hzero := eq_zero_of_forall_fiberMap_eq_zero hunit hM (homOfSectionTop M m) hcon
      have hval := app_homOfSectionTop_oneSection M m
      rw [hzero] at hval
      simp only [Hom.zero_app] at hval
      exact hm (by simpa using hval.symm)
    set t : 𝟙_ X.Modules ≅ X.structureModules := tensorUnitIso X.sheaf
    set σ : X.structureModules ⟶ L := homOfSectionTop L s
    set τ : X.structureModules ⟶ N := homOfSectionTop N v
    set g : 𝟙_ X.Modules ⟶ L := t.hom ≫ σ with hg
    set h : 𝟙_ X.Modules ⟶ N := t.hom ≫ τ with hh
    set ψ : L ⟶ 𝟙_ X.Modules := (ρ_ L).inv ≫ (L ◁ h) ≫ e.hom with hψ
    set χ : X.structureModules ⟶ X.structureModules := σ ≫ ψ ≫ t.hom with hχ
    -- the two degeneracy loci are proper closed subsets of the irreducible space `X`
    obtain ⟨x₁, hx₁⟩ := key L hL s hs
    obtain ⟨x₂, hx₂⟩ := key N hN v hv
    obtain ⟨x₀, -, hx₀₁, hx₀₂⟩ :=
      (IrreducibleSpace.isIrreducible_univ X).isPreirreducible
        {x : X | fiberMap σ x = 0}ᶜ {x : X | fiberMap τ x = 0}ᶜ
        (isClosed_setOf_fiberMap_eq_zero hunit hL σ).isOpen_compl
        (isClosed_setOf_fiberMap_eq_zero hunit hN τ).isOpen_compl
        ⟨x₁, trivial, hx₁⟩ ⟨x₂, trivial, hx₂⟩
    have hσ₀ : fiberMap σ x₀ ≠ 0 := hx₀₁
    have hτ₀ : fiberMap τ x₀ ≠ 0 := hx₀₂
    have htiso : IsIso (fiberMap t.hom x₀) := inferInstance
    have hg₀ : fiberMap g x₀ ≠ 0 := by
      rw [hg, fiberMap_comp, Ne, Preadditive.IsIso.comp_left_eq_zero]
      exact hσ₀
    have hh₀ : fiberMap h x₀ ≠ 0 := by
      rw [hh, fiberMap_comp, Ne, Preadditive.IsIso.comp_left_eq_zero]
      exact hτ₀
    have hgiso : IsIso (fiberMap g x₀) :=
      isIso_fiberMap_of_ne_zero (SheafOfModules.invertible_tensorUnit X.sheaf) hL g hg₀
    have hhiso : IsIso (fiberMap h x₀) :=
      isIso_fiberMap_of_ne_zero (SheafOfModules.invertible_tensorUnit X.sheaf) hN h hh₀
    have htensor : IsIso (fiberMap (g ⊗ₘ h) x₀) := by
      have hnat := fiberTensorIso_hom_naturality g h x₀
      have hcomp : IsIso (fiberMap (g ⊗ₘ h) x₀ ≫ (fiberTensorIso L N x₀).hom) := by
        rw [← hnat]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (fiberTensorIso L N x₀).hom
    have hgψ : g ≫ ψ = (λ_ (𝟙_ X.Modules)).inv ≫ (g ⊗ₘ h) ≫ e.hom := by
      rw [hψ, MonoidalCategory.rightUnitor_inv_naturality_assoc, MonoidalCategory.tensorHom_def,
        MonoidalCategory.unitors_inv_equal]
      simp
    have hχfac : χ = t.inv ≫ ((λ_ (𝟙_ X.Modules)).inv ≫ (g ⊗ₘ h) ≫ e.hom) ≫ t.hom := by
      rw [← hgψ, hχ, hg]
      simp
    have hntfib : Nontrivial (X.structureModules.fiber x₀) :=
      Module.nontrivial_of_finrank_pos (R := X.residueField x₀)
        (by simp [finrank_fiber_structureModules])
    have hχfiberiso : IsIso (fiberMap χ x₀) := by
      rw [hχfac]
      simp only [fiberMap_comp]
      infer_instance
    have hχne : fiberMap χ x₀ ≠ 0 := by
      intro hz
      obtain ⟨w, hw⟩ := exists_ne (0 : X.structureModules.fiber x₀)
      refine hw (((ConcreteCategory.isIso_iff_bijective (fiberMap χ x₀)).1 hχfiberiso).1 ?_)
      rw [hz]
      simp
    have hc : endSection χ ≠ 0 := fun hz ↦ hχne
      ((fiberMap_eq_zero_iff_evaluation_endSection χ x₀).2 (by rw [hz]; simp))
    have hχIso : IsIso χ := (isIso_iff_isUnit_endSection χ).2
      (isUnit_iff_exists_inv.mpr (hfield.mul_inv_cancel hc))
    have hall : ∀ x : X, fiberMap σ x ≠ 0 := by
      intro x hz
      have hnt : Nontrivial (X.structureModules.fiber x) :=
        Module.nontrivial_of_finrank_pos (R := X.residueField x)
          (by simp [finrank_fiber_structureModules])
      refine fiberMap_ne_zero_of_isIso χ x ?_
      rw [hχ, fiberMap_comp, hz, Limits.zero_comp]
    have hσIso : IsIso σ := isIso_of_forall_fiberMap_ne_zero hunit hL σ hall
    exact ⟨(asIso σ).symm ≪≫ t.symm⟩

/-- **The triviality criterion for a line bundle on a proper geometrically integral scheme over a
field.** Let `K` be a field, let `X` be proper and geometrically integral over `K` and let `L`
and `N` be `𝒪ₓ`-modules with `L ⊗ N ≅ 𝒪ₓ`. Then `L` is trivial if and only if both `Γ(X, L)` and
`Γ(X, N)` contain a non-zero global section. The field `K` need not be algebraically closed.

This is `lem:cube-triviality-criterion` of the blueprint. -/
theorem nonempty_iso_tensorUnit_iff_of_geometricallyIntegral {K : Type u} [Field K]
    [X.Over (Spec (.of K))]
    [IsProper (X ↘ Spec (.of K))] [GeometricallyIntegral (X ↘ Spec (.of K))]
    (e : L ⊗ N ≅ 𝟙_ X.Modules) :
    Nonempty (L ≅ 𝟙_ X.Modules) ↔ (∃ s : Γ(L, ⊤), s ≠ 0) ∧ (∃ v : Γ(N, ⊤), v ≠ 0) :=
  have : IsIntegral X := GeometricallyIntegral.isIntegral (X ↘ Spec (.of K))
  nonempty_iso_tensorUnit_iff_of_isField
    (isField_of_universallyClosed K (X ↘ Spec (.of K))) e

end AlgebraicGeometry.Scheme.Modules
