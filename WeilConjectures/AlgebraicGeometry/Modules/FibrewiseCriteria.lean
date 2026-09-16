/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Fiber
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyTrivial
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Fibrewise criteria for a morphism of line bundles

Let `S` be a scheme and `φ : M ⟶ N` a morphism of invertible sheaves of `𝒪_S`-modules. This file
reads `φ` on the fibres: `φ(s) : M(s) ⟶ N(s)` is `AlgebraicGeometry.Scheme.Modules.fiberMap φ s`,
a linear map between one-dimensional `κ(s)`-vector spaces, and proves the two facts about the
*degeneracy locus* `{s : φ(s) = 0}` that the seesaw theorem and the theorem of the cube use: it
is closed, and if it is empty then `φ` is an isomorphism.

Both proofs work on an open `W` trivialising `M` and `N`. There `φ` becomes an endomorphism of
the structure sheaf, that is multiplication by a function `a ∈ Γ(W, 𝒪_W)`: the degeneracy locus
on `W` is the complement of the basic open subset of `a`, which is closed, and the hypothesis of
the second statement says that `a` is a unit in every local ring of `W`, hence a unit of
`Γ(W, 𝒪_W)` by `AlgebraicGeometry.RingedSpace.isUnit_of_isUnit_germ`.

## Main results

- `AlgebraicGeometry.Scheme.Modules.isClosed_setOf_fiberMap_eq_zero`: **the degeneracy locus of a
  morphism of line bundles is closed.**
- `AlgebraicGeometry.Scheme.Modules.isIso_of_forall_fiberMap_ne_zero`: **a morphism of line
  bundles which is non-zero on every fibre is an isomorphism**, with the characterisation
  `AlgebraicGeometry.Scheme.Modules.isIso_iff_forall_fiberMap_ne_zero`.

Along the way the file records what an endomorphism of the structure sheaf is: it is
multiplication by the global function `AlgebraicGeometry.Scheme.Modules.endSection`, by
`AlgebraicGeometry.Scheme.Modules.app_eq_mul_endSection`, it is an isomorphism as soon as that
function is a unit (`AlgebraicGeometry.Scheme.Modules.isIso_of_isUnit_endSection`), and its fibre
at `x` vanishes exactly when that function does
(`AlgebraicGeometry.Scheme.Modules.fiberMap_eq_zero_iff_evaluation_endSection`).

## Blueprint

`lem:cube-degeneracy-closed` and `lem:cube-invertible-fibrewise` of
`blueprint/src/version/detailed/curve_estimates/27_theorem_of_the_cube.tex`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite SheafOfModules TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section StructureSheafEnd

/-- The global function attached to an endomorphism of the structure sheaf of a scheme: the
image of the unit function. The endomorphism is multiplication by it, see
`AlgebraicGeometry.Scheme.Modules.app_eq_mul_endSection`. -/
noncomputable def endSection (ψ : X.structureModules ⟶ X.structureModules) : Γ(X, ⊤) :=
  Hom.app ψ ⊤ (oneSection X ⊤)

/-- **An endomorphism of the structure sheaf is multiplication by a global function**, namely by
`AlgebraicGeometry.Scheme.Modules.endSection`. -/
lemma app_eq_mul_endSection (ψ : X.structureModules ⟶ X.structureModules) (U : X.Opens)
    (r : Γ(X, U)) :
    (Hom.app ψ U r : Γ(X, U)) =
      r * X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (endSection ψ) := by
  have hnat := Hom.naturality_apply ψ (homOfLE (le_top : U ≤ ⊤)) (oneSection X ⊤)
  rw [map_oneSection] at hnat
  conv_lhs => rw [show (r : Γ(X.structureModules, U)) = r • oneSection X U from (mul_one r).symm]
  rw [Hom.app_smul, hnat]
  rfl

/-- **An endomorphism of the structure sheaf is determined by the corresponding global
function.** -/
lemma endSection_injective {ψ ψ' : X.structureModules ⟶ X.structureModules}
    (h : endSection ψ = endSection ψ') : ψ = ψ' := by
  refine hom_ext ψ ψ' fun U ↦ ?_
  ext z
  rw [app_eq_mul_endSection ψ U z, app_eq_mul_endSection ψ' U z, h]

@[simp]
lemma endSection_id : endSection (𝟙 X.structureModules) = 1 := rfl

/-- Multiplication by a global function, as an endomorphism of the structure sheaf. It is the
inverse of `AlgebraicGeometry.Scheme.Modules.endSection`. -/
noncomputable def endOfSection (X : Scheme.{u}) (a : Γ(X, ⊤)) :
    X.structureModules ⟶ X.structureModules :=
  homOfSectionTop X.structureModules a

@[simp]
lemma endSection_endOfSection (a : Γ(X, ⊤)) : endSection (endOfSection X a) = a :=
  (homOfSectionTop_app_top X.structureModules a (1 : Γ(X, ⊤))).trans (one_smul _ _)

@[simp]
lemma endSection_comp (ψ ψ' : X.structureModules ⟶ X.structureModules) :
    endSection (ψ ≫ ψ') = endSection ψ * endSection ψ' := by
  have h : endSection (ψ ≫ ψ') = Hom.app ψ' ⊤ (endSection ψ) := rfl
  rw [h, app_eq_mul_endSection ψ' ⊤ (endSection ψ),
    show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (op (⊤ : X.Opens)) from rfl,
    CategoryTheory.Functor.map_id]
  rfl

/-- **An endomorphism of the structure sheaf given by a unit is an isomorphism**, the inverse
being multiplication by the inverse function. -/
theorem isIso_of_isUnit_endSection {ψ : X.structureModules ⟶ X.structureModules}
    (h : IsUnit (endSection ψ)) : IsIso ψ := by
  obtain ⟨b, hb⟩ : ∃ b : Γ(X, ⊤), endSection ψ * b = 1 := by
    obtain ⟨u, hu⟩ := h
    exact ⟨((u⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)), by rw [← hu]; exact u.mul_inv⟩
  refine ⟨⟨endOfSection X b, endSection_injective ?_, endSection_injective ?_⟩⟩
  · rw [endSection_comp, endSection_endOfSection, endSection_id, hb]
  · rw [endSection_comp, endSection_endOfSection, endSection_id, mul_comm, hb]

/-- **The fibre of an endomorphism of the structure sheaf vanishes at `x` exactly when the
corresponding global function does.** -/
lemma fiberMap_eq_zero_iff_evaluation_endSection (ψ : X.structureModules ⟶ X.structureModules)
    (x : X) : fiberMap ψ x = 0 ↔ X.Γevaluation x (endSection ψ) = 0 := by
  have hv : fiberMk X.structureModules x (oneSection X ⊤) ≠ 0 := by
    intro hz
    have hz' := (fiberMk_unit_eq_zero_iff x (1 : Γ(X, ⊤))).1 hz
    simp at hz'
  have happ : fiberMap ψ x (fiberMk X.structureModules x (oneSection X ⊤)) =
      fiberMk X.structureModules x (endSection ψ) := fiberMap_fiberMk ψ x _
  rw [← fiberMk_unit_eq_zero_iff x (endSection ψ)]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← happ, h]
    simp
  · have hfin : Module.finrank (X.residueField x) (fiber X.structureModules x) = 1 := by
      rw [(fiberUnitIso X x).toLinearEquiv.finrank_eq, Module.finrank_self]
    have hfd : FiniteDimensional (X.residueField x) (fiber X.structureModules x) :=
      Module.finite_of_finrank_pos (by rw [hfin]; norm_num)
    have hspan : Submodule.span (X.residueField x)
        {fiberMk X.structureModules x (oneSection X ⊤)} = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_singleton hv, hfin]
    refine ModuleCat.hom_ext (LinearMap.ext fun w ↦ ?_)
    obtain ⟨c, rfl⟩ :=
      Submodule.mem_span_singleton.1 (hspan ▸ Submodule.mem_top (R := X.residueField x) (x := w))
    rw [ModuleCat.hom_zero, LinearMap.zero_apply]
    have hsm : (fiberMap ψ x) (c • fiberMk X.structureModules x (oneSection X ⊤)) =
        c • (fiberMap ψ x) (fiberMk X.structureModules x (oneSection X ⊤)) :=
      (fiberMap ψ x).hom.map_smul c _
    change (fiberMap ψ x) (c • fiberMk X.structureModules x (oneSection X ⊤)) = 0
    rw [hsm, happ, h, smul_zero]

end StructureSheafEnd

section Local

variable {M N : X.Modules}

/-- **The fibre of a restriction to an open subscheme.** A morphism of sheaves of modules
vanishes on the fibre at a point of an open subscheme exactly when its restriction does. -/
lemma fiberMap_restrictFunctor_map_eq_zero_iff {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (φ : M ⟶ N) (y : Y) :
    fiberMap ((restrictFunctor f).map φ) y = 0 ↔ fiberMap φ (f y) = 0 := by
  have h₁ : fiberMap ((restrictFunctor f).map φ) y ≫
      fiberMap ((restrictFunctorIsoPullback f).hom.app N) y =
      fiberMap ((restrictFunctorIsoPullback f).hom.app M) y ≫
        fiberMap ((Modules.pullback f).map φ) y := by
    rw [← fiberMap_comp, ← fiberMap_comp, (restrictFunctorIsoPullback f).hom.naturality φ]
  have h₂ : fiberMap ((Modules.pullback f).map φ) y ≫ (fiberFunctorPullbackIso f y).hom.app N =
      (fiberFunctorPullbackIso f y).hom.app M ≫
        (ModuleCat.restrictScalars (inv (f.residueFieldMap y)).hom).map (fiberMap φ (f y)) :=
    (fiberFunctorPullbackIso f y).hom.naturality φ
  have e₁ : fiberMap ((restrictFunctor f).map φ) y = 0 ↔
      fiberMap ((Modules.pullback f).map φ) y = 0 := by
    constructor
    · intro h
      exact (Preadditive.IsIso.comp_left_eq_zero
        (fiberMap ((restrictFunctorIsoPullback f).hom.app M) y)
        (fiberMap ((Modules.pullback f).map φ) y)).1 (by rw [← h₁, h, Limits.zero_comp])
    · intro h
      exact (Preadditive.IsIso.comp_right_eq_zero
        (fiberMap ((restrictFunctor f).map φ) y)
        (fiberMap ((restrictFunctorIsoPullback f).hom.app N) y)).1
          (by rw [h₁, h, Limits.comp_zero])
  have e₂ : fiberMap ((Modules.pullback f).map φ) y = 0 ↔
      (ModuleCat.restrictScalars (inv (f.residueFieldMap y)).hom).map (fiberMap φ (f y)) = 0 := by
    constructor
    · intro h
      exact (Preadditive.IsIso.comp_left_eq_zero ((fiberFunctorPullbackIso f y).hom.app M)
        ((ModuleCat.restrictScalars (inv (f.residueFieldMap y)).hom).map
          (fiberMap φ (f y)))).1 (by rw [← h₂, h, Limits.zero_comp])
    · intro h
      exact (Preadditive.IsIso.comp_right_eq_zero (fiberMap ((Modules.pullback f).map φ) y)
        ((fiberFunctorPullbackIso f y).hom.app N)).1 (by rw [h₂, h, Limits.comp_zero])
  rw [e₁, e₂, Functor.map_eq_zero_iff]

/-- **A morphism of sheaves of modules which is locally an isomorphism is an isomorphism**: if
every point has an open neighbourhood `W` such that the morphism is invertible on sections over
every open subset of `W`, then it is an isomorphism. -/
theorem isIso_of_forall_exists_isIso_app (φ : M ⟶ N)
    (h : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧ ∀ V : X.Opens, V ≤ W → IsIso (Hom.app φ V)) :
    IsIso φ := by
  choose W hxW hW using h
  rw [Hom.isIso_iff_isIso_app]
  intro U
  let S : Sieve U :=
    { arrows := fun V _ ↦ ∃ x : X, V ≤ W x
      downward_closed := by
        intro V V' f hV g
        exact hV.imp fun _ hx ↦ le_trans (leOfHom g) hx }
  have hS : S ∈ Opens.grothendieckTopology X U :=
    fun x hx ↦ ⟨U ⊓ W x, homOfLE inf_le_left, ⟨x, inf_le_right⟩, hx, hxW x⟩
  refine Presheaf.isIso_app_of_isIso_app_of_mem (Opens.grothendieckTopology X)
    M.isSheaf N.isSheaf φ.mapPresheaf S hS fun V f hV ↦ ?_
  obtain ⟨x, hx⟩ := hV
  exact hW x V hx

end Local

section Fibrewise

variable {M N : X.Modules}

/-- **The local form of the fibrewise criteria.** Around every point of `X` there is an open `W`
and a function `a ∈ Γ(W, 𝒪_W)` such that, on `W`, the degeneracy locus of `φ` is the zero set of
`a`, and such that `φ` is invertible on every open subset of `W` as soon as `a` is a unit. -/
theorem exists_endSection_spec (hM : M.Invertible) (hN : N.Invertible) (φ : M ⟶ N) (x : X) :
    ∃ (W : X.Opens) (_ : x ∈ W) (a : Γ(W.toScheme, ⊤)),
      (∀ y : W.toScheme, fiberMap φ (W.ι y) = 0 ↔ W.toScheme.Γevaluation y a = 0) ∧
      (IsUnit a → ∀ V : X.Opens, V ≤ W → IsIso (Hom.app φ V)) := by
  obtain ⟨W₁, hx₁, ⟨e₁⟩⟩ := hM.exists_restrict_iso_tensorUnit x
  obtain ⟨W₂, hx₂, ⟨e₂⟩⟩ := hN.exists_restrict_iso_tensorUnit x
  obtain ⟨eM⟩ : Nonempty (M.restrict (W₁ ⊓ W₂).ι ≅ (W₁ ⊓ W₂).toScheme.structureModules) :=
    ⟨restrictIsoTensorUnitOfLE e₁ inf_le_left ≪≫
      SheafOfModules.tensorUnitIso (W₁ ⊓ W₂).toScheme.sheaf⟩
  obtain ⟨eN⟩ : Nonempty (N.restrict (W₁ ⊓ W₂).ι ≅ (W₁ ⊓ W₂).toScheme.structureModules) :=
    ⟨restrictIsoTensorUnitOfLE e₂ inf_le_right ≪≫
      SheafOfModules.tensorUnitIso (W₁ ⊓ W₂).toScheme.sheaf⟩
  set ψ : (W₁ ⊓ W₂).toScheme.structureModules ⟶ (W₁ ⊓ W₂).toScheme.structureModules :=
    eM.inv ≫ (restrictFunctor (W₁ ⊓ W₂).ι).map φ ≫ eN.hom with hψ
  refine ⟨W₁ ⊓ W₂, ⟨hx₁, hx₂⟩, endSection ψ, fun y ↦ ?_, fun ha V hV ↦ ?_⟩
  · rw [← fiberMap_eq_zero_iff_evaluation_endSection ψ y,
      ← fiberMap_restrictFunctor_map_eq_zero_iff (W₁ ⊓ W₂).ι φ y, hψ, fiberMap_comp,
      fiberMap_comp, Preadditive.IsIso.comp_left_eq_zero, Preadditive.IsIso.comp_right_eq_zero]
  · have hiso : IsIso ψ := isIso_of_isUnit_endSection ha
    have hres : IsIso ((restrictFunctor (W₁ ⊓ W₂).ι).map φ) := by
      have hfac : (restrictFunctor (W₁ ⊓ W₂).ι).map φ = eM.hom ≫ ψ ≫ eN.inv := by
        rw [hψ]; simp
      rw [hfac]
      infer_instance
    obtain ⟨U', hU'⟩ : ∃ U' : (W₁ ⊓ W₂).toScheme.Opens, (W₁ ⊓ W₂).ι ''ᵁ U' = V :=
      ⟨(W₁ ⊓ W₂).ι ⁻¹ᵁ V, by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
          inf_eq_right.2 hV]⟩
    subst hU'
    exact (inferInstance : IsIso (Hom.app ((restrictFunctor (W₁ ⊓ W₂).ι).map φ) U'))

/-- **The degeneracy locus of a morphism of line bundles is closed.** For a morphism
`φ : M ⟶ N` of invertible sheaves of modules on a scheme `X`, the set of points at which the
induced map `M(x) ⟶ N(x)` on fibres vanishes is closed.

This is `lem:cube-degeneracy-closed` of the blueprint. -/
theorem isClosed_setOf_fiberMap_eq_zero (hM : M.Invertible) (hN : N.Invertible) (φ : M ⟶ N) :
    IsClosed {x : X | fiberMap φ x = 0} := by
  choose W hxW a ha _ using exists_endSection_spec hM hN φ
  have hcov : IsOpenCover W := eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ⟨x, hxW x⟩
  rw [hcov.isClosed_iff_coe_preimage]
  intro i
  have hset : (Subtype.val ⁻¹' {z : X | fiberMap φ z = 0} : Set (W i)) =
      (((W i).toScheme.basicOpen (a i) : (W i).toScheme.Opens) : Set (W i))ᶜ := by
    ext y
    change fiberMap φ ((W i).ι y) = 0 ↔ y ∉ (W i).toScheme.basicOpen (a i)
    rw [ha i y]
    exact (W i).toScheme.evaluation_eq_zero_iff_notMem_basicOpen (U := ⊤) y trivial (a i)
  exact Eq.mpr (congrArg IsClosed hset)
    ((W i).toScheme.basicOpen (a i)).isOpen.isClosed_compl

/-- **A morphism of line bundles which is non-zero on every fibre is an isomorphism.** For a
morphism `φ : M ⟶ N` of invertible sheaves of modules on a scheme `X`, if the induced map
`M(x) ⟶ N(x)` on fibres is non-zero at every point `x`, then `φ` is an isomorphism.

This is `lem:cube-invertible-fibrewise` of the blueprint. -/
theorem isIso_of_forall_fiberMap_ne_zero (hM : M.Invertible) (hN : N.Invertible) (φ : M ⟶ N)
    (h : ∀ x : X, fiberMap φ x ≠ 0) : IsIso φ := by
  choose W hxW a ha hiso using exists_endSection_spec hM hN φ
  refine isIso_of_forall_exists_isIso_app φ fun x ↦ ⟨W x, hxW x, hiso x ?_⟩
  refine RingedSpace.isUnit_of_isUnit_germ
    (W x).toScheme.toLocallyRingedSpace.toRingedSpace ⊤ (a x) fun y _ ↦ ?_
  have hy : (W x).toScheme.Γevaluation y (a x) ≠ 0 := fun hz ↦ h ((W x).ι y) ((ha x y).2 hz)
  have hy' : y ∈ (W x).toScheme.basicOpen (a x) :=
    ((W x).toScheme.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) y trivial (a x)).1 hy
  exact ((W x).toScheme.mem_basicOpen (a x) y trivial).1 hy'

/-- **The fibrewise criterion for a morphism of line bundles.** A morphism of invertible sheaves
of modules on a scheme is an isomorphism exactly when it is non-zero on every fibre. -/
theorem isIso_iff_forall_fiberMap_ne_zero (hM : M.Invertible) (hN : N.Invertible) (φ : M ⟶ N) :
    IsIso φ ↔ ∀ x : X, fiberMap φ x ≠ 0 := by
  refine ⟨fun hφ x hz ↦ ?_, isIso_of_forall_fiberMap_ne_zero hM hN φ⟩
  have hnt : Nontrivial (fiber M x) :=
    Module.nontrivial_of_finrank_pos (R := X.residueField x)
      (by rw [finrank_fiber_eq_one hM x]; norm_num)
  obtain ⟨v, hv⟩ := exists_ne (0 : fiber M x)
  have hinj : Function.Injective (fiberMap φ x) :=
    ((ConcreteCategory.isIso_iff_bijective (fiberMap φ x)).1 inferInstance).1
  exact hv (hinj (by simp [hz]))

end Fibrewise

end AlgebraicGeometry.Scheme.Modules
