/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.AlgebraicGeometry.Fiber

/-!
# Kernels and fibres of `𝒪_X`-modules

Two independent additions to the theory of sheaves of modules on a scheme.

The first is a concrete description of the sections of a categorical kernel. Limits in
`X.Modules` are computed section-wise, because evaluation at an open subset preserves finite
limits (`SheafOfModules.Finite.evaluationPreservesFiniteLimits`): over any open `U`, the sections
of `kernel f` are exactly the sections of the source that `f` kills. This is the tool that turns
a sheaf of modules defined as a kernel — as the ideal sheaf of a `Scheme.IdealSheafData` is in
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` — into a computable object.

The second is the **fibre `F(x)` of a sheaf of modules at a point**, as a vector space over the
residue field `κ(x)`, together with the **restriction `F_y` of a sheaf of modules to a fibre of a
morphism**. Since Mathlib has no module structure on the stalk of a sheaf of modules, the fibre is
defined not as `F_x ⊗_{𝒪_{X,x}} κ(x)` but by pullback: `F(x)` is the module of global sections of
the pullback of `F` along `Spec κ(x) ⟶ X`. The two agree for quasi-coherent `F`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.fiberFunctor`, `AlgebraicGeometry.Scheme.Modules.fiber`: the
  fibre `F(x)` of a sheaf of `𝒪_X`-modules at a point `x`, as a `κ(x)`-vector space, and its
  functoriality `AlgebraicGeometry.Scheme.Modules.fiberMap` in `F`.
- `AlgebraicGeometry.Scheme.Modules.restrictToFiber`: the restriction `F ↦ F_y` of sheaves of
  modules to the scheme-theoretic fibre of a morphism over a point.

## Main results

- `AlgebraicGeometry.Scheme.Modules.range_map_kernelι`
- `AlgebraicGeometry.Scheme.Modules.fiberFunctorPullbackIso`,
  `AlgebraicGeometry.Scheme.Modules.fiberPullbackIso`: compatibility of the fibre with pullback,
  for a morphism `u` inducing an isomorphism on residue fields at the point in question.
- `AlgebraicGeometry.Scheme.Modules.fiberRestrictToFiberIso`: the fibre of `F_y` at a point `x`
  of the fibre is the fibre of `F` at `f.fiberι y x`.

## Blueprint

The fibre and the restriction to a fibre are notion **(N2)** of `sec:cube-cost`, the formalisation
count of the theorem-of-the-cube chapter. Deferred to later issues, because they need the monoidal
structure on sheaves of modules and the notion of an invertible sheaf, neither of which is
available: the compatibility of the fibre with tensor products and with inverses of line bundles,
and the one-dimensionality of the fibre of a locally free sheaf of rank one.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (U : X.Opens)
  {M N : SheafOfModules.{u} X.ringCatSheaf} (f : M ⟶ N)

/-- **The sections of a kernel are the kernel of the sections.** Over any open `U`, the image
of `kernel.ι f` on sections is the set of sections of `M` killed by `f`.

This is stated for `SheafOfModules X.ringCatSheaf` rather than for the definitionally equal
`X.Modules`, because instance search for `PreservesLimit` does not see through the latter. -/
lemma range_map_kernelι :
    Set.range ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι f)) =
      { x | (SheafOfModules.evaluation X.ringCatSheaf (op U)).map f x = 0 } := by
  set G := SheafOfModules.evaluation X.ringCatSheaf (op U) with hG
  have key : ((PreservesKernel.iso G f ≪≫ ModuleCat.kernelIsoKer (G.map f)).inv ≫
      G.map (kernel.ι f)) = ModuleCat.ofHom (LinearMap.ker (G.map f).hom).subtype := by
    simp [ModuleCat.kernelIsoKer_inv_kernel_ι]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change G.map f (G.map (kernel.ι f) y) = 0
    rw [← ConcreteCategory.comp_apply, ← G.map_comp, kernel.condition, G.map_zero]
    rfl
  · intro hx
    refine ⟨(PreservesKernel.iso G f ≪≫ ModuleCat.kernelIsoKer (G.map f)).inv ⟨x, hx⟩, ?_⟩
    have h2 := ConcreteCategory.congr_hom key ⟨x, hx⟩
    simp only [Iso.trans_inv, ConcreteCategory.comp_apply] at h2
    exact h2

lemma map_kernelι_eq :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι f) =
      (PreservesKernel.iso (SheafOfModules.evaluation X.ringCatSheaf (op U)) f).hom ≫
        kernel.ι _ := by
  rw [← PreservesKernel.iso_inv_ι]
  simp

instance : Mono ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι f)) := by
  rw [map_kernelι_eq]
  infer_instance

/-- `kernel.ι f` is injective on sections over any open, not merely a monomorphism. -/
lemma injective_map_kernelι :
    Function.Injective ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι f)) :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

section BaseChange

variable {R S : CommRingCat.{u}}

/-- Taking global sections of a sheaf of modules on `Spec S` and restricting scalars along
`φ : R ⟶ S` is the same as pushing forward along `Spec φ` and taking global sections there. -/
noncomputable def moduleSpecΓPushforwardIso (φ : R ⟶ S) :
    Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
  NatIso.ofComponents (fun N ↦
    { hom := ModuleCat.homEquiv.symm
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro r x
            obtain ⟨y, rfl⟩ : ∃ y : Γ(N, ⊤), y = x := ⟨x, rfl⟩
            change ((Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r)) • y =
              ((Scheme.ΓSpecIso S).inv (φ r)) • y
            have h := congr($(Scheme.ΓSpecIso_inv_naturality φ) r)
            simp only [CommRingCat.comp_apply] at h
            rw [← h] }
      inv := ModuleCat.homEquiv.symm
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro r x
            obtain ⟨y, rfl⟩ : ∃ y : Γ(N, ⊤), y = x := ⟨x, rfl⟩
            change ((Scheme.ΓSpecIso S).inv (φ r)) • y =
              ((Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r)) • y
            have h := congr($(Scheme.ΓSpecIso_inv_naturality φ) r)
            simp only [CommRingCat.comp_apply] at h
            rw [h] }
      hom_inv_id := rfl
      inv_hom_id := rfl }) (fun _ ↦ rfl)

variable {X Y : Scheme.{u}}

/-- The pullback of sheaves of modules along an isomorphism is the pushforward along its
inverse. -/
noncomputable def pullbackIsoPushforwardInv (f : X ⟶ Y) [IsIso f] :
    Modules.pullback f ≅ Modules.pushforward (inv f) :=
  Adjunction.rightAdjointUniq
    (CategoryTheory.Equivalence.mk (Modules.pullback f) (Modules.pullback (inv f))
      (pullbackComp (inv f) f ≪≫ pullbackCongr (by simp) ≪≫ pullbackId Y).symm
      (pullbackComp f (inv f) ≪≫ pullbackCongr (by simp) ≪≫ pullbackId X)).symm.toAdjunction
    (pullbackPushforwardAdjunction (inv f))

/-- **Base change of global sections along an isomorphism of rings.** For `φ : R ⟶ S` an
isomorphism, pulling a sheaf of modules on `Spec R` back along `Spec φ` and taking global
sections is restricting the scalars of its global sections along `φ⁻¹`. -/
noncomputable def moduleSpecΓPullbackIso (φ : R ⟶ S) [IsIso φ] :
    Modules.pullback (Spec.map φ) ⋙ moduleSpecΓFunctor (R := S) ≅
      moduleSpecΓFunctor (R := R) ⋙ ModuleCat.restrictScalars (inv φ).hom :=
  Functor.isoWhiskerRight (pullbackIsoPushforwardInv (Spec.map φ)) _ ≪≫
    Functor.isoWhiskerRight (pushforwardCongr (Spec.map_inv φ).symm) _ ≪≫
    moduleSpecΓPushforwardIso (inv φ)

end BaseChange

section Fiber

variable {X Y : Scheme.{u}}

/-- The fibre functor at a point `x` of a scheme `X`: it sends a sheaf of `𝒪_X`-modules `F` to
the `κ(x)`-vector space `F(x)`, obtained by pulling `F` back along `Spec κ(x) ⟶ X` and taking
global sections. -/
noncomputable def fiberFunctor (X : Scheme.{u}) (x : X) :
    X.Modules ⥤ ModuleCat (X.residueField x) :=
  Modules.pullback (X.fromSpecResidueField x) ⋙ moduleSpecΓFunctor (R := X.residueField x)

/-- The fibre `F(x)` of a sheaf of `𝒪_X`-modules at a point `x`, as a `κ(x)`-vector space. -/
noncomputable abbrev fiber (F : X.Modules) (x : X) : ModuleCat (X.residueField x) :=
  (fiberFunctor X x).obj F

/-- The `κ(x)`-linear map `φ(x) : F(x) ⟶ G(x)` induced by a morphism `φ : F ⟶ G` of sheaves of
`𝒪_X`-modules. -/
noncomputable abbrev fiberMap {F G : X.Modules} (φ : F ⟶ G) (x : X) : F.fiber x ⟶ G.fiber x :=
  (fiberFunctor X x).map φ

@[simp]
lemma fiberMap_id (F : X.Modules) (x : X) : fiberMap (𝟙 F) x = 𝟙 (F.fiber x) :=
  (fiberFunctor X x).map_id F

@[simp]
lemma fiberMap_comp {F G H : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ H) (x : X) :
    fiberMap (φ ≫ ψ) x = fiberMap φ x ≫ fiberMap ψ x :=
  (fiberFunctor X x).map_comp φ ψ

/-- The restriction `F ↦ F_y` of sheaves of modules to the scheme-theoretic fibre of
`f : X ⟶ Y` over a point `y : Y`, that is, the pullback along `f.fiberι y`. -/
noncomputable abbrev restrictToFiber (f : X ⟶ Y) (y : Y) : X.Modules ⥤ (f.fiber y).Modules :=
  Modules.pullback (f.fiberι y)

/-- **The fibre of a pullback.** If `u : X ⟶ Y` induces an isomorphism `κ(u x) ≅ κ(x)` on
residue fields, then the fibre of `u^* F` at `x` is the fibre of `F` at `u x`, viewed as a
`κ(x)`-vector space along `κ(u x) ≅ κ(x)`. -/
noncomputable def fiberFunctorPullbackIso (u : X ⟶ Y) (x : X) [IsIso (u.residueFieldMap x)] :
    Modules.pullback u ⋙ fiberFunctor X x ≅
      fiberFunctor Y (u x) ⋙ ModuleCat.restrictScalars (inv (u.residueFieldMap x)).hom :=
  Functor.isoWhiskerRight (pullbackComp (X.fromSpecResidueField x) u)
      (moduleSpecΓFunctor (R := X.residueField x)) ≪≫
    Functor.isoWhiskerRight (pullbackCongr (u.SpecMap_residueFieldMap_fromSpecResidueField x).symm)
      (moduleSpecΓFunctor (R := X.residueField x)) ≪≫
    Functor.isoWhiskerRight
      (pullbackComp (Spec.map (u.residueFieldMap x)) (Y.fromSpecResidueField (u x))).symm
      (moduleSpecΓFunctor (R := X.residueField x)) ≪≫
    Functor.isoWhiskerLeft (Modules.pullback (Y.fromSpecResidueField (u x)))
      (moduleSpecΓPullbackIso (u.residueFieldMap x))

/-- The fibre of `u^* F` at `x`, for `u` inducing an isomorphism on the residue field at `x`. -/
noncomputable def fiberPullbackIso (u : X ⟶ Y) (F : Y.Modules) (x : X)
    [IsIso (u.residueFieldMap x)] :
    ((Modules.pullback u).obj F).fiber x ≅
      (ModuleCat.restrictScalars (inv (u.residueFieldMap x)).hom).obj (F.fiber (u x)) :=
  (fiberFunctorPullbackIso u x).app F

/-- **The fibre of a restriction to a fibre.** The fibre of `F_y` at a point `x` of the
scheme-theoretic fibre of `f` over `y` is the fibre of `F` at `f.fiberι y x`; the residue fields
`κ(f.fiberι y x)` and `κ(x)` agree because `f.fiberι y` is a preimmersion. -/
noncomputable def fiberRestrictToFiberIso (f : X ⟶ Y) (y : Y) (F : X.Modules) (x : f.fiber y) :
    ((restrictToFiber f y).obj F).fiber x ≅
      (ModuleCat.restrictScalars (inv ((f.fiberι y).residueFieldMap x)).hom).obj
        (F.fiber (f.fiberι y x)) :=
  fiberPullbackIso (f.fiberι y) F x

end Fiber

end AlgebraicGeometry.Scheme.Modules
