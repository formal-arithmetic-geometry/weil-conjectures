/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.PicardGroup
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.AlgebraicGeometry.Modules.SectionsMonoidal
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The fibre of a sheaf of modules: tensor products, inverses and rank one

Let `X` be a scheme and `x` a point of `X`. The fibre functor
`AlgebraicGeometry.Scheme.Modules.fiberFunctor X x` sends an `𝒪ₓ`-module `F` to the
`κ(x)`-vector space `F(x)`, obtained by pulling `F` back along `Spec κ(x) ⟶ X` and taking global
sections. We show that this functor is monoidal, so that `(F ⊗ G)(x)` is `F(x) ⊗_{κ(x)} G(x)`
and the fibre of the structure sheaf is `κ(x)`.

Both halves of the composite are monoidal: the pullback of `𝒪ₓ`-modules by
`WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal`, and the global sections functor on
`Spec κ(x)` by `WeilConjectures.AlgebraicGeometry.Modules.SectionsMonoidal`, the latter because
`Spec κ(x)` has a single point.

As a consequence, if `L` is an invertible `𝒪ₓ`-module with tensor inverse `N`, then `L(x)` and
`N(x)` are inverse invertible `κ(x)`-modules — they pair to `κ(x)`, and `N(x)` is the dual of
`L(x)` — and `L(x)` is a one-dimensional `κ(x)`-vector space.

## Main declarations

- `AlgebraicGeometry.Scheme.Modules.fiberFunctorMonoidal`: the fibre functor is monoidal, with
  the isomorphisms `AlgebraicGeometry.Scheme.Modules.fiberTensorIso` for a tensor product,
  `AlgebraicGeometry.Scheme.Modules.fiberTensorUnitIso` for the tensor unit and
  `AlgebraicGeometry.Scheme.Modules.fiberUnitIso` for the structure sheaf itself.
- `AlgebraicGeometry.Scheme.Modules.fiberTensorIsoTensorUnit` and
  `AlgebraicGeometry.Scheme.Modules.fiberLinearEquivDual`: the fibres of an invertible sheaf and
  of its inverse pair to `κ(x)`, and the second is the dual of the first; with
  `AlgebraicGeometry.Scheme.Modules.module_invertible_fiber`, the fibre of an invertible sheaf
  is an invertible `κ(x)`-module.
- `AlgebraicGeometry.Scheme.Modules.finrank_fiber_eq_one`: the fibre of an invertible sheaf of
  modules is a one-dimensional `κ(x)`-vector space, with
  `AlgebraicGeometry.Scheme.Modules.rank_fiber_eq_one` for the cardinal-valued rank and
  `AlgebraicGeometry.Scheme.Modules.finiteDimensional_fiber`,
  `AlgebraicGeometry.Scheme.Modules.nontrivial_fiber` for the two consequences used downstream.
- `AlgebraicGeometry.Scheme.Modules.isIso_fiberMap_of_ne_zero`: a non-zero map between the fibres
  of two line bundles is an isomorphism.
- `AlgebraicGeometry.Scheme.Modules.span_fiberMk_oneSection`: the fibre of the structure sheaf
  is spanned by the image of the unit function, whence
  `AlgebraicGeometry.Scheme.Modules.fiberMap_homOfSectionTop_apply`, the fibre of multiplication
  by a global function is multiplication by its value, and
  `AlgebraicGeometry.Scheme.Modules.fiberMap_eq_zero_iff_evaluation_endSection`: the fibre of an
  endomorphism of the structure sheaf vanishes at `x` exactly when the corresponding global
  function does.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **The fibre functor is monoidal.** It is the pullback along `Spec κ(x) ⟶ X`, which is
monoidal, followed by the global sections functor on `Spec κ(x)`, which is monoidal because
`Spec κ(x)` has a single point.

```
     X.Modules ── pullback (X.fromSpecResidueField x) ──> (Spec κ(x)).Modules
           │                                                      │
   fiberFunctor X x                                     moduleSpecΓFunctor
           ↓                                                      ↓
   ModuleCat κ(x) ═══════════════════════════════════════ ModuleCat κ(x)
```
-/
noncomputable instance fiberFunctorMonoidal (X : Scheme.{u}) (x : X) :
    (fiberFunctor X x).Monoidal :=
  inferInstanceAs (Modules.pullback (X.fromSpecResidueField x) ⋙
    moduleSpecΓFunctor (R := X.residueField x)).Monoidal

/-- **The fibre of a tensor product** of sheaves of `𝒪ₓ`-modules is the tensor product over
`κ(x)` of the fibres. -/
noncomputable def fiberTensorIso (F G : X.Modules) (x : X) :
    (F ⊗ G).fiber x ≅ F.fiber x ⊗ G.fiber x :=
  (Functor.Monoidal.μIso (fiberFunctor X x) F G).symm

@[simp]
lemma fiberTensorIso_hom (F G : X.Modules) (x : X) :
    (fiberTensorIso F G x).hom = Functor.OplaxMonoidal.δ (fiberFunctor X x) F G :=
  rfl

@[simp]
lemma fiberTensorIso_inv (F G : X.Modules) (x : X) :
    (fiberTensorIso F G x).inv = Functor.LaxMonoidal.μ (fiberFunctor X x) F G :=
  rfl

/-- **The fibre of a tensor product is natural** in both arguments. -/
@[reassoc]
lemma fiberTensorIso_hom_naturality {F F' G G' : X.Modules} (φ : F ⟶ F') (ψ : G ⟶ G') (x : X) :
    (fiberTensorIso F G x).hom ≫ (fiberMap φ x ⊗ₘ fiberMap ψ x) =
      fiberMap (φ ⊗ₘ ψ) x ≫ (fiberTensorIso F' G' x).hom :=
  Functor.OplaxMonoidal.δ_natural (fiberFunctor X x) φ ψ

/-- **The fibre of the tensor unit** is `κ(x)`. -/
noncomputable def fiberTensorUnitIso (X : Scheme.{u}) (x : X) :
    (𝟙_ X.Modules).fiber x ≅ 𝟙_ (ModuleCat (X.residueField x)) :=
  (Functor.Monoidal.εIso (fiberFunctor X x)).symm

@[simp]
lemma fiberTensorUnitIso_hom (X : Scheme.{u}) (x : X) :
    (fiberTensorUnitIso X x).hom = Functor.OplaxMonoidal.η (fiberFunctor X x) :=
  rfl

@[simp]
lemma fiberTensorUnitIso_inv (X : Scheme.{u}) (x : X) :
    (fiberTensorUnitIso X x).inv = Functor.LaxMonoidal.ε (fiberFunctor X x) :=
  rfl

/-- **The fibre of the structure sheaf** at `x` is the residue field `κ(x)`. This is
`fiberTensorUnitIso` written for `SheafOfModules.unit`, the free `𝒪ₓ`-module of rank one, rather
than for the tensor unit. -/
noncomputable def fiberUnitIso (X : Scheme.{u}) (x : X) :
    fiber (X := X) (SheafOfModules.unit X.ringCatSheaf) x ≅
      ModuleCat.of (X.residueField x) (X.residueField x) :=
  (fiberFunctor X x).mapIso (SheafOfModules.tensorUnitIso X.sheaf).symm ≪≫
    fiberTensorUnitIso X x

/-- **The fibre of the structure sheaf is one-dimensional.** -/
@[simp]
theorem finrank_fiber_structureModules (X : Scheme.{u}) (x : X) :
    Module.finrank (X.residueField x) (fiber X.structureModules x) = 1 := by
  rw [(fiberUnitIso X x).toLinearEquiv.finrank_eq, Module.finrank_self]

instance finiteDimensional_fiber_structureModules (X : Scheme.{u}) (x : X) :
    FiniteDimensional (X.residueField x) (fiber X.structureModules x) :=
  Module.finite_of_finrank_pos (by simp)

instance nontrivial_fiber_structureModules (X : Scheme.{u}) (x : X) :
    Nontrivial (fiber X.structureModules x) :=
  Module.nontrivial_of_finrank_pos (R := X.residueField x) (by simp)

/-- **The fibre of the structure sheaf is spanned by the image of the unit function.** This is
the fibrewise analogue of `AlgebraicGeometry.Scheme.Modules.span_germ_oneSection`. -/
lemma span_fiberMk_oneSection (X : Scheme.{u}) (x : X) :
    Submodule.span (X.residueField x) {fiberMk X.structureModules x (oneSection X ⊤)} = ⊤ := by
  have hv : fiberMk X.structureModules x (oneSection X ⊤) ≠ 0 :=
    fiberMk_unit_ne_zero_of_isUnit isUnit_one x
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [finrank_span_singleton hv, finrank_fiber_structureModules]

/-- **The fibre of multiplication by a global function is multiplication by its value**: the
fibre at `x` of the endomorphism `· a` of the structure sheaf acts on `𝒪ₓ(x) = κ(x)` as the
value `a(x)`. -/
lemma fiberMap_homOfSectionTop_apply (X : Scheme.{u}) (a : Γ(X, ⊤)) (x : X)
    (v : fiber X.structureModules x) :
    fiberMap (homOfSectionTop X.structureModules a) x v = X.Γevaluation x a • v := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1
    ((span_fiberMk_oneSection X x).ge (Submodule.mem_top (x := v)))
  have hsm : fiberMap (homOfSectionTop X.structureModules a) x
      (c • fiberMk X.structureModules x (oneSection X ⊤)) =
      c • fiberMap (homOfSectionTop X.structureModules a) x
        (fiberMk X.structureModules x (oneSection X ⊤)) :=
    (fiberMap (homOfSectionTop X.structureModules a) x).hom.map_smul c _
  rw [hsm, fiberMap_fiberMk, app_homOfSectionTop_oneSection, fiberMk_structureModules_eq_smul,
    smul_comm]

/-- **The fibre of an endomorphism of the structure sheaf vanishes at `x` exactly when the
corresponding global function does.** -/
lemma fiberMap_eq_zero_iff_evaluation_endSection (ψ : X.structureModules ⟶ X.structureModules)
    (x : X) : fiberMap ψ x = 0 ↔ X.Γevaluation x (endSection ψ) = 0 := by
  have happ : fiberMap ψ x (fiberMk X.structureModules x (oneSection X ⊤)) =
      fiberMk X.structureModules x (endSection ψ) := fiberMap_fiberMk ψ x _
  rw [← fiberMk_unit_eq_zero_iff x (endSection ψ)]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← happ, h]
    simp
  · refine ModuleCat.hom_ext (LinearMap.ext_on (span_fiberMk_oneSection X x) ?_)
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    rw [happ, h]
    simp

/-- **The fibre of multiplication by a global function** vanishes at `x` exactly when the
function does. -/
lemma fiberMap_homOfSectionTop_eq_zero_iff (X : Scheme.{u}) (a : Γ(X, ⊤)) (x : X) :
    fiberMap (homOfSectionTop X.structureModules a) x = 0 ↔ X.Γevaluation x a = 0 := by
  rw [fiberMap_eq_zero_iff_evaluation_endSection, endSection_homOfSectionTop]

/-- **The pairing between the fibres of an invertible sheaf and of its inverse.** If `L ⊗ N` is
isomorphic to the structure sheaf, then `L(x) ⊗ N(x)` is isomorphic to `κ(x)`. -/
noncomputable def fiberTensorIsoTensorUnit {L N : X.Modules} (e : L ⊗ N ≅ 𝟙_ X.Modules) (x : X) :
    L.fiber x ⊗ N.fiber x ≅ 𝟙_ (ModuleCat (X.residueField x)) :=
  Functor.Monoidal.mapIsoTensorUnit (fiberFunctor X x) e

/-- **The fibre of the inverse of an invertible sheaf is the dual of the fibre.** If `L ⊗ N` is
isomorphic to the structure sheaf, then `N(x)` is the `κ(x)`-linear dual of `L(x)`. -/
noncomputable def fiberLinearEquivDual {L N : X.Modules} (e : L ⊗ N ≅ 𝟙_ X.Modules) (x : X) :
    N.fiber x ≃ₗ[X.residueField x] Module.Dual (X.residueField x) (L.fiber x) :=
  Module.Invertible.linearEquivDual
    ((β_ (N.fiber x) (L.fiber x) ≪≫ fiberTensorIsoTensorUnit e x).toLinearEquiv)

/-- **The fibre of an invertible sheaf of modules is an invertible `κ(x)`-vector space.** -/
theorem module_invertible_fiber {L : X.Modules} (hL : L.Invertible) (x : X) :
    Module.Invertible (X.residueField x) (L.fiber x) := by
  obtain ⟨N, ⟨e⟩⟩ := (SheafOfModules.invertible_iff_exists (R := X.sheaf)).1 hL
  exact .left (fiberTensorIsoTensorUnit e x).toLinearEquiv

/-- **The fibre of an invertible sheaf of modules is a one-dimensional `κ(x)`-vector space.** -/
theorem finrank_fiber_eq_one {L : X.Modules} (hL : L.Invertible) (x : X) :
    Module.finrank (X.residueField x) (L.fiber x) = 1 :=
  have := module_invertible_fiber hL x
  Module.Invertible.finrank_eq_one _ _

/-- The `Cardinal`-valued version of `finrank_fiber_eq_one`: the fibre of an invertible sheaf of
modules has `Module.rank` equal to one. -/
theorem rank_fiber_eq_one {L : X.Modules} (hL : L.Invertible) (x : X) :
    Module.rank (X.residueField x) (L.fiber x) = 1 :=
  have := module_invertible_fiber hL x
  Module.Invertible.rank_eq_one _ _

/-- **The fibre of an invertible sheaf of modules is a finite-dimensional `κ(x)`-vector
space.** -/
theorem finiteDimensional_fiber {L : X.Modules} (hL : L.Invertible) (x : X) :
    FiniteDimensional (X.residueField x) (L.fiber x) :=
  Module.finite_of_finrank_pos (by simp [finrank_fiber_eq_one hL x])

/-- **The fibre of an invertible sheaf of modules is non-trivial.** -/
theorem nontrivial_fiber {L : X.Modules} (hL : L.Invertible) (x : X) :
    Nontrivial (L.fiber x) :=
  Module.nontrivial_of_finrank_pos (R := X.residueField x)
    (by simp [finrank_fiber_eq_one hL x])

/-- **A non-zero map between the fibres of two line bundles is an isomorphism**: both fibres are
one-dimensional over the residue field. -/
theorem isIso_fiberMap_of_ne_zero {M N : X.Modules} (hM : M.Invertible) (hN : N.Invertible)
    (φ : M ⟶ N) {x : X} (hφ : fiberMap φ x ≠ 0) : IsIso (fiberMap φ x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact LinearMap.bijective_of_ne_zero_of_finrank_eq_one (finrank_fiber_eq_one hM x)
    (finrank_fiber_eq_one hN x) fun hz ↦ hφ (ModuleCat.hom_ext hz)

end AlgebraicGeometry.Scheme.Modules
