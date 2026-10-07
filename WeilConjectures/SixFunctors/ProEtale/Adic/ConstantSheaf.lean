/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.NumberTheory.Padics.Complex
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso

/-!
# The constant `ℓ`-adic sheaf `ℚ̄_ℓ` on the pro-étale site

Let `ℓ` be a prime and `ℚ̄_ℓ = PadicAlgCl ℓ`. The `ℓ`-adic sheaves of the blueprint are
modules over the pro-étale sheaf of *continuous* `ℓ`-adic functions, not over the constant
sheaf of the discrete ring `ℚ̄_ℓ` (Bhatt–Scholze, *The pro-étale topology for schemes*, §6.8).
For a finite extension `E` of `ℚ_ℓ` this is the sheaf `E_X : U ↦ C(U, E)`; for `ℚ̄_ℓ`, the union
of the finite extensions, it is the sheaf `ℚ̄_ℓ,X` whose sections over a quasi-compact `U` are
`colim_E C(U, E)`: the continuous functions `U → ℚ̄_ℓ` whose values span a finite-dimensional
`ℚ_ℓ`-subspace. A finite-dimensional `ℚ_ℓ`-subspace of `ℚ̄_ℓ` carries its unique Hausdorff
vector space topology as subspace topology, so continuity may be tested in `ℚ̄_ℓ`.

Since this condition is local, `ℚ̄_ℓ,X(U)` is, for an arbitrary scheme `U`, the module
`PadicAlgCl.locallyFiniteFunctions ℓ U` of continuous functions `f : U → ℚ̄_ℓ` such that every
point has a neighbourhood on which the values of `f` span a finite-dimensional
`ℚ_ℓ`-subspace. This defines a presheaf `AlgebraicGeometry.adicFunctionsPresheaf` on all
schemes, a sheaf for the fpqc topology, and `AlgebraicGeometry.ProEtale.adicConstantSheaf ℓ X`
is its restriction to the small pro-étale site of `X`, a sheaf of modules over `ℚ̄_ℓ`.

It is *not* the constant sheaf of the discrete module `ℚ̄_ℓ`, whose sections are the locally
constant functions: that sheaf is of étale origin, and the constructible sheaves of étale origin
with coefficients in a field of characteristic zero all vanish.

## Main definitions

- `AlgebraicGeometry.WeilCoefficients`: the coefficient category of `ℓ`-adic pro-étale sheaves,
  modules over `ℚ̄_ℓ`, lifted to the universe of the sites.
- `PadicAlgCl.locallyFiniteFunctions`: continuous functions with locally finite-dimensional
  `ℚ_ℓ`-span of values.
- `AlgebraicGeometry.adicFunctionsPresheaf`: the presheaf `U ↦ ℚ̄_ℓ,X(U)` on all schemes.
- `AlgebraicGeometry.ProEtale.adicConstantSheaf`: the constant `ℓ`-adic sheaf `ℚ̄_ℓ,X`.
- `AlgebraicGeometry.ProEtale.adicConstantSheafLowerStarIso`: for an isomorphism `e : X ≅ Y`,
  `e_* ℚ̄_ℓ,X ≅ ℚ̄_ℓ,Y`.

## Main results

- `AlgebraicGeometry.ProEtale.not_isZero_adicConstantSheaf`: `ℚ̄_ℓ,X` is nonzero on a nonempty
  scheme.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite Topology

section LocallyFiniteFunctions

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (T : Type*) [TopologicalSpace T]

/-- The continuous functions `f : T → ℚ̄_ℓ` whose values span, locally on `T`, a
finite-dimensional `ℚ_ℓ`-subspace. For compact `T` these are the continuous functions with
values in a finite-dimensional `ℚ_ℓ`-subspace, the sections of the constant `ℓ`-adic sheaf
`ℚ̄_ℓ = colim_E E` over a quasi-compact scheme. -/
noncomputable def locallyFiniteFunctions : Submodule (PadicAlgCl l) C(T, PadicAlgCl l) where
  carrier := {f | ∀ x, ∃ U ∈ 𝓝 x, FiniteDimensional ℚ_[l] (Submodule.span ℚ_[l] (f '' U))}
  zero_mem' x := by
    refine ⟨Set.univ, Filter.univ_mem, Submodule.finiteDimensional_of_le (S₂ := ⊥) ?_⟩
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, -, rfl⟩
    simp
  add_mem' {f g} hf hg x := by
    obtain ⟨U, hU, hfU⟩ := hf x
    obtain ⟨V, hV, hgV⟩ := hg x
    refine ⟨U ∩ V, Filter.inter_mem hU hV, Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℚ_[l] (f '' U) ⊔ Submodule.span ℚ_[l] (g '' V)) ?_⟩
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨y, hy.1, rfl⟩)
      (Submodule.subset_span ⟨y, hy.2, rfl⟩)
  smul_mem' c f hf x := by
    obtain ⟨U, hU, hfU⟩ := hf x
    refine ⟨U, hU, Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℚ_[l] (f '' U)).map (LinearMap.mulLeft ℚ_[l] c)) ?_⟩
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨f y, Submodule.subset_span ⟨y, hy, rfl⟩, rfl⟩

variable {l T}

lemma mem_locallyFiniteFunctions_iff (f : C(T, PadicAlgCl l)) :
    f ∈ locallyFiniteFunctions l T ↔
      ∀ x, ∃ U ∈ 𝓝 x, FiniteDimensional ℚ_[l] (Submodule.span ℚ_[l] (f '' U)) :=
  Iff.rfl

/-- The constant functions are locally finite: their values span a line. -/
lemma const_mem_locallyFiniteFunctions (c : PadicAlgCl l) :
    ContinuousMap.const T c ∈ locallyFiniteFunctions l T := by
  intro x
  refine ⟨Set.univ, Filter.univ_mem, Submodule.finiteDimensional_of_le
    (S₂ := Submodule.span ℚ_[l] {c}) (Submodule.span_mono ?_)⟩
  rintro _ ⟨y, -, rfl⟩
  rfl

variable {T' : Type*} [TopologicalSpace T']

/-- Precomposition with a continuous map preserves local finiteness. -/
lemma comp_mem_locallyFiniteFunctions {f : C(T, PadicAlgCl l)}
    (hf : f ∈ locallyFiniteFunctions l T) (g : C(T', T)) :
    f.comp g ∈ locallyFiniteFunctions l T' := by
  intro x
  obtain ⟨U, hU, hfU⟩ := hf (g x)
  refine ⟨g ⁻¹' U, g.continuous.continuousAt.preimage_mem_nhds hU,
    Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ_[l] (f '' U))
      (Submodule.span_mono ?_)⟩
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨g y, hy, rfl⟩

variable (l) in
/-- Precomposition with a continuous map `g : T' → T`, as a `ℚ̄_ℓ`-linear map of locally
finite functions. -/
noncomputable def locallyFiniteFunctionsComp (g : C(T', T)) :
    locallyFiniteFunctions l T →ₗ[PadicAlgCl l] locallyFiniteFunctions l T' where
  toFun f := ⟨f.1.comp g, comp_mem_locallyFiniteFunctions f.2 g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma locallyFiniteFunctionsComp_apply_coe (g : C(T', T)) (f : locallyFiniteFunctions l T) :
    ((locallyFiniteFunctionsComp l g f : locallyFiniteFunctions l T') :
      C(T', PadicAlgCl l)) = (f : C(T, PadicAlgCl l)).comp g :=
  rfl

end PadicAlgCl

end LocallyFiniteFunctions

namespace AlgebraicGeometry

/-- The coefficients of `ℓ`-adic pro-étale sheaves: modules over `ℚ̄_ℓ`, lifted to
`Type (u + 1)`, the universe of the `Hom`-types of sheaves on the sites of `Scheme.{u}`. The
`ℓ`-adic topology does not enter the coefficient category: it enters through the constant sheaf
`AlgebraicGeometry.ProEtale.adicConstantSheaf`. -/
abbrev WeilCoefficients (l : ℕ) [Fact l.Prime] : Type (u + 2) :=
  ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l))

namespace WeilCoefficients

variable (l : ℕ) [Fact l.Prime]

/-- The underlying `ℚ̄_ℓ`-vector space of a module over `ULift ℚ̄_ℓ`, by restriction of scalars
along `ℚ̄_ℓ ≃ ULift ℚ̄_ℓ`. -/
noncomputable abbrev toModuleCat :
    WeilCoefficients.{u} l ⥤ ModuleCat.{u + 1} (PadicAlgCl l) :=
  ModuleCat.restrictScalars (ULift.ringEquiv (R := PadicAlgCl l)).symm.toRingHom

variable {l}

/-- An isomorphism of modules over `ULift ℚ̄_ℓ` as a `ℚ̄_ℓ`-linear isomorphism of the
underlying `ℚ̄_ℓ`-vector spaces. -/
noncomputable def linearEquivOfIso {M N : WeilCoefficients.{u} l} (e : M ≅ N) :
    (toModuleCat l).obj M ≃ₗ[PadicAlgCl l] (toModuleCat l).obj N :=
  ((toModuleCat l).mapIso e).toLinearEquiv

/-- A `ℚ̄_ℓ`-linear map, lifted to a `ULift ℚ̄_ℓ`-linear map of the universe lifts. -/
noncomputable def uliftLinearMap {M N : Type*} [AddCommGroup M] [Module (PadicAlgCl l) M]
    [AddCommGroup N] [Module (PadicAlgCl l) N] (φ : M →ₗ[PadicAlgCl l] N) :
    ULift.{u + 1} M →ₗ[ULift.{u + 1} (PadicAlgCl l)] ULift.{u + 1} N where
  toFun x := ULift.up (φ x.down)
  map_add' x y := congrArg ULift.up (φ.map_add x.down y.down)
  map_smul' c x := congrArg ULift.up (φ.map_smul c.down x.down)

end WeilCoefficients

variable (l : ℕ) [Fact l.Prime]

open PadicAlgCl WeilCoefficients

/-- The presheaf `U ↦ ℚ̄_ℓ,U(U)` on all schemes: the continuous functions `U → ℚ̄_ℓ` whose
values locally span finite-dimensional `ℚ_ℓ`-subspaces, with restriction given by
precomposition with the underlying continuous maps. -/
@[simps]
noncomputable def adicFunctionsPresheaf : Scheme.{u}ᵒᵖ ⥤ WeilCoefficients.{u} l where
  obj U := ModuleCat.of _ (ULift.{u + 1} (locallyFiniteFunctions l U.unop))
  map f := ModuleCat.ofHom (uliftLinearMap (locallyFiniteFunctionsComp l f.unop.base.hom))

/-- The presheaf of locally finite continuous `ℓ`-adic functions is a sheaf for the fpqc
topology. It is a subpresheaf of the fpqc sheaf `U ↦ C(U, ℚ̄_ℓ)`
(`AlgebraicGeometry.isSheaf_fpqcTopology_continuousMapPresheaf`), defined by a condition which
descends along fpqc covers: an fpqc cover is quasi-compact, so a continuous function on an
affine open which is locally finite on the members of a cover takes its values in the span of
finitely many finite-dimensional subspaces. -/
theorem isSheaf_fpqcTopology_adicFunctionsPresheaf :
    Presheaf.IsSheaf Scheme.fpqcTopology (adicFunctionsPresheaf.{u} l) :=
  sorry

namespace ProEtale

/-- The constant `ℓ`-adic sheaf `ℚ̄_ℓ,X` on the small pro-étale site of `X`: the sections over a
weakly étale `U → X` are the continuous functions `U → ℚ̄_ℓ` whose values locally span
finite-dimensional `ℚ_ℓ`-subspaces (Bhatt–Scholze, §6.8). -/
noncomputable def adicConstantSheaf (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l) :=
  ((Scheme.ProEt.forget X ⋙ Over.forget _).sheafPushforwardContinuous _ _
    Scheme.proetaleTopology).obj
    ⟨adicFunctionsPresheaf l, .of_le Scheme.proetaleTopology_le_fpqcTopology <|
      isSheaf_fpqcTopology_adicFunctionsPresheaf l⟩

/-- The sections of `ℚ̄_ℓ,X` over `U` are the locally finite continuous functions on `U`. -/
lemma adicConstantSheaf_obj_obj (X : Scheme.{u}) (U : X.ProEt) :
    (adicConstantSheaf l X).obj.obj (op U) =
      ModuleCat.of _ (ULift.{u + 1} (locallyFiniteFunctions l U.left)) :=
  rfl

/-- Base change along an isomorphism `g : X ⟶ Y` does not change the underlying schemes of the
objects of the pro-étale site, up to the canonical isomorphisms `V ×_Y X ≅ V`. -/
noncomputable def overPullbackForgetIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    MorphismProperty.Over.pullback @WeaklyEtale ⊤ g ⋙ Scheme.ProEt.forget X ⋙ Over.forget X ≅
      Scheme.ProEt.forget Y ⋙ Over.forget Y :=
  NatIso.ofComponents (fun V ↦ asIso (pullback.fst V.hom g)) fun f ↦ by
    simp

/-- The pushforward of the constant `ℓ`-adic sheaf along an isomorphism `e : X ≅ Y` is the
constant `ℓ`-adic sheaf: its sections over `V → Y` are the locally finite functions on
`V ×_Y X`, which the canonical isomorphism `V ×_Y X ≅ V` identifies with those on `V`. -/
noncomputable def adicConstantSheafLowerStarIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    (e.hom)_*[WeilCoefficients.{u} l].obj (adicConstantSheaf l X) ≅ adicConstantSheaf l Y :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (show _ ≅ _ from
    (Functor.isoWhiskerRight (NatIso.op (overPullbackForgetIso e.hom))
      (adicFunctionsPresheaf l)).symm)

/-- The constant `ℓ`-adic sheaf on a nonempty scheme is nonzero: the constant function `1` is a
nonzero global section. -/
theorem not_isZero_adicConstantSheaf (X : Scheme.{u}) [Nonempty X] :
    ¬ IsZero (adicConstantSheaf l X) := by
  intro h
  -- the sections over the terminal object `X` of the pro-étale site
  let T : X.ProEt := Scheme.ProEt.mk (𝟙 X)
  have h' : IsZero ((adicConstantSheaf l X).obj.obj (op T)) :=
    ((evaluation _ _).obj (op T)).map_isZero ((sheafToPresheaf _ _).map_isZero h)
  have h1 : (ULift.up ⟨ContinuousMap.const _ 1, const_mem_locallyFiniteFunctions 1⟩ :
      ULift.{u + 1} (locallyFiniteFunctions l T.left)) = 0 :=
    (ModuleCat.isZero_iff_subsingleton.1 h').elim _ _
  obtain ⟨x⟩ := ‹Nonempty X›
  have := congrArg (fun f : ULift.{u + 1} (locallyFiniteFunctions l T.left) ↦
    (f.down : C(T.left, PadicAlgCl l)) x) h1
  simp at this

end ProEtale

end AlgebraicGeometry
