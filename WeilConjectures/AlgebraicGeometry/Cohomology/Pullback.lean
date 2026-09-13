/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.AlgebraicGeometry.Cohomology.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Mathlib.Topology.Sheaves.Abelian

/-!
# The pullback map on the cohomology of a sheaf of modules

Let `f : X ⟶ Y` be a morphism of schemes and let `G` be a sheaf of `𝒪_Y`-modules. This file
constructs the comparison map

`H^n(Y, G) ⟶ H^n(X, f^* G)`,

which is semilinear over the ring homomorphism `f.appTop : Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`.

Cohomology of an abelian sheaf is an `Ext`-group out of the constant sheaf `ℤ`, so the map
is assembled from three ingredients:

* the pullback functor `f^{-1}` on sheaves of abelian groups is exact, hence induces a map
  `Ext^n(ℤ_Y, G^♭) ⟶ Ext^n(f^{-1} ℤ_Y, f^{-1} G^♭)` by
  `CategoryTheory.Abelian.Ext.mapExactFunctor`;
* `f^{-1}` takes the constant sheaf `ℤ_Y` to the constant sheaf `ℤ_X`
  (`AlgebraicGeometry.Scheme.Hom.pullbackAbConstantSheafIso`);
* the comparison map `f^{-1}(G^♭) ⟶ (f^* G)^♭` between the pullback of the underlying
  abelian sheaf of `G` and the underlying abelian sheaf of the pullback of `G` as a sheaf
  of modules (`AlgebraicGeometry.Scheme.Modules.pullbackAbComparison`); it is the mate of
  the unit of the adjunction `f^* ⊣ f_*` for sheaves of modules.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.pullbackAb`, `AlgebraicGeometry.Scheme.Hom.pushforwardAb` —
  the pullback and the pushforward of sheaves of abelian groups along `f`.
* `AlgebraicGeometry.Scheme.Modules.pullbackAbComparison` — the comparison map
  `f^{-1}(G^♭) ⟶ (f^* G)^♭`.
* `AlgebraicGeometry.Scheme.Modules.H.pullbackMap` — the pullback map
  `H^n(Y, G) ⟶ H^n(X, f^* G)`, semilinear over `f.appTop`.
* `AlgebraicGeometry.Scheme.Modules.H.structurePullbackMap` — the composite of the pullback
  map with the identification `f^* 𝒪_Y ≅ 𝒪_X`, that is the pullback map
  `H^n(Y, 𝒪_Y) ⟶ H^n(X, 𝒪_X)` on the cohomology of the structure sheaves.
* `AlgebraicGeometry.Scheme.Modules.H.pullbackMapOver` and
  `AlgebraicGeometry.Scheme.Modules.H.structurePullbackMapOver` — the same two maps for a
  morphism of schemes over `Spec R`, where they are `R`-linear.

## TODO

The identity and composition laws for `H.pullbackMap` (`f = 𝟙` gives the identity, and
`(f ≫ g)^*` is the composite modulo the canonical isomorphism `(f ≫ g)^* ≅ f^* ∘ g^*`)
require `CategoryTheory.Abelian.Ext.mapExactFunctor` to be functorial in the exact functor,
which Mathlib does not provide.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace Abelian

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The pushforward of sheaves of abelian groups along a morphism of schemes. -/
noncomputable abbrev pushforwardAb :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
  (Opens.map f.base).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- The pullback of sheaves of abelian groups along a morphism of schemes. -/
noncomputable abbrev pullbackAb :
    Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (Opens.map f.base).sheafPullback AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- The pullback of sheaves of abelian groups is left adjoint to the pushforward. -/
noncomputable abbrev pullbackPushforwardAbAdjunction : f.pullbackAb ⊣ f.pushforwardAb :=
  (Opens.map f.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- The pullback of the constant sheaf with values in an abelian group `A` is the constant
sheaf with values in `A`. -/
noncomputable def pullbackAbConstantSheafIso (A : AddCommGrpCat.{u}) :
    f.pullbackAb.obj ((constantSheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}).obj A) ≅
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A :=
  ((Opens.map f.base).constantSheafsheafPullbackIso AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
    isTerminalTop isTerminalTop).app A

end Scheme.Hom

namespace Scheme.Modules

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### Multiplication by a global section and the pushforward -/

/-- Multiplication by `r : Γ(Y, 𝒪_Y)` on the pushforward of a sheaf of modules `N` on `X`
is the pushforward of multiplication by `f^# r : Γ(X, 𝒪_X)` on `N`. -/
lemma smulEnd_pushforward (N : X.Modules) (r : Γ(Y, ⊤)) :
    smulEnd ((pushforward f).obj N) r = (pushforward f).map (smulEnd N (f.appTop r)) := by
  have h : ∀ U : Y.Opens, ConcreteCategory.hom (f.app U)
        (ConcreteCategory.hom (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) r) =
      ConcreteCategory.hom (X.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ U ≤ ⊤)).op)
        (ConcreteCategory.hom f.appTop r) := fun U ↦
    ConcreteCategory.congr_hom (f.naturality (homOfLE (le_top : U ≤ ⊤)).op) r
  ext U x
  exact congrArg (fun s ↦ s • (id x : Γ(N, f ⁻¹ᵁ U))) (h U)

/-! ### The comparison map -/

/-- Forgetting a morphism of sheaves of modules on `X` to abelian sheaves and pushing it
forward to `Y` is the same as pushing it forward and then forgetting. -/
lemma pushforwardAb_map_toSheafAb_map {M N : X.Modules} (φ : M ⟶ N) :
    f.pushforwardAb.map ((toSheafAb X).map φ) = (toSheafAb Y).map ((pushforward f).map φ) :=
  rfl

/-- The comparison map `f^{-1}(G^♭) ⟶ (f^* G)^♭` between the pullback of the underlying
abelian sheaf of a sheaf of modules `G` on `Y` and the underlying abelian sheaf of the
pullback of `G`. It is the mate of the unit of the adjunction `f^* ⊣ f_*`. -/
noncomputable def pullbackAbComparison :
    toSheafAb Y ⋙ f.pullbackAb ⟶ pullback f ⋙ toSheafAb X where
  app G := ((f.pullbackPushforwardAbAdjunction.homEquiv _ _).symm
    ((toSheafAb Y).map ((pullbackPushforwardAdjunction f).unit.app G)))
  naturality G G' φ := by
    dsimp
    rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm]
    congr 1
    rw [← Functor.map_comp]
    exact congrArg _ ((pullbackPushforwardAdjunction f).unit.naturality φ)

@[reassoc]
lemma pullbackAbComparison_naturality {G G' : Y.Modules} (φ : G ⟶ G') :
    f.pullbackAb.map ((toSheafAb Y).map φ) ≫ (pullbackAbComparison f).app G' =
      (pullbackAbComparison f).app G ≫ (toSheafAb X).map ((pullback f).map φ) :=
  (pullbackAbComparison f).naturality φ

/-- The comparison map `f^{-1}(G^♭) ⟶ (f^* G)^♭` is semilinear: multiplication by
`r : Γ(Y, 𝒪_Y)` on the source corresponds to multiplication by `f^# r` on the target. -/
lemma pullbackAb_map_smulEnd_comp_pullbackAbComparison (G : Y.Modules) (r : Γ(Y, ⊤)) :
    f.pullbackAb.map ((toSheafAb Y).map (smulEnd G r)) ≫ (pullbackAbComparison f).app G =
      (pullbackAbComparison f).app G ≫
        (toSheafAb X).map (smulEnd ((pullback f).obj G) (f.appTop r)) := by
  dsimp [pullbackAbComparison]
  rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm,
    pushforwardAb_map_toSheafAb_map]
  congr 1
  rw [← Functor.map_comp, ← Functor.map_comp, smulEnd_comp, smulEnd_pushforward]

/-! ### The pullback map on cohomology -/

/-- The pullback map `H^n(Y, G) ⟶ H^n(X, f^* G)` as a map of additive groups. See
`AlgebraicGeometry.Scheme.Modules.H.pullbackMap` for the semilinear refinement. -/
noncomputable def H.pullbackAddHom (G : Y.Modules) (n : ℕ) :
    G.H n →+ ((pullback f).obj G).H n where
  toFun e := (Ext.mk₀ (f.pullbackAbConstantSheafIso _).inv).comp
    ((e.mapExactFunctor f.pullbackAb).comp
      (Ext.mk₀ ((pullbackAbComparison f).app G)) (add_zero n)) (zero_add n)
  map_zero' := by simp
  map_add' e e' := by simp [Ext.add_comp, Ext.comp_add]

@[simp]
lemma H.pullbackAddHom_apply (G : Y.Modules) (n : ℕ) (e : G.H n) :
    H.pullbackAddHom f G n e = (Ext.mk₀ (f.pullbackAbConstantSheafIso _).inv).comp
      ((e.mapExactFunctor f.pullbackAb).comp
        (Ext.mk₀ ((pullbackAbComparison f).app G)) (add_zero n)) (zero_add n) :=
  rfl

/-- The pullback map on cohomology is semilinear over `f.appTop`. -/
lemma H.pullbackAddHom_smul (G : Y.Modules) (n : ℕ) (r : Γ(Y, ⊤)) (e : G.H n) :
    H.pullbackAddHom f G n (r • e) = f.appTop.hom r • H.pullbackAddHom f G n e := by
  rw [H.smul_def, H.smul_def]
  simp only [H.pullbackAddHom_apply, H.mapAddHom, Sheaf.H.map_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_second_deg_zero,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    pullbackAb_map_smulEnd_comp_pullbackAbComparison]

/-- The pullback map on cohomology is natural in the sheaf of modules. -/
lemma H.pullbackAddHom_map {G G' : Y.Modules} (φ : G ⟶ G') (n : ℕ) (e : G.H n) :
    H.pullbackAddHom f G' n (H.map φ n e) =
      H.map ((pullback f).map φ) n (H.pullbackAddHom f G n e) := by
  simp only [H.map_apply, H.mapAddHom, Sheaf.H.map_apply, H.pullbackAddHom_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_second_deg_zero,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, pullbackAbComparison_naturality]

/-- The pullback map `H^n(Y, G) ⟶ H^n(X, f^* G)` on the cohomology of a sheaf of modules,
semilinear over the ring homomorphism `f.appTop : Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`. -/
noncomputable def H.pullbackMap (G : Y.Modules) (n : ℕ) :
    G.H n →ₛₗ[f.appTop.hom] ((pullback f).obj G).H n where
  toFun := H.pullbackAddHom f G n
  map_add' := (H.pullbackAddHom f G n).map_add
  map_smul' := H.pullbackAddHom_smul f G n

@[simp]
lemma H.pullbackMap_apply (G : Y.Modules) (n : ℕ) (e : G.H n) :
    H.pullbackMap f G n e = H.pullbackAddHom f G n e :=
  rfl

/-- **The pullback map `H^n(Y, 𝒪_Y) ⟶ H^n(X, 𝒪_X)` on the cohomology of the structure sheaves**
attached to a morphism `f : X ⟶ Y` of schemes, semilinear over `f.appTop`:

```
  H^n(Y, 𝒪_Y) ──pullbackMap──▶ H^n(X, f^* 𝒪_Y) ──map (pullbackUnitIso f).hom──▶ H^n(X, 𝒪_X)
```

The second map is induced by the identification `f^* 𝒪_Y ≅ 𝒪_X` of
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`. -/
noncomputable def H.structurePullbackMap (n : ℕ) :
    Y.structureModules.H n →ₛₗ[f.appTop.hom] X.structureModules.H n :=
  (H.map (pullbackUnitIso f).hom n).comp (H.pullbackMap f Y.structureModules n)

@[simp]
lemma H.structurePullbackMap_apply (n : ℕ) (e : Y.structureModules.H n) :
    H.structurePullbackMap f n e =
      H.map (pullbackUnitIso f).hom n (H.pullbackAddHom f Y.structureModules n e) :=
  rfl

end

/-! ### The pullback map for schemes over a base ring -/

section OverBase

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Y)
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [f.IsOver (Spec (.of R))]

/-- The pullback map on cohomology is `R`-linear for a morphism of schemes over `Spec R`. -/
lemma H.pullbackAddHom_smul_over (G : Y.Modules) (n : ℕ) (r : R) (e : G.H n) :
    H.pullbackAddHom f G n (r • e) = r • H.pullbackAddHom f G n e := by
  rw [H.smul_over_def R Y, H.pullbackAddHom_smul, Scheme.appTop_overRingHom R f,
    ← H.smul_over_def R X]

/-- The pullback map `H^n(Y, G) ⟶ H^n(X, f^* G)` on the cohomology of a sheaf of modules, as an
`R`-linear map for a morphism `f : X ⟶ Y` of schemes over `Spec R`. -/
noncomputable def H.pullbackMapOver (G : Y.Modules) (n : ℕ) :
    G.H n →ₗ[R] ((pullback f).obj G).H n where
  toFun := H.pullbackAddHom f G n
  map_add' := (H.pullbackAddHom f G n).map_add
  map_smul' := H.pullbackAddHom_smul_over R f G n

@[simp]
lemma H.pullbackMapOver_apply (G : Y.Modules) (n : ℕ) (e : G.H n) :
    H.pullbackMapOver R f G n e = H.pullbackAddHom f G n e :=
  rfl

/-- **The pullback map on the cohomology of the structure sheaves, as an `R`-linear map**, for a
morphism `f : X ⟶ Y` of schemes over `Spec R`:

```
  H^n(Y, 𝒪_Y) ──pullbackMapOver──▶ H^n(X, f^* 𝒪_Y) ──mapOver (pullbackUnitIso f).hom──▶ H^n(X, 𝒪_X)
```

This is the restriction of scalars to `R` of
`AlgebraicGeometry.Scheme.Modules.H.structurePullbackMap`, which is semilinear over
`f.appTop`. -/
noncomputable def H.structurePullbackMapOver (n : ℕ) :
    Y.structureModules.H n →ₗ[R] X.structureModules.H n :=
  (H.mapOver R (pullbackUnitIso f).hom n).comp (H.pullbackMapOver R f Y.structureModules n)

@[simp]
lemma H.structurePullbackMapOver_apply (n : ℕ) (e : Y.structureModules.H n) :
    H.structurePullbackMapOver R f n e = H.structurePullbackMap f n e :=
  rfl

end OverBase

end Scheme.Modules

end AlgebraicGeometry
