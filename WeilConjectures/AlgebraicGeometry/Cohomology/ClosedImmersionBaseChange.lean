/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Cohomology.PullbackComp

/-!
# Cohomology along a closed immersion commutes with base change

Let

```
  W'₀ ──i'₀──▶ W'₁
   │ g₀         │ g
   ▼            ▼
  W₀  ──i₀────▶ W₁
```

be a commutative square of schemes in which `i₀` and `i'₀` are closed immersions, and let `F`
be a sheaf of `𝒪_{W₀}`-modules. Cohomology is invariant under pushforward along a closed
immersion (`AlgebraicGeometry.Scheme.Modules.H.pushforwardMap`) and it has a pullback map along
an arbitrary morphism (`AlgebraicGeometry.Scheme.Modules.H.pullbackAddHom`). This file proves
that the two fit into a commuting square

```
  H^n(W₁, i₀_* F) ────pullbackMap g───▶ H^n(W'₁, g^*(i₀_* F))
        │                                        │ H.map (base change)
        │ pushforwardMap i₀                      ▼
        │                              H^n(W'₁, i'₀_*(g₀^* F))
        ▼                                        │ pushforwardMap i'₀
  H^n(W₀, F) ────────pullbackMap g₀────▶ H^n(W'₀, g₀^* F)
```

where the vertical comparison is `AlgebraicGeometry.Scheme.Modules.baseChange`, the base change
morphism `g^* i₀_* F ⟶ i'₀_* g₀^* F` attached to the square. **No cartesianness is needed**: the
statement holds for any commutative square whose horizontal arrows are closed immersions, the
base change morphism being the mate of the comparison of pullbacks.

The statement is given as a pointwise identity of cohomology classes rather than as an equality
of additive maps, because `H.pushforwardMap` is semilinear over `i.appTop` rather than additive
over a fixed ring, so the two composites are not maps of modules over one and the same ring.

## Strategy

Both composites are pullbacks of `y` along the two factorisations `g₀ ≫ i₀ = i'₀ ≫ g` of the
same morphism `W'₀ ⟶ W₁`, followed by a morphism of abelian sheaves in degree `0`. Concretely,
`H.pushforwardMap` is the *pullback* map on the cohomology of the underlying abelian sheaf
followed by the counit of the adjunction `i^{-1} ⊣ i_♭` (`H.pushforwardMap_eq`), and
`H.pullbackAddHom` is the pullback map followed by the comparison map
(`H.pullbackAddHom_eq`). So the composition law for the pullback map,
`AlgebraicGeometry.Scheme.Hom.H.pullbackAddHom_comp`, reduces the square to the identity
`Scheme.Modules.baseChange_key` between morphisms of abelian sheaves in degree `0`, which is in
turn deduced from the mate identity `Scheme.Modules.map_baseChange_comp_counit` satisfied by the
base change morphism.

Note that the pullback map, not the pushforward map, is the one that composes: this is what
makes the argument work with only the *functoriality* of `Ext.mapExactFunctor` in the exact
functor. Formulating the square with `H.pushforwardAddEquiv` instead would require comparing
`g^{-1} i_{0♭}` with `i'_{0♭} g_0^{-1}`, which is base change for the pushforward of abelian
sheaves and is genuinely harder.

## Main statements

* `AlgebraicGeometry.Scheme.Modules.H.pushforwardMap_eq` and
  `AlgebraicGeometry.Scheme.Modules.H.pullbackAddHom_eq` — the two maps on cohomology, factored
  through the pullback map on the cohomology of the underlying abelian sheaf.
* `AlgebraicGeometry.Scheme.Modules.pullbackAbComparison_comp` — the comparison map between the
  two notions of pullback is compatible with the composition of morphisms of schemes.
* `AlgebraicGeometry.Scheme.Modules.baseChange_key` — the identity of degree-zero morphisms of
  abelian sheaves behind the base change square.
* `AlgebraicGeometry.Scheme.Modules.H.pushforwardMap_pullbackAddHom` — **cohomology along a
  closed immersion commutes with base change**, and
  `AlgebraicGeometry.Scheme.Modules.H.pullbackAddHom_pushforwardAddEquiv`, the equivalent form
  using `H.pushforwardAddEquiv` instead of its inverse `H.pushforwardMap`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace Abelian

namespace AlgebraicGeometry.Scheme.Modules

variable {W₀ W₁ : Scheme.{u}} (i : W₀ ⟶ W₁) [IsClosedImmersion i] (F : W₀.Modules) (n : ℕ)

attribute [local instance] Scheme.Hom.preservesFiniteColimits_pushforwardAb

/-- `H.pushforwardMap` is the pullback map on the cohomology of the underlying abelian sheaf,
followed by the counit of the adjunction `i^{-1} ⊣ i_♭`. -/
lemma H.pushforwardMap_eq (y : ((pushforward i).obj F).H n) :
    H.pushforwardMap i F n y =
      (Scheme.Hom.H.pullbackAddHom i ((toSheafAb W₁).obj ((pushforward i).obj F)) n y).comp
        (Ext.mk₀ (i.pullbackPushforwardAbAdjunction.counit.app ((toSheafAb W₀).obj F)))
        (add_zero n) := by
  simp only [H.pushforwardMap_apply, H.pushforwardAddEquiv, AddEquiv.symm_trans_apply,
    Ext.precompAddEquiv_symm_apply, Scheme.Hom.H.pullbackAddHom_apply,
    Ext.comp_assoc_of_third_deg_zero]
  refine congrArg (fun z ↦ (Ext.mk₀ (i.pullbackAbConstantSheafIso
      (AddCommGrpCat.of (ULift ℤ))).inv).comp z (zero_add n)) ?_
  exact i.pullbackPushforwardAbAdjunction.extAddEquiv_symm_apply
    ((constantSheaf (Opens.grothendieckTopology W₁) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))) ((toSheafAb W₀).obj F) n y

/-- The pullback map on the cohomology of a sheaf of modules is the pullback map on the
cohomology of the underlying abelian sheaf, followed by the comparison map. -/
lemma H.pullbackAddHom_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Y.Modules) (m : ℕ) (e : G.H m) :
    H.pullbackAddHom f G m e =
      (Scheme.Hom.H.pullbackAddHom f ((toSheafAb Y).obj G) m e).comp
        (Ext.mk₀ ((pullbackAbComparison f).app G)) (add_zero m) := by
  simp only [H.pullbackAddHom_apply, Scheme.Hom.H.pullbackAddHom_apply,
    Ext.comp_assoc_of_third_deg_zero]

section Comparison

variable {X Y Z : Scheme.{u}}

/-- The counit of the adjunction `f^{-1} ⊣ f_♭` for abelian sheaves is the comparison map
followed by the counit of the adjunction `f^* ⊣ f_*` for sheaves of modules. -/
lemma counit_app_toSheafAb (f : X ⟶ Y) (M : X.Modules) :
    f.pullbackPushforwardAbAdjunction.counit.app ((toSheafAb X).obj M) =
      (pullbackAbComparison f).app ((pushforward f).obj M) ≫
        (toSheafAb X).map ((pullbackPushforwardAdjunction f).counit.app M) := by
  simp only [pullbackAbComparison]
  rw [← Adjunction.homEquiv_naturality_right_symm, pushforwardAb_map_toSheafAb_map,
    ← Functor.map_comp, Adjunction.right_triangle_components]
  simp [Adjunction.homEquiv_counit]

/-- The comparison map `f^{-1}(G^♭) ⟶ (f^* G)^♭` is the transpose of the unit of the
adjunction `f^* ⊣ f_*` for sheaves of modules. -/
lemma unit_comp_map_pullbackAbComparison (f : X ⟶ Y) (G : Y.Modules) :
    f.pullbackPushforwardAbAdjunction.unit.app ((toSheafAb Y).obj G) ≫
        f.pushforwardAb.map ((pullbackAbComparison f).app G) =
      (toSheafAb Y).map ((pullbackPushforwardAdjunction f).unit.app G) :=
  Equiv.apply_symm_apply (f.pullbackPushforwardAbAdjunction.homEquiv _ _) _

/-- The variant of `unit_comp_map_pullbackAbComparison` with a morphism of sheaves of modules
appended. -/
lemma unit_comp_map_pullbackAbComparison_comp (f : X ⟶ Y) (M : Y.Modules) {N : X.Modules}
    (ψ : (pullback f).obj M ⟶ N) :
    f.pullbackPushforwardAbAdjunction.unit.app ((toSheafAb Y).obj M) ≫
        f.pushforwardAb.map ((pullbackAbComparison f).app M ≫ (toSheafAb X).map ψ) =
      (toSheafAb Y).map ((pullbackPushforwardAdjunction f).unit.app M ≫
        (pushforward f).map ψ) := by
  rw [Functor.map_comp, ← Category.assoc, unit_comp_map_pullbackAbComparison,
    pushforwardAb_map_toSheafAb_map, ← Functor.map_comp]

/-- The pushforward of abelian sheaves along a composite is the composite of the
pushforwards. -/
lemma pushforwardAb_comp_map {a : Z ⟶ X} {b : X ⟶ Y}
    {𝒩 𝒩' : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}} (ψ : 𝒩 ⟶ 𝒩') :
    (a ≫ b).pushforwardAb.map ψ = b.pushforwardAb.map (a.pushforwardAb.map ψ) := rfl

/-- The comparison map is compatible with the composition of morphisms of schemes. -/
lemma pullbackAbComparison_comp (a : Z ⟶ X) (b : X ⟶ Y) (M : Y.Modules) :
    (a.pullbackAbComp b).hom.app ((toSheafAb Y).obj M) ≫
        a.pullbackAb.map ((pullbackAbComparison b).app M) ≫
          (pullbackAbComparison a).app ((pullback b).obj M) =
      (pullbackAbComparison (a ≫ b)).app M ≫
        (toSheafAb Z).map ((pullbackComp a b).inv.app M) := by
  refine ((a ≫ b).pullbackPushforwardAbAdjunction.homEquiv _ _).injective ?_
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc ((Scheme.Hom.pullbackPushforwardAbAdjunction (a ≫ b)).unit.app _),
    Scheme.Hom.unit_pullbackAbComp_hom_app, Category.assoc, pushforwardAb_comp_map,
    pushforwardAb_comp_map]
  simp only [← Functor.map_comp]
  dsimp only [Functor.comp_obj]
  have hinner : a.pullbackPushforwardAbAdjunction.unit.app
        (b.pullbackAb.obj ((toSheafAb Y).obj M)) ≫
        a.pushforwardAb.map (a.pullbackAb.map ((pullbackAbComparison b).app M) ≫
          (pullbackAbComparison a).app ((pullback b).obj M)) =
      (pullbackAbComparison b).app M ≫ (toSheafAb X).map
        ((pullbackPushforwardAdjunction a).unit.app ((pullback b).obj M)) := by
    have h := a.pullbackPushforwardAbAdjunction.unit.naturality ((pullbackAbComparison b).app M)
    dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at h
    rw [Functor.map_comp, ← Category.assoc, ← h, Category.assoc,
      unit_comp_map_pullbackAbComparison]
  have hid : (pushforwardComp a b).hom.app ((pullback a).obj ((pullback b).obj M)) = 𝟙 _ := by
    ext U
    simp
  have hmod : (pullbackPushforwardAdjunction b).unit.app M ≫
        (pushforward b).map ((pullbackPushforwardAdjunction a).unit.app ((pullback b).obj M)) =
      (pullbackPushforwardAdjunction (a ≫ b)).unit.app M ≫
        (pushforward (a ≫ b)).map ((pullbackComp a b).inv.app M) := by
    have h := CategoryTheory.unit_conjugateEquiv ((pullbackPushforwardAdjunction b).comp
      (pullbackPushforwardAdjunction a)) (pullbackPushforwardAdjunction (a ≫ b))
      (pullbackComp a b).inv M
    dsimp only [Functor.comp_obj] at h
    rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
    simpa [hid] using h
  rw [hinner, unit_comp_map_pullbackAbComparison_comp,
    unit_comp_map_pullbackAbComparison_comp]
  exact congrArg ((toSheafAb Y).map) hmod

/-- The comparison map is compatible with transport along an equality of morphisms. -/
lemma pullbackAbComparison_congr {c₁ c₂ : Z ⟶ Y} (h : c₁ = c₂) (M : Y.Modules) :
    eqToHom (congrArg (fun m : Z ⟶ Y ↦ m.pullbackAb.obj ((toSheafAb Y).obj M)) h) ≫
        (pullbackAbComparison c₂).app M =
      (pullbackAbComparison c₁).app M ≫ (toSheafAb Z).map ((pullbackCongr h).hom.app M) := by
  subst h
  simp [pullbackCongr]

end Comparison

section BaseChange

variable {W'₀ W'₁ : Scheme.{u}} {i₀ : W₀ ⟶ W₁} {g : W'₁ ⟶ W₁} {g₀ : W'₀ ⟶ W₀}
  {i'₀ : W'₀ ⟶ W'₁}

/-- The right hand side of `Scheme.Modules.baseChange_key`, rewritten through the comparison
map for the composite `g₀ ≫ i₀`. -/
lemma baseChange_key_rhs (F : W₀.Modules) :
    (g₀.pullbackAbComp i₀).hom.app ((toSheafAb W₁).obj ((pushforward i₀).obj F)) ≫
        g₀.pullbackAb.map
            (i₀.pullbackPushforwardAbAdjunction.counit.app ((toSheafAb W₀).obj F)) ≫
          (pullbackAbComparison g₀).app F =
      (pullbackAbComparison (g₀ ≫ i₀)).app ((pushforward i₀).obj F) ≫
        (toSheafAb W'₀).map ((pullbackComp g₀ i₀).inv.app ((pushforward i₀).obj F) ≫
          (pullback g₀).map ((pullbackPushforwardAdjunction i₀).counit.app F)) := by
  rw [counit_app_toSheafAb, Functor.map_comp, Category.assoc]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [pullbackAbComparison_naturality]
  slice_lhs 1 3 => rw [pullbackAbComparison_comp]
  rw [Category.assoc, ← Functor.map_comp]

/-- The left hand side of `Scheme.Modules.baseChange_key`, rewritten through the comparison
map for the composite `i'₀ ≫ g`; this is where the mate identity
`Scheme.Modules.map_baseChange_comp_counit` for the base change morphism enters. -/
lemma baseChange_key_lhs (w : g₀ ≫ i₀ = i'₀ ≫ g) (F : W₀.Modules) :
    (i'₀.pullbackAbComp g).hom.app ((toSheafAb W₁).obj ((pushforward i₀).obj F)) ≫
        i'₀.pullbackAb.map ((pullbackAbComparison g).app ((pushforward i₀).obj F) ≫
            (toSheafAb W'₁).map ((baseChange w).natTrans.app F)) ≫
          i'₀.pullbackPushforwardAbAdjunction.counit.app
            ((toSheafAb W'₀).obj ((pullback g₀).obj F)) =
      (pullbackAbComparison (i'₀ ≫ g)).app ((pushforward i₀).obj F) ≫
        (toSheafAb W'₀).map ((pullbackComp i'₀ g).inv.app ((pushforward i₀).obj F) ≫
          (pullbackTwoSquare w).natTrans.app ((pushforward i₀).obj F) ≫
          (pullback g₀).map ((pullbackPushforwardAdjunction i₀).counit.app F)) := by
  rw [counit_app_toSheafAb, Functor.map_comp, Category.assoc]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  have hnat := pullbackAbComparison_naturality (f := i'₀) (φ := (baseChange w).natTrans.app F)
  dsimp only [Functor.comp_obj] at hnat ⊢
  rw [reassoc_of% hnat, ← Functor.map_comp, map_baseChange_comp_counit]
  slice_lhs 1 3 => rw [pullbackAbComparison_comp]
  rw [Category.assoc, ← Functor.map_comp]

/-- **The key compatibility**: the base change morphism of sheaves of modules, read through the
comparison maps between the pullback of abelian sheaves and the pullback of sheaves of modules,
is the comparison of the two ways of pulling back around the square. -/
lemma baseChange_key (w : g₀ ≫ i₀ = i'₀ ≫ g) (F : W₀.Modules) :
    eqToHom (congrArg (fun m : W'₀ ⟶ W₁ ↦
        m.pullbackAb.obj ((toSheafAb W₁).obj ((pushforward i₀).obj F))) w) ≫
      (i'₀.pullbackAbComp g).hom.app ((toSheafAb W₁).obj ((pushforward i₀).obj F)) ≫
        i'₀.pullbackAb.map ((pullbackAbComparison g).app ((pushforward i₀).obj F) ≫
            (toSheafAb W'₁).map ((baseChange w).natTrans.app F)) ≫
          i'₀.pullbackPushforwardAbAdjunction.counit.app
            ((toSheafAb W'₀).obj ((pullback g₀).obj F)) =
      (g₀.pullbackAbComp i₀).hom.app ((toSheafAb W₁).obj ((pushforward i₀).obj F)) ≫
        g₀.pullbackAb.map
            (i₀.pullbackPushforwardAbAdjunction.counit.app ((toSheafAb W₀).obj F)) ≫
          (pullbackAbComparison g₀).app F := by
  rw [baseChange_key_lhs w, baseChange_key_rhs]
  have hptsq : (pullbackTwoSquare w).natTrans.app ((pushforward i₀).obj F) =
      (pullbackComp i'₀ g).hom.app ((pushforward i₀).obj F) ≫
        (pullbackCongr w.symm).hom.app ((pushforward i₀).obj F) ≫
          (pullbackComp g₀ i₀).inv.app ((pushforward i₀).obj F) := rfl
  rw [hptsq]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [Functor.map_comp]
  slice_lhs 2 3 => rw [← pullbackAbComparison_congr w.symm]
  simp


/-- **Cohomology along a closed immersion commutes with base change.** For a commutative square
`g₀ ≫ i₀ = i'₀ ≫ g` of schemes whose horizontal arrows `i₀` and `i'₀` are closed immersions,
restricting a class along `i₀` and then pulling it back along `g₀` is pulling it back along `g`,
transporting it by the base change morphism `g^* i₀_* F ⟶ i'₀_* g₀^* F` and restricting along
`i'₀`. -/
theorem H.pushforwardMap_pullbackAddHom (w : g₀ ≫ i₀ = i'₀ ≫ g)
    [IsClosedImmersion i₀] [IsClosedImmersion i'₀] (F : W₀.Modules) (n : ℕ)
    (y : ((pushforward i₀).obj F).H n) :
    H.pushforwardMap i'₀ ((pullback g₀).obj F) n
        (H.map ((baseChange w).natTrans.app F) n
          (H.pullbackAddHom g ((pushforward i₀).obj F) n y)) =
      H.pullbackAddHom g₀ F n (H.pushforwardMap i₀ F n y) := by
  rw [H.pullbackAddHom_eq, H.map_apply, H.mapAddHom_apply_eq_comp,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, H.pushforwardMap_eq,
    Scheme.Hom.H.pullbackAddHom_comp_mk₀, Scheme.Hom.H.pullbackAddHom_comp,
    H.pushforwardMap_eq, H.pullbackAddHom_eq, Scheme.Hom.H.pullbackAddHom_comp_mk₀,
    Scheme.Hom.H.pullbackAddHom_comp]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Category.assoc]
  rw [← Scheme.Hom.H.pullbackAddHom_eqToHom w, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, baseChange_key w F]

/-- **Cohomology along a closed immersion commutes with base change**, in the form using the
isomorphism `H^n(W₀, F) ≃+ H^n(W₁, i₀_* F)` rather than its inverse. -/
theorem H.pullbackAddHom_pushforwardAddEquiv (w : g₀ ≫ i₀ = i'₀ ≫ g)
    [IsClosedImmersion i₀] [IsClosedImmersion i'₀] (F : W₀.Modules) (n : ℕ) (x : F.H n) :
    H.map ((baseChange w).natTrans.app F) n
        (H.pullbackAddHom g ((pushforward i₀).obj F) n
          (H.pushforwardAddEquiv i₀ F n x)) =
      H.pushforwardAddEquiv i'₀ ((pullback g₀).obj F) n (H.pullbackAddHom g₀ F n x) := by
  have hx : H.pushforwardMap i₀ F n (H.pushforwardAddEquiv i₀ F n x) = x := by simp
  have h := H.pushforwardMap_pullbackAddHom w F n (H.pushforwardAddEquiv i₀ F n x)
  rw [hx] at h
  refine (H.pushforwardAddEquiv i'₀ ((pullback g₀).obj F) n).symm.injective ?_
  simpa using h

end BaseChange

end AlgebraicGeometry.Scheme.Modules
