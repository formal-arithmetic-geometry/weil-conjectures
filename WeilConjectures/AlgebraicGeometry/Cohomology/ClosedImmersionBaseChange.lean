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

The statement is given as a pointwise identity of cohomology classes. Both composites are
additive maps between the same two groups, so an equality of `AddMonoidHom`s would also
typecheck; what is *not* available is an equality of semilinear maps, because
`H.pushforwardMap i` is semilinear over `i.appTop` and `H.pullbackAddHom f` over `f.appTop`,
so the two composites are
semilinear over `(g₀ ≫ i₀).appTop` and `(i'₀ ≫ g).appTop`, which agree only through `w` and not
on the nose. The pointwise identity carries the same content without the transport, and is the
form a consumer rewrites with.

## Strategy

Both composites are pullbacks of `y` along the two factorisations `g₀ ≫ i₀ = i'₀ ≫ g` of the
same morphism `W'₀ ⟶ W₁`, followed by a morphism of abelian sheaves in degree `0`. Concretely,
`H.pushforwardMap` is the *pullback* map on the cohomology of the underlying abelian sheaf
followed by the counit of the adjunction `i^{-1} ⊣ i_♭`
(`H.pushforwardMap_eq_comp_counit`), and `H.pullbackAddHom` is the pullback map followed by the
comparison map (`H.pullbackAddHom_eq_comp_pullbackAbComparison`). So the composition law for the
pullback map, `AlgebraicGeometry.Scheme.Hom.H.pullbackAddHom_comp`, reduces the square to the
identity `Scheme.Modules.pullbackAbComparison_baseChange` between morphisms of abelian sheaves in
degree `0`, which is in turn deduced from the mate identity
`Scheme.Modules.map_baseChange_comp_counit` satisfied by the base change morphism.

Note that the pullback map, not the pushforward map, is the one that composes: this is what
makes the argument work with only the *functoriality* of `Ext.mapExactFunctor` in the exact
functor. Formulating the square with `H.pushforwardAddEquiv` instead would require comparing
`g^{-1} i_{0♭}` with `i'_{0♭} g_0^{-1}`, which is base change for the pushforward of abelian
sheaves and is genuinely harder.

## Main statements

* `AlgebraicGeometry.Scheme.Modules.H.pushforwardMap_eq_comp_counit` — the restriction map along
  a closed immersion, factored through the pullback map on the cohomology of the underlying
  abelian sheaf.
* `AlgebraicGeometry.Scheme.Modules.pullbackAbComparison_baseChange` — the identity of
  degree-zero morphisms of abelian sheaves behind the base change square.
* `AlgebraicGeometry.Scheme.Modules.H.pushforwardMap_pullbackAddHom` — **cohomology along a
  closed immersion commutes with base change**, and
  `AlgebraicGeometry.Scheme.Modules.H.pullbackAddHom_pushforwardAddEquiv`, the equivalent form
  using `H.pushforwardAddEquiv` instead of its inverse `H.pushforwardMap`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace Abelian

namespace AlgebraicGeometry.Scheme.Modules

variable {W₀ W₁ : Scheme.{u}}

attribute [local instance] Scheme.Hom.preservesFiniteColimits_pushforwardAb

section Pushforward

variable (i : W₀ ⟶ W₁) [IsClosedImmersion i] (F : W₀.Modules) (n : ℕ)

/-- **The restriction map along a closed immersion factors through the pullback map on the
cohomology of the underlying abelian sheaf**, followed by the counit of the adjunction
`i^{-1} ⊣ i_♭`:

```
H^n(W₁, i_* F) --Hom.H.pullbackAddHom--> H^n(W₀, i^{-1}((i_* F)^♭)) -- ∘ counit --> H^n(W₀, F)
       |                                                                              ^
       +------------------------------H.pushforwardMap-------------------------------+
```

This is `CategoryTheory.Adjunction.extAddEquiv_symm_apply` read on sheaves of modules. -/
lemma H.pushforwardMap_eq_comp_counit (y : ((pushforward i).obj F).H n) :
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
    ((constantSheafAb W₁).obj (AddCommGrpCat.of (ULift ℤ))) ((toSheafAb W₀).obj F) n y

end Pushforward

section BaseChange

variable {W'₀ W'₁ : Scheme.{u}} {i₀ : W₀ ⟶ W₁} {g : W'₁ ⟶ W₁} {g₀ : W'₀ ⟶ W₀}
  {i'₀ : W'₀ ⟶ W'₁} [IsClosedImmersion i₀] [IsClosedImmersion i'₀]

omit [IsClosedImmersion i₀] in
/-- The route `W'₀ → W₀ → W₁` around the square, expressed through the comparison map for the
composite `g₀ ≫ i₀`:

```
(g₀ ≫ i₀)^{-1} (i₀_* F)^♭ --comp--> g₀^{-1} i₀^{-1} (i₀_* F)^♭ --counit--> g₀^{-1} (F^♭)
          |                                                                     |
     comparison                                                            comparison
          v                                                                     v
 ((g₀ ≫ i₀)^* i₀_* F)^♭ --((pullbackComp)⁻¹ ≫ g₀^* counit)^♭--> (g₀^* F)^♭
```
-/
lemma pullbackAbComp_hom_app_comp_counit (F : W₀.Modules) :
    (g₀.pullbackAbComp i₀).hom.app ((toSheafAb W₁).obj ((pushforward i₀).obj F)) ≫
        g₀.pullbackAb.map
            (i₀.pullbackPushforwardAbAdjunction.counit.app ((toSheafAb W₀).obj F)) ≫
          (pullbackAbComparison g₀).app F =
      (pullbackAbComparison (g₀ ≫ i₀)).app ((pushforward i₀).obj F) ≫
        (toSheafAb W'₀).map ((pullbackComp g₀ i₀).inv.app ((pushforward i₀).obj F) ≫
          (pullback g₀).map ((pullbackPushforwardAdjunction i₀).counit.app F)) := by
  rw [pullbackPushforwardAbAdjunction_counit_app_toSheafAb_obj, Functor.map_comp, Category.assoc]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [pullbackAbComparison_naturality]
  slice_lhs 1 3 => rw [pullbackAbComparison_comp]
  rw [Category.assoc, ← Functor.map_comp]

omit [IsClosedImmersion i₀] [IsClosedImmersion i'₀] in
/-- The route `W'₀ → W'₁ → W₁` around the square, expressed through the comparison map for the
composite `i'₀ ≫ g`; this is where the mate identity
`AlgebraicGeometry.Scheme.Modules.map_baseChange_comp_counit` for the base change morphism
enters:

```
(i'₀ ≫ g)^{-1} (i₀_* F)^♭ --comp--> i'₀^{-1} g^{-1} (i₀_* F)^♭
                          --baseChange--> i'₀^{-1} (i'₀_* g₀^* F)^♭
          |                                              |
     comparison                                       counit
          v                                              v
 ((i'₀ ≫ g)^* i₀_* F)^♭ --((pullbackComp)⁻¹ ≫ pullbackTwoSquare ≫ g₀^* counit)^♭--> (g₀^* F)^♭
```
-/
lemma pullbackAbComp_hom_app_comp_baseChange (w : g₀ ≫ i₀ = i'₀ ≫ g) (F : W₀.Modules) :
    (i'₀.pullbackAbComp g).hom.app ((toSheafAb W₁).obj ((pushforward i₀).obj F)) ≫
        i'₀.pullbackAb.map ((pullbackAbComparison g).app ((pushforward i₀).obj F) ≫
            (toSheafAb W'₁).map ((baseChange w).natTrans.app F)) ≫
          i'₀.pullbackPushforwardAbAdjunction.counit.app
            ((toSheafAb W'₀).obj ((pullback g₀).obj F)) =
      (pullbackAbComparison (i'₀ ≫ g)).app ((pushforward i₀).obj F) ≫
        (toSheafAb W'₀).map ((pullbackComp i'₀ g).inv.app ((pushforward i₀).obj F) ≫
          (pullbackTwoSquare w).natTrans.app ((pushforward i₀).obj F) ≫
          (pullback g₀).map ((pullbackPushforwardAdjunction i₀).counit.app F)) := by
  rw [pullbackPushforwardAbAdjunction_counit_app_toSheafAb_obj, Functor.map_comp, Category.assoc]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  have hnat := pullbackAbComparison_naturality (f := i'₀) (φ := (baseChange w).natTrans.app F)
  dsimp only [Functor.comp_obj] at hnat ⊢
  rw [reassoc_of% hnat, ← Functor.map_comp, map_baseChange_comp_counit]
  slice_lhs 1 3 => rw [pullbackAbComparison_comp]
  rw [Category.assoc, ← Functor.map_comp]

omit [IsClosedImmersion i₀] [IsClosedImmersion i'₀] in
/-- **The key compatibility**: the base change morphism of sheaves of modules, read through the
comparison maps between the pullback of abelian sheaves and the pullback of sheaves of modules,
is the comparison of the two ways of pulling `(i₀_* F)^♭` back around the square:

```
                      W'₀ --eqToHom, pullbackAbComp, comparison, baseChange, counit--> (g₀^* F)^♭
(i₀_* F)^♭ on W₁  <                                                                        ‖
                      W'₀ --pullbackAbComp, counit, comparison--------------------------> (g₀^* F)^♭
```

the upper route running through `W'₁` and the lower one through `W₀`. -/
lemma pullbackAbComparison_baseChange (w : g₀ ≫ i₀ = i'₀ ≫ g) (F : W₀.Modules) :
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
  rw [pullbackAbComp_hom_app_comp_baseChange w, pullbackAbComp_hom_app_comp_counit]
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
`i'₀`:

```
  H^n(W₁, i₀_* F) ────pullbackAddHom g───▶ H^n(W'₁, g^*(i₀_* F))
        │                                        │ H.map (baseChange w)
        │ pushforwardMap i₀                      ▼
        │                              H^n(W'₁, i'₀_*(g₀^* F))
        ▼                                        │ pushforwardMap i'₀
  H^n(W₀, F) ───────pullbackAddHom g₀────▶ H^n(W'₀, g₀^* F)
```
-/
theorem H.pushforwardMap_pullbackAddHom (w : g₀ ≫ i₀ = i'₀ ≫ g) (F : W₀.Modules) (n : ℕ)
    (y : ((pushforward i₀).obj F).H n) :
    H.pushforwardMap i'₀ ((pullback g₀).obj F) n
        (H.map ((baseChange w).natTrans.app F) n
          (H.pullbackAddHom g ((pushforward i₀).obj F) n y)) =
      H.pullbackAddHom g₀ F n (H.pushforwardMap i₀ F n y) := by
  rw [H.pullbackAddHom_eq_comp_pullbackAbComparison, H.map_apply, H.mapAddHom_apply_eq_comp,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, H.pushforwardMap_eq_comp_counit,
    Scheme.Hom.H.pullbackAddHom_comp_mk₀, Scheme.Hom.H.pullbackAddHom_comp,
    H.pushforwardMap_eq_comp_counit, H.pullbackAddHom_eq_comp_pullbackAbComparison,
    Scheme.Hom.H.pullbackAddHom_comp_mk₀, Scheme.Hom.H.pullbackAddHom_comp]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Category.assoc]
  rw [← Scheme.Hom.H.pullbackAddHom_eqToHom w, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, pullbackAbComparison_baseChange w F]

/-- **Cohomology along a closed immersion commutes with base change**, in the form using the
isomorphism `H^n(W₀, F) ≃+ H^n(W₁, i₀_* F)` rather than its inverse:

```
  H^n(W₀, F) ──pushforwardAddEquiv i₀──▶ H^n(W₁, i₀_* F) ──pullbackAddHom g──▶ H^n(W'₁, g^*(i₀_* F))
        │                                                                              │
        │ pullbackAddHom g₀                                              H.map (baseChange w)
        ▼                                                                              ▼
  H^n(W'₀, g₀^* F) ─────pushforwardAddEquiv i'₀────────────────────▶ H^n(W'₁, i'₀_*(g₀^* F))
```
-/
theorem H.pullbackAddHom_pushforwardAddEquiv (w : g₀ ≫ i₀ = i'₀ ≫ g) (F : W₀.Modules) (n : ℕ)
    (x : F.H n) :
    H.map ((baseChange w).natTrans.app F) n
        (H.pullbackAddHom g ((pushforward i₀).obj F) n
          (H.pushforwardAddEquiv i₀ F n x)) =
      H.pushforwardAddEquiv i'₀ ((pullback g₀).obj F) n (H.pullbackAddHom g₀ F n x) := by
  have h := H.pushforwardMap_pullbackAddHom w F n (H.pushforwardAddEquiv i₀ F n x)
  rw [show H.pushforwardMap i₀ F n (H.pushforwardAddEquiv i₀ F n x) = x by simp] at h
  refine (H.pushforwardAddEquiv i'₀ ((pullback g₀).obj F) n).symm.injective ?_
  simpa using h

end BaseChange

end AlgebraicGeometry.Scheme.Modules
