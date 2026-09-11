/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.AdicCompletion.Noetherian

/-!
# The theorem on formal functions, in degree zero

Let `f : W ⟶ T` be a proper morphism of schemes, let `F` be a coherent sheaf of `𝒪_W`-modules
and let `t` be a point of `T`. Writing `T_n = Spec (𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1))` for the `n`-th
infinitesimal neighbourhood of `t` and `F^{(n)}` for the pullback of `F` to `W ×_T T_n`, the
theorem on formal functions compares the `𝔪_t`-adic completion of the stalk `(f_* F)_t` with
the inverse limit of the modules `Γ(W ×_T T_n, F^{(n)})`.

This file builds the two sides of that comparison and the map between them, and states the
theorem.

## Main definitions

- `AlgebraicGeometry.Scheme.infinitesimalBaseChange`: the base change `W ×_T T_n` of a morphism
  `f : W ⟶ T` along the `n`-th infinitesimal neighbourhood of a point `t` of `T`, together with
  its projection to `W`, the transition morphisms `W ×_T T_m ⟶ W ×_T T_n` for `m ≤ n` and the
  fact that every point of `W ×_T T_n` lies over `t`.
- `AlgebraicGeometry.Scheme.Modules.formalSectionsSystem`: the inverse system
  `n ↦ Γ(W ×_T T_n, F^{(n)})` of modules over the local ring `𝒪_{T, t}`, as a functor
  `ℕᵒᵖ ⥤ ModuleCat 𝒪_{T, t}`. Its objects are
  `AlgebraicGeometry.Scheme.Modules.formalSections` and its transition maps are
  `AlgebraicGeometry.Scheme.Modules.formalSectionsMap`.
- `AlgebraicGeometry.Scheme.Modules.completedStalk`: the `𝔪_t`-adic completion of the stalk of
  a sheaf of `𝒪_T`-modules at `t`, which is the left-hand side of the comparison. By
  `AlgebraicGeometry.Scheme.Modules.finite_stalk` the stalk of a coherent sheaf is a finite
  module over `𝒪_{T, t}`, so over a noetherian scheme the completion is the completion of a
  finite module over a noetherian local ring.
- `AlgebraicGeometry.Scheme.Modules.formalFunctionsComparison`: the comparison map from the
  completed stalk of `f_* F` at `t` to `lim_n Γ(W ×_T T_n, F^{(n)})`. It is assembled from the
  maps `AlgebraicGeometry.Scheme.Modules.completedStalkToFormalSections`, which are the maps
  `(f_* F)_t ⟶ Γ(W ×_T T_n, F^{(n)})` of
  `AlgebraicGeometry.Scheme.Modules.stalkToFormalSections` factored through the quotient of the
  stalk by `𝔪_t ^ (n + 1)`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isIso_formalFunctionsComparison` (blueprint
  `prop:cube-formal-functions`): for `T` noetherian, `f : W ⟶ T` proper and `F` coherent, the
  comparison map `formalFunctionsComparison` is an isomorphism. This is `sorry` by design; see
  the implementation notes.

## Implementation notes

* `isIso_formalFunctionsComparison` is `sorry` **by design**: it is the degree-zero case of
  [Stacks, 02OC], and the blueprint marks it as an open obligation rather than proving it. The
  degree-zero case is not appreciably easier than the general one — the standard proof runs the
  comparison through a Čech complex in all degrees at once — so this file states it and leaves
  the proof to a subtree of its own. It is the only input of the chapter on the theorem of the
  cube that no other statement of that chapter needs: it is consumed only by
  `prop:cube-formal-triviality`. The statement of `prop:cube-proper-pushforward-coherent` in
  `WeilConjectures.AlgebraicGeometry.Cohomology.Proper` is `sorry` for the same reason, and this
  file follows its style.
* The section `Pulling back sections along a morphism of schemes` below develops general API for
  `Scheme.Modules` — pullback of sections over an open subset, and maps out of the stalk of a
  sheaf of modules — which belongs in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`, next to
  `AlgebraicGeometry.Scheme.Modules.sectionsPullback`. It is kept here because that file is
  being restored by another change at the time of writing and must not be edited concurrently.
* The transition maps and the maps out of the stalk are all built from generic lemmas about a
  *variable* morphism of schemes and then instantiated. Stating them generically is not only
  tidier: elaborating the element-level rewrites directly against the concrete scheme
  `Limits.pullback f (T.fromInfinitesimalNeighborhood t n)` makes the kernel unfold its glueing
  data and time out, whereas instantiating an already-proved generic lemma at that scheme is
  cheap. For the same reason `sectionsPullbackLE` inserts an explicit
  `eqToHom (pushforward_obj_obj ..)` instead of letting `Γ(a_* N, U)` and `Γ(N, a ⁻¹ᵁ U)` be
  identified silently.

## References

* [Stacks, 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Hartshorne, *Algebraic geometry*][hartshorne1977], III, Theorem 11.1

## Blueprint

`isIso_formalFunctionsComparison` implements `prop:cube-formal-functions` of the chapter on the
theorem of the cube.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite IsLocalRing SheafOfModules TopologicalSpace

namespace AlgebraicGeometry.Scheme

section BaseChange

variable {W T : Scheme.{u}} (f : W ⟶ T) (t : T)

/-- The base change `W ×_T T_n` of `f : W ⟶ T` along the `n`-th infinitesimal neighbourhood
of `t`. -/
noncomputable abbrev infinitesimalBaseChange (n : ℕ) : Scheme.{u} :=
  Limits.pullback f (T.fromInfinitesimalNeighborhood t n)

/-- The projection `W ×_T T_n ⟶ W`. -/
noncomputable abbrev infinitesimalBaseChangeπ (n : ℕ) : infinitesimalBaseChange f t n ⟶ W :=
  Limits.pullback.fst _ _

/-- For `m ≤ n`, the morphism `W ×_T T_m ⟶ W ×_T T_n` induced by `T_m ⟶ T_n`. -/
noncomputable def infinitesimalBaseChangeMap {m n : ℕ} (h : m ≤ n) :
    infinitesimalBaseChange f t m ⟶ infinitesimalBaseChange f t n :=
  Limits.pullback.map _ _ _ _ (𝟙 W) (T.infinitesimalNeighborhoodMap t h) (𝟙 T) (by simp) (by simp)

@[reassoc (attr := simp)]
lemma infinitesimalBaseChangeMap_π {m n : ℕ} (h : m ≤ n) :
    infinitesimalBaseChangeMap f t h ≫ infinitesimalBaseChangeπ f t n =
      infinitesimalBaseChangeπ f t m := by
  simp [infinitesimalBaseChangeMap]

/-- Every point of `W ×_T T_n` lies over `t`. -/
lemma f_infinitesimalBaseChangeπ_apply (n : ℕ) (w : infinitesimalBaseChange f t n) :
    f (infinitesimalBaseChangeπ f t n w) = t := by
  rw [← Scheme.Hom.comp_apply, Limits.pullback.condition, Scheme.Hom.comp_apply,
    T.fromInfinitesimalNeighborhood_apply]

/-- `W ×_T T_n` lies over any open neighbourhood of `t`. -/
lemma preimage_infinitesimalBaseChangeπ_eq_top (n : ℕ) {U : T.Opens} (hU : t ∈ U) :
    infinitesimalBaseChangeπ f t n ⁻¹ᵁ (f ⁻¹ᵁ U) = ⊤ := by
  ext w
  simpa [f_infinitesimalBaseChangeπ_apply f t n w] using hU

end BaseChange

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules

/-!
## Pulling back sections along a morphism of schemes

This section develops two pieces of general API: the pullback of sections of a sheaf of modules
from an open subset of the target to an open subset of the source contained in its preimage,
and the construction of a map out of the stalk of a sheaf of modules from a compatible family of
maps out of its sections over the open neighbourhoods of a point.
-/

noncomputable section PushforwardPullback

/-- The `app` of a morphism of sheaves of modules is natural in the open subset. -/
@[reassoc]
lemma Hom.map_app {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens}
    (i : op U ⟶ op V) : M.presheaf.map i ≫ φ.app V = φ.app U ≫ N.presheaf.map i := by
  simpa only [mapPresheaf_app] using φ.mapPresheaf.naturality i

variable {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (N : Y.Modules)

lemma eqToHom_pushforward_obj_obj (M : X.Modules) (U : Y.Opens) :
    eqToHom (pushforward_obj_obj a M U) = 𝟙 Γ((pushforward a).obj M, U) := rfl

lemma eqToHom_pushforward_map (M : X.Modules) {U U' : Y.Opens} (i : op U' ⟶ op U) :
    ((pushforward a).obj M).presheaf.map i ≫ eqToHom (pushforward_obj_obj a M U) =
      eqToHom (pushforward_obj_obj a M U') ≫
        M.presheaf.map ((Opens.map a.base).map i.unop).op := rfl

/-- The pullback of sections along `a : X ⟶ Y`, from an open `U` of `Y` to an open `V` of `X`
contained in `a ⁻¹ᵁ U`: the image of a section under the unit `N ⟶ a_* a^* N`, read as a section
of `a^* N` over `a ⁻¹ᵁ U` and restricted to `V`. -/
noncomputable def sectionsPullbackLE {U : Y.Opens} {V : X.Opens} (h : V ≤ a ⁻¹ᵁ U) :
    Γ(N, U) ⟶ Γ((pullback a).obj N, V) :=
  ((pullbackPushforwardAdjunction a).unit.app N).app U ≫
    eqToHom (pushforward_obj_obj a ((pullback a).obj N) U) ≫
    ((pullback a).obj N).presheaf.map (homOfLE h).op

lemma sectionsPullback_eq_sectionsPullbackLE :
    sectionsPullback a N = sectionsPullbackLE a N (by simp : (⊤ : X.Opens) ≤ a ⁻¹ᵁ ⊤) := rfl

/-- Restricting further after pulling back is pulling back to the smaller open. -/
@[reassoc]
lemma sectionsPullbackLE_map {U : Y.Opens} {V V' : X.Opens} (h : V ≤ a ⁻¹ᵁ U) (i : op V ⟶ op V') :
    sectionsPullbackLE a N h ≫ ((pullback a).obj N).presheaf.map i =
      sectionsPullbackLE a N (i.unop.le.trans h) := by
  rw [sectionsPullbackLE, sectionsPullbackLE, Category.assoc, Category.assoc,
    ← Functor.map_comp]
  congr 1

/-- Pulling back the restriction of a section is the pullback of the section. -/
@[reassoc]
lemma map_sectionsPullbackLE {U U' : Y.Opens} {V : X.Opens} (h : V ≤ a ⁻¹ᵁ U) (i : op U' ⟶ op U) :
    N.presheaf.map i ≫ sectionsPullbackLE a N h =
      sectionsPullbackLE a N (h.trans ((Opens.map a.base).map i.unop).le) := by
  have hnat := ((pullbackPushforwardAdjunction a).unit.app N).mapPresheaf.naturality i
  simp only [mapPresheaf_app, Functor.id_obj, Functor.comp_obj] at hnat
  rw [sectionsPullbackLE, sectionsPullbackLE, ← Category.assoc, ← Category.assoc, hnat,
    Category.assoc, Category.assoc]
  congr 1
  rw [← Category.assoc, eqToHom_pushforward_map, Category.assoc, ← Functor.map_comp]
  congr 1

/-- The pullback of sections is semilinear over `AlgebraicGeometry.Scheme.Hom.appLE`. -/
lemma sectionsPullbackLE_smul {U : Y.Opens} {V : X.Opens} (h : V ≤ a ⁻¹ᵁ U)
    (r : Γ(Y, U)) (r' : Γ(X, V)) (hr : a.appLE U V h r = r') (s : Γ(N, U)) :
    sectionsPullbackLE a N h (r • s) = r' • sectionsPullbackLE a N h s := by
  subst hr
  rw [Scheme.Hom.appLE, ConcreteCategory.comp_apply, sectionsPullbackLE]
  simp only [ConcreteCategory.comp_apply, Functor.id_obj, Functor.comp_obj, Hom.app_smul,
    eqToHom_pushforward_smul, map_smul]

/-- Pulling a section back to the full preimage in two steps agrees with pulling it back in
one. -/
@[reassoc]
lemma sectionsPullbackLE_comp_le_rfl (M : Z.Modules) (U : Z.Opens) :
    sectionsPullbackLE b M (le_refl (b ⁻¹ᵁ U)) ≫
        sectionsPullbackLE a ((pullback b).obj M) (le_refl (a ⁻¹ᵁ (b ⁻¹ᵁ U))) ≫
          ((pullbackComp a b).hom.app M).app (a ⁻¹ᵁ (b ⁻¹ᵁ U)) =
      sectionsPullbackLE (a ≫ b) M (le_refl ((a ≫ b) ⁻¹ᵁ U)) := by
  have h := congrArg (fun φ ↦ Hom.app φ U) (unit_pushforwardPullbackComp a b M)
  simp only [Hom.comp_app, pushforwardPullbackComp_app] at h
  simp only [sectionsPullbackLE, homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rw [eqToHom_pushforward_obj_obj b ((pullback b).obj M) U,
    eqToHom_pushforward_obj_obj a ((pullback a).obj ((pullback b).obj M)) (b ⁻¹ᵁ U),
    eqToHom_pushforward_obj_obj (a ≫ b) ((pullback (a ≫ b)).obj M) U]
  simpa using h

/-- Pulling a section back in two steps agrees with pulling it back in one. -/
@[reassoc]
lemma sectionsPullbackLE_comp (M : Z.Modules) {U : Z.Opens} {V : Y.Opens} {V' : X.Opens}
    (h₁ : V ≤ b ⁻¹ᵁ U) (h₂ : V' ≤ a ⁻¹ᵁ V) (h₃ : V' ≤ (a ≫ b) ⁻¹ᵁ U) :
    sectionsPullbackLE b M h₁ ≫ sectionsPullbackLE a ((pullback b).obj M) h₂ ≫
        ((pullbackComp a b).hom.app M).app V' =
      sectionsPullbackLE (a ≫ b) M h₃ := by
  rw [← sectionsPullbackLE_map b M (le_refl (b ⁻¹ᵁ U)) (homOfLE h₁).op, Category.assoc,
    map_sectionsPullbackLE_assoc,
    ← sectionsPullbackLE_map a ((pullback b).obj M) (le_refl (a ⁻¹ᵁ (b ⁻¹ᵁ U)))
      (homOfLE (h₂.trans ((Opens.map a.base).map (homOfLE h₁)).le)).op,
    Category.assoc, Hom.map_app, sectionsPullbackLE_comp_le_rfl_assoc,
    sectionsPullbackLE_map]

/-- Pulling back sections along equal morphisms. -/
lemma sectionsPullbackLE_congr {c d : X ⟶ Y} (hcd : c = d) {U : Y.Opens} {V : X.Opens}
    (hc : V ≤ c ⁻¹ᵁ U) (hd : V ≤ d ⁻¹ᵁ U) :
    sectionsPullbackLE c N hc ≫ ((pullbackCongr hcd).hom.app N).app V =
      sectionsPullbackLE d N hd := by
  subst hcd
  simp [pullbackCongr]

/-- The pullback of global sections along `a`, followed by a morphism out of `a^* N`. -/
noncomputable def sectionsPullbackApp {P : X.Modules} (e : (pullback a).obj N ⟶ P) :
    Γ(N, ⊤) ⟶ Γ(P, ⊤) :=
  sectionsPullback a N ≫ e.app ⊤

lemma sectionsPullbackApp_apply {P : X.Modules} (e : (pullback a).obj N ⟶ P) (s : Γ(N, ⊤)) :
    sectionsPullbackApp a N e s = e.app ⊤ (sectionsPullback a N s) := rfl

/-- The pullback of global sections is semilinear over `AlgebraicGeometry.Scheme.Hom.appTop`. -/
lemma sectionsPullbackApp_smul {P : X.Modules} (e : (pullback a).obj N ⟶ P) (r : Γ(Y, ⊤))
    (r' : Γ(X, ⊤)) (hr : a.appTop r = r') (s : Γ(N, ⊤)) :
    sectionsPullbackApp a N e (r • s) = r' • sectionsPullbackApp a N e s := by
  rw [sectionsPullbackApp_apply, sectionsPullbackApp_apply, sectionsPullback_smul,
    Hom.app_smul, hr]

end PushforwardPullback

noncomputable section StalkDesc

variable {X : Scheme.{u}} (G : X.Modules) (x : X) (M : Ab.{u})
  (c : ∀ U : X.Opens, x ∈ U → (Γ(G, U) ⟶ M))
  (hc : ∀ (U V : X.Opens) (hU : x ∈ U) (hV : x ∈ V) (i : op U ⟶ op V),
    G.presheaf.map i ≫ c V hV = c U hU)

/-- The cocone on the diagram computing the stalk of `G` at `x` given by a compatible family of
maps out of the sections of `G` over the open neighbourhoods of `x`. -/
noncomputable def stalkCocone : Cocone ((OpenNhds.inclusion x).op ⋙ G.presheaf) where
  pt := M
  ι :=
    { app U := c U.unop.1 U.unop.2
      naturality U V i := by
        simpa using hc U.unop.1 V.unop.1 U.unop.2 V.unop.2 ((OpenNhds.inclusion x).op.map i) }

/-- The map out of the stalk of `G` at `x` induced by a compatible family of maps out of the
sections of `G` over the open neighbourhoods of `x`. -/
noncomputable def stalkDesc : G.presheaf.stalk x ⟶ M :=
  colimit.desc _ (stalkCocone G x M c hc)

@[reassoc (attr := simp)]
lemma germ_comp_stalkDesc (U : X.Opens) (hU : x ∈ U) :
    G.presheaf.germ U x hU ≫ stalkDesc G x M c hc = c U hU :=
  colimit.ι_desc (stalkCocone G x M c hc) (op ⟨U, hU⟩)

@[simp]
lemma stalkDesc_germ (U : X.Opens) (hU : x ∈ U) (s : Γ(G, U)) :
    stalkDesc G x M c hc (G.presheaf.germ U x hU s) = c U hU s := by
  rw [← ConcreteCategory.comp_apply, germ_comp_stalkDesc]

section Linear

variable {S : CommRingCat.{u}} (φ : X.presheaf.stalk x ⟶ S) [Module S M]
  (hφ : ∀ (U : X.Opens) (hU : x ∈ U) (r : Γ(X, U)) (s : Γ(G, U)),
    c U hU (r • s) = φ (X.presheaf.germ U x hU r) • c U hU s)

include hφ in
lemma stalkDesc_smul (r : X.presheaf.stalk x) (z : G.presheaf.stalk x) :
    stalkDesc G x M c hc (r • z) = φ r • stalkDesc G x M c hc z := by
  obtain ⟨U, hU, s, rfl⟩ := G.presheaf.exists_germ_eq z
  obtain ⟨V, hV, r₀, rfl⟩ := X.presheaf.exists_germ_eq r
  rw [← X.presheaf.germ_res_apply (homOfLE inf_le_right : U ⊓ V ⟶ V) x ⟨hU, hV⟩ r₀,
    ← G.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x ⟨hU, hV⟩ s,
    ← germ_smul, stalkDesc_germ, stalkDesc_germ, hφ]

/-- The `𝒪_{X, x}`-linear map out of the stalk of `G` at `x` induced by a compatible family of
maps out of the sections of `G` over the open neighbourhoods of `x` which is semilinear over a
ring map `φ : 𝒪_{X, x} ⟶ S`. -/
noncomputable def stalkDescₗ :
    G.presheaf.stalk x →ₗ[X.presheaf.stalk x]
      (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S M) where
  toFun := stalkDesc G x M c hc
  map_add' := map_add _
  map_smul' := stalkDesc_smul G x M c hc φ hφ

include hφ in
/-- Composing the linear map out of the stalk with a semilinear map of the targets is the
linear map out of the stalk for the composed family. -/
lemma ofSemilinear_comp_stalkDescₗ {S' : CommRingCat.{u}} (ψ : X.presheaf.stalk x ⟶ S')
    (M' : Ab.{u}) [Module S' M'] (c' : ∀ U : X.Opens, x ∈ U → (Γ(G, U) ⟶ M'))
    (hc' : ∀ (U V : X.Opens) (hU : x ∈ U) (hV : x ∈ V) (i : op U ⟶ op V),
      G.presheaf.map i ≫ c' V hV = c' U hU)
    (hψ : ∀ (U : X.Opens) (hU : x ∈ U) (r : Γ(X, U)) (s : Γ(G, U)),
      c' U hU (r • s) = ψ (X.presheaf.germ U x hU r) • c' U hU s)
    (g : M ⟶ M') (hg : ∀ (r : X.presheaf.stalk x) (a : M), g (φ r • a) = ψ r • g a)
    (hcomp : stalkDesc G x M c hc ≫ g = stalkDesc G x M' c' hc') :
    (ModuleCat.ofSemilinear φ ψ g hg).hom.comp (stalkDescₗ G x M c hc φ hφ) =
      stalkDescₗ G x M' c' hc' ψ hψ :=
  LinearMap.ext fun z ↦
    (ModuleCat.ofSemilinear_apply φ ψ g hg _).trans
      ((ConcreteCategory.comp_apply (stalkDesc G x M c hc) g z).symm.trans
        (ConcreteCategory.congr_hom hcomp z))

end Linear

end StalkDesc

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section FormalSections

open Limits

variable {W T : Scheme.{u}} (f : W ⟶ T) (t : T) (F : W.Modules)

/-- The structure morphism `W ×_T T_n ⟶ T_n`. -/
noncomputable abbrev infinitesimalBaseChangeρ (n : ℕ) :
    infinitesimalBaseChange f t n ⟶ T.infinitesimalNeighborhood t n :=
  pullback.snd _ _

@[reassoc (attr := simp)]
lemma infinitesimalBaseChangeMap_ρ {m n : ℕ} (h : m ≤ n) :
    infinitesimalBaseChangeMap f t h ≫ infinitesimalBaseChangeρ f t n =
      infinitesimalBaseChangeρ f t m ≫ T.infinitesimalNeighborhoodMap t h := by
  simp [infinitesimalBaseChangeMap]

/-- The ring homomorphism `𝒪_{T, t} ⟶ Γ(W ×_T T_n, 𝒪)`, through which `𝒪_{T, t}` acts on the
sections of the pullback of `F` to `W ×_T T_n`. -/
noncomputable def toInfinitesimalBaseChangeΓ (n : ℕ) :
    T.presheaf.stalk t ⟶ Γ(infinitesimalBaseChange f t n, ⊤) :=
  T.toInfinitesimalRing t n ≫ (Scheme.ΓSpecIso _).inv ≫ (infinitesimalBaseChangeρ f t n).appTop

@[reassoc (attr := simp)]
lemma toInfinitesimalBaseChangeΓ_comp_appTop {m n : ℕ} (h : m ≤ n) :
    toInfinitesimalBaseChangeΓ f t n ≫ (infinitesimalBaseChangeMap f t h).appTop =
      toInfinitesimalBaseChangeΓ f t m := by
  rw [toInfinitesimalBaseChangeΓ, toInfinitesimalBaseChangeΓ, Category.assoc, Category.assoc,
    ← Scheme.Hom.comp_appTop, infinitesimalBaseChangeMap_ρ, Scheme.Hom.comp_appTop,
    ← Category.assoc ((Scheme.ΓSpecIso _).inv), Scheme.infinitesimalNeighborhoodMap,
    ← Scheme.ΓSpecIso_inv_naturality, ← Category.assoc, ← Category.assoc,
    Scheme.toInfinitesimalRing_infinitesimalRingMap, Category.assoc]

/-- Pulling a function on an open neighbourhood `U` of `t` back to `W ×_T T_n` is taking its
germ at `t` and mapping it by `𝒪_{T, t} ⟶ Γ(W ×_T T_n, 𝒪)`. -/
lemma appLE_infinitesimalBaseChangeπ_comp (n : ℕ) {U : T.Opens} (hU : t ∈ U)
    (h : (⊤ : (infinitesimalBaseChange f t n).Opens) ≤
      (infinitesimalBaseChangeπ f t n ≫ f) ⁻¹ᵁ U) :
    (infinitesimalBaseChangeπ f t n ≫ f).appLE U ⊤ h =
      T.presheaf.germ U t hU ≫ toInfinitesimalBaseChangeΓ f t n := by
  rw [Scheme.Hom.appLE_congr_hom (Limits.pullback.condition
      (f := f) (g := T.fromInfinitesimalNeighborhood t n)) U ⊤ h
      (by simp [T.preimage_fromInfinitesimalNeighborhood_eq_top t n hU]),
    ← Scheme.Hom.appLE_comp_appLE (infinitesimalBaseChangeρ f t n)
      (T.fromInfinitesimalNeighborhood t n) U ⊤ ⊤
      (T.preimage_fromInfinitesimalNeighborhood_eq_top t n hU).ge (by simp),
    T.fromInfinitesimalNeighborhood_appLE t n hU, Scheme.Hom.appLE_top_top,
    toInfinitesimalBaseChangeΓ, Category.assoc, Category.assoc]

/-- The comparison isomorphism `u^* F^{(n)} ≅ F^{(m)}` between the pullback of `F^{(n)}` along
`W ×_T T_m ⟶ W ×_T T_n` and `F^{(m)}`. -/
noncomputable def infinitesimalPullbackCompIso {m n : ℕ} (h : m ≤ n) :
    (pullback (infinitesimalBaseChangeMap f t h)).obj
        ((pullback (infinitesimalBaseChangeπ f t n)).obj F) ≅
      (pullback (infinitesimalBaseChangeπ f t m)).obj F :=
  (pullbackComp _ _).app F ≪≫ (pullbackCongr (infinitesimalBaseChangeMap_π f t h)).app F

/-- `Γ(W ×_T T_n, F^{(n)})`, as a module over the local ring `𝒪_{T, t}`. -/
noncomputable def formalSections (n : ℕ) : ModuleCat (T.presheaf.stalk t) :=
  (ModuleCat.restrictScalars (toInfinitesimalBaseChangeΓ f t n).hom).obj
    (ModuleCat.of Γ(infinitesimalBaseChange f t n, ⊤)
      Γ((pullback (infinitesimalBaseChangeπ f t n)).obj F, ⊤))

/-- The transition map of the inverse system: the pullback of sections along
`W ×_T T_m ⟶ W ×_T T_n`, followed by the identification of the pullback of `F^{(n)}` with
`F^{(m)}`. -/
noncomputable def formalSectionsFun {m n : ℕ} (h : m ≤ n) :
    Γ((pullback (infinitesimalBaseChangeπ f t n)).obj F, ⊤) ⟶
      Γ((pullback (infinitesimalBaseChangeπ f t m)).obj F, ⊤) :=
  sectionsPullbackApp (infinitesimalBaseChangeMap f t h)
    ((pullback (infinitesimalBaseChangeπ f t n)).obj F) (infinitesimalPullbackCompIso f t F h).hom

/-- The transition map is `𝒪_{T, t}`-linear: it is semilinear over the pullback of functions
along `W ×_T T_m ⟶ W ×_T T_n`, which is compatible with the two actions of `𝒪_{T, t}`. -/
lemma formalSectionsFun_smul {m n : ℕ} (h : m ≤ n) (r : T.presheaf.stalk t)
    (s : Γ((pullback (infinitesimalBaseChangeπ f t n)).obj F, ⊤)) :
    formalSectionsFun f t F h (toInfinitesimalBaseChangeΓ f t n r • s) =
      toInfinitesimalBaseChangeΓ f t m r • formalSectionsFun f t F h s :=
  sectionsPullbackApp_smul _ _ _ _ _
    (by rw [← toInfinitesimalBaseChangeΓ_comp_appTop f t h]; rfl) _

/-- The transition map `Γ(W ×_T T_n, F^{(n)}) ⟶ Γ(W ×_T T_m, F^{(m)})` of the inverse system,
as a map of `𝒪_{T, t}`-modules. -/
noncomputable def formalSectionsMap {m n : ℕ} (h : m ≤ n) :
    formalSections f t F n ⟶ formalSections f t F m :=
  ModuleCat.ofSemilinear (toInfinitesimalBaseChangeΓ f t n) (toInfinitesimalBaseChangeΓ f t m)
    (formalSectionsFun f t F h) (formalSectionsFun_smul f t F h)

lemma formalSectionsMap_apply {m n : ℕ} (h : m ≤ n)
    (y : Γ((pullback (infinitesimalBaseChangeπ f t n)).obj F, ⊤)) :
    (formalSectionsMap f t F h).hom y = formalSectionsFun f t F h y :=
  ModuleCat.ofSemilinear_apply _ _ _ _ y

/-- The inverse system `n ↦ Γ(W ×_T T_n, F^{(n)})` of `𝒪_{T, t}`-modules. -/
noncomputable def formalSectionsSystem : ℕᵒᵖ ⥤ ModuleCat (T.presheaf.stalk t) :=
  Functor.ofOpSequence fun n ↦ formalSectionsMap f t F n.le_succ

@[simp]
lemma formalSectionsSystem_obj (n : ℕ) :
    (formalSectionsSystem f t F).obj (op n) = formalSections f t F n :=
  rfl

@[simp]
lemma formalSectionsSystem_map_succ (n : ℕ) :
    (formalSectionsSystem f t F).map (homOfLE n.le_succ).op = formalSectionsMap f t F n.le_succ :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The map sending a section of `f_* F` over an open neighbourhood `U` of `t` to the
corresponding global section of `F^{(n)}`, which makes sense because `W ×_T T_n` lies over
`U`. -/
noncomputable def formalSectionsOfNhds (n : ℕ) (U : T.Opens) (hU : t ∈ U) :
    Γ((pushforward f).obj F, U) ⟶ Γ((pullback (infinitesimalBaseChangeπ f t n)).obj F, ⊤) :=
  eqToHom (pushforward_obj_obj f F U) ≫
    sectionsPullbackLE (infinitesimalBaseChangeπ f t n) F
      (preimage_infinitesimalBaseChangeπ_eq_top f t n hU).ge

lemma map_formalSectionsOfNhds (n : ℕ) (U V : T.Opens) (hU : t ∈ U) (hV : t ∈ V)
    (i : op U ⟶ op V) :
    ((pushforward f).obj F).presheaf.map i ≫ formalSectionsOfNhds f t F n V hV =
      formalSectionsOfNhds f t F n U hU := by
  rw [formalSectionsOfNhds, formalSectionsOfNhds, ← Category.assoc, eqToHom_pushforward_map,
    Category.assoc, map_sectionsPullbackLE]

lemma formalSectionsOfNhds_smul (n : ℕ) (U : T.Opens) (hU : t ∈ U) (r : Γ(T, U))
    (s : Γ((pushforward f).obj F, U)) :
    formalSectionsOfNhds f t F n U hU (r • s) =
      toInfinitesimalBaseChangeΓ f t n (T.presheaf.germ U t hU r) •
        formalSectionsOfNhds f t F n U hU s := by
  have key : (infinitesimalBaseChangeπ f t n).appLE (f ⁻¹ᵁ U) ⊤
      (preimage_infinitesimalBaseChangeπ_eq_top f t n hU).ge (f.app U r) =
      toInfinitesimalBaseChangeΓ f t n (T.presheaf.germ U t hU r) := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appLE,
      appLE_infinitesimalBaseChangeπ_comp f t n hU, ConcreteCategory.comp_apply]
  rw [formalSectionsOfNhds, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    eqToHom_pushforward_smul, sectionsPullbackLE_smul _ _ _ _ _ key]

lemma formalSectionsOfNhds_comp {m n : ℕ} (h : m ≤ n) (U : T.Opens) (hU : t ∈ U) :
    formalSectionsOfNhds f t F n U hU ≫ formalSectionsFun f t F h =
      formalSectionsOfNhds f t F m U hU := by
  have h₃ : (⊤ : (infinitesimalBaseChange f t m).Opens) ≤
      (infinitesimalBaseChangeMap f t h ≫ infinitesimalBaseChangeπ f t n) ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    rw [infinitesimalBaseChangeMap_π]
    exact (preimage_infinitesimalBaseChangeπ_eq_top f t m hU).ge
  rw [formalSectionsOfNhds, formalSectionsOfNhds, Category.assoc]
  congr 1
  rw [formalSectionsFun, sectionsPullbackApp, sectionsPullback_eq_sectionsPullbackLE,
    infinitesimalPullbackCompIso, Iso.trans_hom, Iso.app_hom, Iso.app_hom, Hom.comp_app,
    sectionsPullbackLE_comp_assoc _ _ F _ _ h₃, sectionsPullbackLE_congr]

/-- The canonical map from the stalk of `f_* F` at `t` to `Γ(W ×_T T_n, F^{(n)})`, as a map of
abelian groups. -/
noncomputable def stalkToFormalSectionsFun (n : ℕ) :
    ((pushforward f).obj F).presheaf.stalk t ⟶
      Γ((pullback (infinitesimalBaseChangeπ f t n)).obj F, ⊤) :=
  stalkDesc _ t _ (formalSectionsOfNhds f t F n) (map_formalSectionsOfNhds f t F n)

@[reassoc]
lemma stalkToFormalSectionsFun_comp {m n : ℕ} (h : m ≤ n) :
    stalkToFormalSectionsFun f t F n ≫ formalSectionsFun f t F h =
      stalkToFormalSectionsFun f t F m := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU ↦ ?_
  rw [← Category.assoc, stalkToFormalSectionsFun, germ_comp_stalkDesc,
    formalSectionsOfNhds_comp, stalkToFormalSectionsFun, germ_comp_stalkDesc]

/-- The canonical map from the stalk of `f_* F` at `t` to `Γ(W ×_T T_n, F^{(n)})`, as a map of
`𝒪_{T, t}`-modules. -/
noncomputable def stalkToFormalSections (n : ℕ) :
    ((pushforward f).obj F).presheaf.stalk t →ₗ[T.presheaf.stalk t] formalSections f t F n :=
  stalkDescₗ _ t _ (formalSectionsOfNhds f t F n) (map_formalSectionsOfNhds f t F n)
    (toInfinitesimalBaseChangeΓ f t n) (formalSectionsOfNhds_smul f t F n)

lemma stalkToFormalSections_apply (n : ℕ) (z : ((pushforward f).obj F).presheaf.stalk t) :
    stalkToFormalSections f t F n z = stalkToFormalSectionsFun f t F n z := rfl

/-- An element of `𝔪_t ^ (n + 1)` acts as zero on `Γ(W ×_T T_n, 𝒪)`, because the action of
`𝒪_{T, t}` factors through `𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1)`. -/
lemma toInfinitesimalBaseChangeΓ_eq_zero (n : ℕ) {r : T.presheaf.stalk t}
    (hr : r ∈ maximalIdeal (T.presheaf.stalk t) ^ (n + 1)) :
    toInfinitesimalBaseChangeΓ f t n r = 0 := by
  have h0 : T.toInfinitesimalRing t n r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
  rw [toInfinitesimalBaseChangeΓ, CommRingCat.comp_apply, h0, map_zero]

lemma smul_pow_le_ker_stalkToFormalSections (n : ℕ) :
    (maximalIdeal (T.presheaf.stalk t) ^ (n + 1) •
        (⊤ : Submodule (T.presheaf.stalk t) (((pushforward f).obj F).presheaf.stalk t))) ≤
      LinearMap.ker (stalkToFormalSections f t F n) := by
  rw [Submodule.smul_le]
  intro r hr z _
  rw [LinearMap.mem_ker, LinearMap.map_smul]
  exact ModuleCat.smul_restrictScalars_eq_zero _ _ (toInfinitesimalBaseChangeΓ_eq_zero f t n hr) _

/-- The `𝔪_t`-adic completion of the stalk of a sheaf of `𝒪_T`-modules `G` at `t`. This is the
left-hand side of the theorem on formal functions, for `G = f_* F`. -/
noncomputable abbrev completedStalk (G : T.Modules) : Type u :=
  AdicCompletion (maximalIdeal (T.presheaf.stalk t)) (G.presheaf.stalk t)

/-- The canonical map from the stalk of `G` at `t` to its `𝔪_t`-adic completion. -/
noncomputable abbrev toCompletedStalk (G : T.Modules) :
    G.presheaf.stalk t →ₗ[T.presheaf.stalk t] completedStalk t G :=
  AdicCompletion.of _ _

/-- The canonical map from the `𝔪_t`-adic completion of the stalk of `f_* F` at `t` to
`Γ(W ×_T T_n, F^{(n)})`: the map out of the stalk factors through the quotient by
`𝔪_t ^ (n + 1)`, which is the `(n + 1)`-st component of the completion. -/
noncomputable def completedStalkToFormalSections (n : ℕ) :
    completedStalk t ((pushforward f).obj F) →ₗ[T.presheaf.stalk t] formalSections f t F n :=
  (Submodule.liftQ _ (stalkToFormalSections f t F n)
      (smul_pow_le_ker_stalkToFormalSections f t F n)).comp
    (AdicCompletion.eval (maximalIdeal (T.presheaf.stalk t)) _ (n + 1))

lemma formalSectionsMap_comp_stalkToFormalSections {m n : ℕ} (h : m ≤ n) :
    (formalSectionsMap f t F h).hom.comp (stalkToFormalSections f t F n) =
      stalkToFormalSections f t F m :=
  ofSemilinear_comp_stalkDescₗ (hcomp := stalkToFormalSectionsFun_comp f t F h) ..

lemma formalSectionsMap_comp_completedStalkToFormalSections {m n : ℕ} (h : m ≤ n) :
    (formalSectionsMap f t F h).hom.comp (completedStalkToFormalSections f t F n) =
      completedStalkToFormalSections f t F m := by
  rw [completedStalkToFormalSections, completedStalkToFormalSections, ← LinearMap.comp_assoc,
    Submodule.comp_liftQ
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))) _ _
      (smul_pow_le_ker_stalkToFormalSections f t F m)
      (formalSectionsMap_comp_stalkToFormalSections f t F h),
    LinearMap.comp_assoc, AdicCompletion.transitionMap_comp_eval]
  exact Nat.add_le_add_right h 1

/-- The cone on the inverse system `n ↦ Γ(W ×_T T_n, F^{(n)})` with vertex the `𝔪_t`-adic
completion of the stalk of `f_* F` at `t`. -/
noncomputable def formalSectionsCone : Cone (formalSectionsSystem f t F) where
  pt := ModuleCat.of (T.presheaf.stalk t) (completedStalk t ((pushforward f).obj F))
  π := NatTrans.ofOpSequence
    (fun n ↦ ConcreteCategory.ofHom (C := ModuleCat (T.presheaf.stalk t))
      (X := ModuleCat.of (T.presheaf.stalk t) (completedStalk t ((pushforward f).obj F)))
      (Y := formalSections f t F n) (completedStalkToFormalSections f t F n))
    (fun n ↦ by
      rw [formalSectionsSystem_map_succ]
      refine (Category.id_comp _).trans ?_
      exact (ModuleCat.hom_ext
        (formalSectionsMap_comp_completedStalkToFormalSections f t F n.le_succ)).symm)

/-- **The comparison map of the theorem on formal functions**, in degree zero: the canonical map
from the `𝔪_t`-adic completion of the stalk of `f_* F` at `t` to the inverse limit of the
modules `Γ(W ×_T T_n, F^{(n)})`. -/
noncomputable def formalFunctionsComparison :
    ModuleCat.of (T.presheaf.stalk t) (completedStalk t ((pushforward f).obj F)) ⟶
      limit (formalSectionsSystem f t F) :=
  limit.lift _ (formalSectionsCone f t F)

/-- **The theorem on formal functions**, in degree zero.

For a noetherian scheme `T`, a proper morphism `f : W ⟶ T` and a coherent sheaf of
`𝒪_W`-modules `F`, the comparison map from the `𝔪_t`-adic completion of the stalk of `f_* F`
at `t` to the inverse limit of the modules `Γ(W ×_T T_n, F^{(n)})` is an isomorphism. This is
`prop:cube-formal-functions` of the blueprint.

This is the degree-zero case of [Stacks, 02OC] and is `sorry` by design; see the implementation
notes of this file. -/
@[stacks 02OC]
theorem isIso_formalFunctionsComparison [AlgebraicGeometry.IsNoetherian T] [IsProper f]
    [F.IsCoherent] : IsIso (formalFunctionsComparison f t F) :=
  sorry

end FormalSections

end AlgebraicGeometry.Scheme.Modules
