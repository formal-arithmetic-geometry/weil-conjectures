/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import WeilConjectures.AlgebraicGeometry.Cohomology.Proper
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The theorem on formal functions, in degree zero

Let `f : W ⟶ T` be a proper morphism of schemes, let `F` be a coherent sheaf of `𝒪_W`-modules
and let `t` be a point of `T`. Writing `T_n = Spec (𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1))` for the `n`-th
infinitesimal neighbourhood of `t` and `F^{(n)}` for the pullback of `F` to `W ×_T T_n`, the
theorem on formal functions compares the `𝔪_t`-adic completion of the stalk `(f_* F)_t` with
the inverse limit of the modules `Γ(W ×_T T_n, F^{(n)})`.

This file builds the two sides of that comparison and the map between them, and states the
theorem. The base change `W ×_T T_n` itself, its transition morphisms and the ring map
`𝒪_{T, t} ⟶ Γ(W ×_T T_n, 𝒪)` are in
`WeilConjectures.Mathlib.AlgebraicGeometry.Stalk`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.formalSectionsSystem`: the inverse system
  `n ↦ Γ(W ×_T T_n, F^{(n)})` of modules over the local ring `𝒪_{T, t}`, as a functor
  `ℕᵒᵖ ⥤ ModuleCat 𝒪_{T, t}`. Its objects are
  `AlgebraicGeometry.Scheme.Modules.formalSections` and its transition maps are
  `AlgebraicGeometry.Scheme.Modules.formalSectionsMap`.
- `AlgebraicGeometry.Scheme.Modules.stalkToFormalSections`: the canonical `𝒪_{T, t}`-linear map
  `(f_* F)_t ⟶ Γ(W ×_T T_n, F^{(n)})`, defined on the stalk from the maps
  `AlgebraicGeometry.Scheme.Modules.formalSectionsOfNhds` out of the sections over the open
  neighbourhoods of `t`.
- `AlgebraicGeometry.Scheme.Modules.formalFunctionsComparison`: the comparison map from the
  completed stalk `AlgebraicGeometry.Scheme.Modules.completedStalk` of `f_* F` at `t` to
  `lim_n Γ(W ×_T T_n, F^{(n)})`. It is assembled from the maps
  `AlgebraicGeometry.Scheme.Modules.completedStalkToFormalSections`, which are the maps
  `stalkToFormalSections` factored through the quotient of the stalk by `𝔪_t ^ (n + 1)`. By
  `AlgebraicGeometry.Scheme.Modules.finite_stalk` the stalk of a coherent sheaf is a finite
  module over `𝒪_{T, t}`, so over a locally noetherian scheme the left-hand side is the
  completion of a finite module over a noetherian local ring.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isIso_formalFunctionsComparison` (blueprint
  `prop:cube-formal-functions`): for `T` locally noetherian, `f : W ⟶ T` proper and `F`
  coherent, the comparison map `formalFunctionsComparison` is an isomorphism. This is `sorry`
  by design; see the implementation notes.

## Implementation notes

* `isIso_formalFunctionsComparison` is `sorry` **by design**: it is the degree-zero case of
  [Stacks, 02OC], and the blueprint marks it as an open obligation rather than proving it. The
  degree-zero case is not appreciably easier than the general one — the standard proof runs the
  comparison through a Čech complex in all degrees at once — so this file states it and leaves
  the proof to a subtree of its own. It is the only input of the chapter on the theorem of the
  cube that no other statement of that chapter needs: it is consumed only by
  `prop:cube-formal-triviality`. It is one of the thirteen open obligations of the cube and
  degree chapters classified on issue 837. The statement of
  `prop:cube-proper-pushforward-coherent` in
  `WeilConjectures.AlgebraicGeometry.Cohomology.Proper` is `sorry` for the same reason, and this
  file follows its style.
* It is stated as a `theorem` rather than an `instance` on purpose: a statement that rests on a
  `sorry` should be applied by name, so that every place depending on it is visible in the
  source, rather than being picked up silently by typeclass inference.
* The transition maps and the maps out of the stalk are all built from generic lemmas about a
  *variable* morphism of schemes and then instantiated. Stating them generically is not only
  tidier: elaborating the element-level rewrites directly against the concrete scheme
  `Limits.pullback f (T.fromInfinitesimalNeighborhood t n)` makes the kernel unfold its glueing
  data and time out, whereas instantiating an already-proved generic lemma at that scheme is
  cheap. For the same reason `AlgebraicGeometry.Scheme.Modules.sectionsPullbackLE` inserts an
  explicit `eqToHom (pushforward_obj_obj ..)` instead of letting `Γ(a_* N, U)` and
  `Γ(N, a ⁻¹ᵁ U)` be identified silently.

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

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section FormalSections

variable {W T : Scheme.{u}} (f : W ⟶ T) (t : T) (F : W.Modules)

/-- `Γ(W ×_T T_n, F^{(n)})`, as a module over the local ring `𝒪_{T, t}`. -/
def formalSections (n : ℕ) : ModuleCat (T.presheaf.stalk t) :=
  (ModuleCat.restrictScalars (toInfinitesimalBaseChangeΓ f t n).hom).obj
    (ModuleCat.of Γ(infinitesimalBaseChange f t n, ⊤)
      Γ((pullback (infinitesimalBaseChangeFst f t n)).obj F, ⊤))

/-- `formalSections` is the evaluation of `F^{(n)}` at the top open, with scalars restricted
along `𝒪_{T, t} ⟶ Γ(W ×_T T_n, 𝒪)`. -/
lemma formalSections_eq_evaluation (n : ℕ) :
    formalSections f t F n =
      (ModuleCat.restrictScalars (toInfinitesimalBaseChangeΓ f t n).hom).obj
        ((SheafOfModules.evaluation _ (op ⊤)).obj
          ((pullback (infinitesimalBaseChangeFst f t n)).obj F)) := rfl

/-- The transition map of the inverse system: the pullback of sections along
`W ×_T T_m ⟶ W ×_T T_n`, followed by the identification of the pullback of `F^{(n)}` with
`F^{(m)}`. -/
def formalSectionsFun {m n : ℕ} (h : m ≤ n) :
    Γ((pullback (infinitesimalBaseChangeFst f t n)).obj F, ⊤) ⟶
      Γ((pullback (infinitesimalBaseChangeFst f t m)).obj F, ⊤) :=
  sectionsPullbackOver (infinitesimalBaseChangeMap f t h)
    (infinitesimalBaseChangeMap_fst f t h) F

/-- The transition map is `𝒪_{T, t}`-linear: it is semilinear over the pullback of functions
along `W ×_T T_m ⟶ W ×_T T_n`, which is compatible with the two actions of `𝒪_{T, t}`. -/
lemma formalSectionsFun_smul {m n : ℕ} (h : m ≤ n) (r : T.presheaf.stalk t)
    (s : Γ((pullback (infinitesimalBaseChangeFst f t n)).obj F, ⊤)) :
    formalSectionsFun f t F h (toInfinitesimalBaseChangeΓ f t n r • s) =
      toInfinitesimalBaseChangeΓ f t m r • formalSectionsFun f t F h s :=
  sectionsPullbackOver_smul _ _ _ _ _
    (by rw [← CommRingCat.comp_apply, toInfinitesimalBaseChangeΓ_comp_appTop]) _

/-- The transition map at `m = n` is the identity. -/
@[simp]
lemma formalSectionsFun_refl (n : ℕ) : formalSectionsFun f t F (le_refl n) = 𝟙 _ := by
  rw [formalSectionsFun]
  simp only [infinitesimalBaseChangeMap_refl]
  exact sectionsPullbackOver_id _ _

/-- The transition maps compose. -/
lemma formalSectionsFun_comp {l m n : ℕ} (h₁ : l ≤ m) (h₂ : m ≤ n) :
    formalSectionsFun f t F h₂ ≫ formalSectionsFun f t F h₁ =
      formalSectionsFun f t F (h₁.trans h₂) := by
  rw [formalSectionsFun, formalSectionsFun, formalSectionsFun, sectionsPullbackOver_comp]
  simp only [infinitesimalBaseChangeMap_comp]

/-- The transition map `Γ(W ×_T T_n, F^{(n)}) ⟶ Γ(W ×_T T_m, F^{(m)})` of the inverse system,
as a map of `𝒪_{T, t}`-modules. -/
def formalSectionsMap {m n : ℕ} (h : m ≤ n) :
    formalSections f t F n ⟶ formalSections f t F m :=
  ModuleCat.ofSemilinear (toInfinitesimalBaseChangeΓ f t n) (toInfinitesimalBaseChangeΓ f t m)
    (formalSectionsFun f t F h) (formalSectionsFun_smul f t F h)

/-- The transition map at `m = n` is the identity. -/
@[simp]
lemma formalSectionsMap_refl (n : ℕ) : formalSectionsMap f t F (le_refl n) = 𝟙 _ :=
  ModuleCat.ofSemilinear_eq_id _ _ _ (formalSectionsFun_refl f t F n)

/-- The transition maps compose. -/
lemma formalSectionsMap_comp {l m n : ℕ} (h₁ : l ≤ m) (h₂ : m ≤ n) :
    formalSectionsMap f t F h₂ ≫ formalSectionsMap f t F h₁ =
      formalSectionsMap f t F (h₁.trans h₂) :=
  ModuleCat.ofSemilinear_comp _ _ _ _ _ _ _ _ _ (formalSectionsFun_comp f t F h₁ h₂)

/-- The inverse system `n ↦ Γ(W ×_T T_n, F^{(n)})` of `𝒪_{T, t}`-modules. -/
def formalSectionsSystem : ℕᵒᵖ ⥤ ModuleCat (T.presheaf.stalk t) :=
  Functor.ofOpSequence fun n ↦ formalSectionsMap f t F n.le_succ

@[simp]
lemma formalSectionsSystem_obj (n : ℕ) :
    (formalSectionsSystem f t F).obj (op n) = formalSections f t F n :=
  rfl

lemma formalSectionsSystem_map_succ (n : ℕ) :
    (formalSectionsSystem f t F).map (homOfLE n.le_succ).op = formalSectionsMap f t F n.le_succ :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The transition maps of the inverse system are the maps
`AlgebraicGeometry.Scheme.Modules.formalSectionsMap`, for every `m ≤ n` and not only for
consecutive indices. -/
@[simp]
lemma formalSectionsSystem_map {m n : ℕ} (h : m ≤ n) :
    (formalSectionsSystem f t F).map (homOfLE h).op = formalSectionsMap f t F h := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [show (homOfLE (hmn.trans n.le_succ) : m ⟶ n + 1).op =
        (homOfLE n.le_succ).op ≫ (homOfLE hmn).op from Subsingleton.elim _ _,
      Functor.map_comp, ih, formalSectionsSystem_map_succ, formalSectionsMap_comp]

/-- The map sending a section of `f_* F` over an open neighbourhood `U` of `t` to the
corresponding global section of `F^{(n)}`, which makes sense because `W ×_T T_n` lies over
`U`. -/
def formalSectionsOfNhds (n : ℕ) (U : T.Opens) (hU : t ∈ U) :
    Γ((pushforward f).obj F, U) ⟶ Γ((pullback (infinitesimalBaseChangeFst f t n)).obj F, ⊤) :=
  eqToHom (pushforward_obj_obj f F U) ≫
    sectionsPullbackLE (infinitesimalBaseChangeFst f t n) F
      (preimage_infinitesimalBaseChangeFst_eq_top f t n hU).ge

/-- The maps out of the sections over the open neighbourhoods of `t` are compatible with
restriction, so that they descend to the stalk of `f_* F` at `t`. -/
lemma map_formalSectionsOfNhds (n : ℕ) (U V : T.Opens) (hU : t ∈ U) (hV : t ∈ V)
    (i : op U ⟶ op V) :
    ((pushforward f).obj F).presheaf.map i ≫ formalSectionsOfNhds f t F n V hV =
      formalSectionsOfNhds f t F n U hU := by
  rw [formalSectionsOfNhds, formalSectionsOfNhds, ← Category.assoc, eqToHom_pushforward_map,
    Category.assoc, map_sectionsPullbackLE]

/-- The map out of the sections over an open neighbourhood `U` of `t` is semilinear over the
germ map `Γ(T, U) ⟶ 𝒪_{T, t}` followed by `𝒪_{T, t} ⟶ Γ(W ×_T T_n, 𝒪)`. -/
lemma formalSectionsOfNhds_smul (n : ℕ) (U : T.Opens) (hU : t ∈ U) (r : Γ(T, U))
    (s : Γ((pushforward f).obj F, U)) :
    formalSectionsOfNhds f t F n U hU (r • s) =
      toInfinitesimalBaseChangeΓ f t n (T.presheaf.germ U t hU r) •
        formalSectionsOfNhds f t F n U hU s := by
  have key : (infinitesimalBaseChangeFst f t n).appLE (f ⁻¹ᵁ U) ⊤
      (preimage_infinitesimalBaseChangeFst_eq_top f t n hU).ge (f.app U r) =
      toInfinitesimalBaseChangeΓ f t n (T.presheaf.germ U t hU r) := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appLE,
      infinitesimalBaseChangeFst_comp_appLE f t n hU, ConcreteCategory.comp_apply]
  rw [formalSectionsOfNhds, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    eqToHom_pushforward_smul, sectionsPullbackLE_smul _ _ _ _ _ key]

/-- The maps out of the sections over the open neighbourhoods of `t` are compatible with the
transition maps of the inverse system:

```
                     formalSectionsOfNhds f t F n U hU
  Γ(f_* F, U) ------------------------------------------> Γ(W ×_T T_n, F^{(n)})
             ╲                                                      |
              ╲  formalSectionsOfNhds f t F m U hU                  | formalSectionsFun f t F h
               ╲                                                    v
                ─────────────────────────────────────> Γ(W ×_T T_m, F^{(m)})
```
-/
lemma formalSectionsOfNhds_comp {m n : ℕ} (h : m ≤ n) (U : T.Opens) (hU : t ∈ U) :
    formalSectionsOfNhds f t F n U hU ≫ formalSectionsFun f t F h =
      formalSectionsOfNhds f t F m U hU := by
  have h₃ : (⊤ : (infinitesimalBaseChange f t m).Opens) ≤
      (infinitesimalBaseChangeMap f t h ≫ infinitesimalBaseChangeFst f t n) ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    rw [infinitesimalBaseChangeMap_fst]
    exact (preimage_infinitesimalBaseChangeFst_eq_top f t m hU).ge
  rw [formalSectionsOfNhds, formalSectionsOfNhds, Category.assoc]
  congr 1
  rw [formalSectionsFun, sectionsPullbackOver, sectionsPullback,
    sectionsPullbackLE_comp_assoc _ _ F _ _ h₃, sectionsPullbackLE_congr]

/-- The canonical map from the stalk of `f_* F` at `t` to `Γ(W ×_T T_n, F^{(n)})`, as a map of
`𝒪_{T, t}`-modules. -/
def stalkToFormalSections (n : ℕ) :
    ((pushforward f).obj F).presheaf.stalk t →ₗ[T.presheaf.stalk t] formalSections f t F n :=
  stalkDescₗ _ t _ (formalSectionsOfNhds f t F n) (map_formalSectionsOfNhds f t F n)
    (toInfinitesimalBaseChangeΓ f t n) (formalSectionsOfNhds_smul f t F n)

/-- The maps out of the stalk are compatible with the transition maps of the inverse system:

```
                       stalkToFormalSections f t F n
  (f_* F)_t --------------------------------------------> Γ(W ×_T T_n, F^{(n)})
           ╲                                                       |
            ╲  stalkToFormalSections f t F m                       | formalSectionsMap f t F h
             ╲                                                     v
              ──────────────────────────────────────> Γ(W ×_T T_m, F^{(m)})
```
-/
lemma formalSectionsMap_comp_stalkToFormalSections {m n : ℕ} (h : m ≤ n) :
    (formalSectionsMap f t F h).hom.comp (stalkToFormalSections f t F n) =
      stalkToFormalSections f t F m :=
  ofSemilinear_comp_stalkDescₗ (hgc := fun U hU ↦ formalSectionsOfNhds_comp f t F h U hU) ..

/-- The map out of the stalk kills `𝔪_t ^ (n + 1)`, so that it factors through the quotient of
the stalk by `𝔪_t ^ (n + 1)`. -/
lemma pow_smul_top_le_ker_stalkToFormalSections (n : ℕ) :
    (maximalIdeal (T.presheaf.stalk t) ^ (n + 1) •
        (⊤ : Submodule (T.presheaf.stalk t) (((pushforward f).obj F).presheaf.stalk t))) ≤
      LinearMap.ker (stalkToFormalSections f t F n) := by
  rw [Submodule.smul_le]
  intro r hr z _
  rw [LinearMap.mem_ker, LinearMap.map_smul]
  exact ModuleCat.restrictScalars.smul_eq_zero _ _
    (toInfinitesimalBaseChangeΓ_eq_zero f t n hr) _

/-- The canonical map from the `𝔪_t`-adic completion of the stalk of `f_* F` at `t` to
`Γ(W ×_T T_n, F^{(n)})`: the map out of the stalk factors through the quotient by
`𝔪_t ^ (n + 1)`, which is the `(n + 1)`-st component of the completion. -/
def completedStalkToFormalSections (n : ℕ) :
    completedStalk ((pushforward f).obj F) t →ₗ[T.presheaf.stalk t] formalSections f t F n :=
  (Submodule.liftQ _ (stalkToFormalSections f t F n)
      (pow_smul_top_le_ker_stalkToFormalSections f t F n)).comp
    (AdicCompletion.eval (maximalIdeal (T.presheaf.stalk t)) _ (n + 1))

/-- The map out of the completed stalk extends the map out of the stalk. -/
lemma completedStalkToFormalSections_comp_toCompletedStalk (n : ℕ) :
    (completedStalkToFormalSections f t F n).comp (toCompletedStalk ((pushforward f).obj F) t) =
      stalkToFormalSections f t F n :=
  LinearMap.ext fun z ↦ by
    rw [LinearMap.comp_apply, completedStalkToFormalSections, LinearMap.comp_apply,
      AdicCompletion.eval_of, Submodule.mkQ_apply, Submodule.liftQ_apply]

/-- The maps out of the completed stalk are compatible with the transition maps of the inverse
system:

```
                      completedStalkToFormalSections f t F n
  ((f_* F)_t)^∧ ------------------------------------------------> Γ(W ×_T T_n, F^{(n)})
               ╲                                                            |
                ╲  completedStalkToFormalSections f t F m                   | formalSectionsMap
                 ╲                                                          v
                  ───────────────────────────────────────> Γ(W ×_T T_m, F^{(m)})
```
-/
lemma formalSectionsMap_comp_completedStalkToFormalSections {m n : ℕ} (h : m ≤ n) :
    (formalSectionsMap f t F h).hom.comp (completedStalkToFormalSections f t F n) =
      completedStalkToFormalSections f t F m := by
  rw [completedStalkToFormalSections, completedStalkToFormalSections, ← LinearMap.comp_assoc,
    Submodule.comp_liftQ]
  simp only [formalSectionsMap_comp_stalkToFormalSections]
  rw [← AdicCompletion.transitionMap_comp_eval _ _ (Nat.add_le_add_right h 1),
    ← LinearMap.comp_assoc, Submodule.liftQ_comp_factor]

/-- `AlgebraicGeometry.Scheme.Modules.completedStalkToFormalSections` as a morphism of
`𝒪_{T, t}`-modules.

The source and target are spelled out because `ModuleCat.ofHom` would elaborate its target as
`ModuleCat.of _ Γ(W ×_T T_n, F^{(n)})`, which unfolds the restriction of scalars in
`formalSections` and loses the `𝒪_{T, t}`-module structure. -/
def completedStalkToFormalSectionsHom (n : ℕ) :
    ModuleCat.of (T.presheaf.stalk t) (completedStalk ((pushforward f).obj F) t) ⟶
      formalSections f t F n :=
  ConcreteCategory.ofHom (C := ModuleCat (T.presheaf.stalk t))
    (X := ModuleCat.of (T.presheaf.stalk t) (completedStalk ((pushforward f).obj F) t))
    (Y := formalSections f t F n) (completedStalkToFormalSections f t F n)

/-- The cone on the inverse system `n ↦ Γ(W ×_T T_n, F^{(n)})` with vertex the `𝔪_t`-adic
completion of the stalk of `f_* F` at `t`. -/
def formalSectionsCone : Cone (formalSectionsSystem f t F) where
  pt := ModuleCat.of (T.presheaf.stalk t) (completedStalk ((pushforward f).obj F) t)
  π := NatTrans.ofOpSequence
    (fun n ↦ completedStalkToFormalSectionsHom f t F n)
    (fun n ↦ by
      rw [formalSectionsSystem_map_succ]
      refine (Category.id_comp _).trans ?_
      exact (ModuleCat.hom_ext
        (formalSectionsMap_comp_completedStalkToFormalSections f t F n.le_succ)).symm)

/-- **The comparison map of the theorem on formal functions**, in degree zero: the canonical map
from the `𝔪_t`-adic completion of the stalk of `f_* F` at `t` to the inverse limit of the
modules `Γ(W ×_T T_n, F^{(n)})`. -/
def formalFunctionsComparison :
    ModuleCat.of (T.presheaf.stalk t) (completedStalk ((pushforward f).obj F) t) ⟶
      limit (formalSectionsSystem f t F) :=
  limit.lift _ (formalSectionsCone f t F)

/-- The `n`-th component of the comparison map is
`AlgebraicGeometry.Scheme.Modules.completedStalkToFormalSections`. -/
@[reassoc (attr := simp)]
lemma formalFunctionsComparison_π (n : ℕ) :
    formalFunctionsComparison f t F ≫ limit.π (formalSectionsSystem f t F) (op n) =
      completedStalkToFormalSectionsHom f t F n :=
  limit.lift_π _ _

/-- **The theorem on formal functions**, in degree zero.

For a locally noetherian scheme `T`, a proper morphism `f : W ⟶ T` and a coherent sheaf of
`𝒪_W`-modules `F`, the comparison map from the `𝔪_t`-adic completion of the stalk of `f_* F`
at `t` to the inverse limit of the modules `Γ(W ×_T T_n, F^{(n)})` is an isomorphism. This is
`prop:cube-formal-functions` of the blueprint.

This is the degree-zero case of [Stacks, 02OC] and is `sorry` by design; see the implementation
notes of this file. -/
@[stacks 02OC]
theorem isIso_formalFunctionsComparison [IsLocallyNoetherian T] [IsProper f] [F.IsCoherent] :
    IsIso (formalFunctionsComparison f t F) :=
  sorry

end FormalSections

end AlgebraicGeometry.Scheme.Modules
