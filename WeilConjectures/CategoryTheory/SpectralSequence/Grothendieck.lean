/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.SpectralObject

/-!
# The Grothendieck spectral sequence

Let `A ⥤ B ⥤ C` be left exact additive functors such that `F` sends injective objects of `A` to
`G`-acyclic objects of `B`. Then for every `X : A` there is a first quadrant cohomological
spectral sequence with `E₂`-page `R^p G (R^q F X)` abutting to `R^{p + q} (F ⋙ G) X`.

Convergence is expressed through `CategoryTheory.SpectralSequence.AbutsTo` of
`WeilConjectures/Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`; the blueprint's
`sk-def-groth-ss` describes both the acyclicity hypothesis on the pair `(F, G)` and the image
filtration attached to a first quadrant double complex, and the second half of that subsection
is what `SpectralSequence.Abutment` records.

## The construction

The blueprint builds the spectral sequence from a Cartan–Eilenberg resolution of `F(I)`, `I` an
injective resolution of `X`. We use instead the equivalent construction through the canonical
t-structure on the bounded below derived category `D⁺(B)`, for which Mathlib provides spectral
objects and their spectral sequences. Let `K = RF(X) = R⁺F(X[0]) ∈ D⁺(B)`. To `a ≤ b` in `EInt`
and `n : ℤ` we attach `Hⁿ(RG(τ_{≥ a} τ_{< b} K))`; this is a first quadrant spectral object in
`C` (`Functor.grothendieckSpectralObject`), whose `E₂` spectral sequence is the Grothendieck
spectral sequence (`Functor.grothendieckSpectralSequence`). Its `E₂`-terms are
`H^{p+q}(RG(τ_{≥ q} τ_{< q+1} K)) = H^{p+q}(RG((R^q F X)[-q])) = R^p G (R^q F X)`, and it
converges to `Hⁿ(RG(K))`, which is `Hⁿ(G(F(I))) = R^n (F ⋙ G) X` because `F(I)` is a complex
of `G`-acyclic objects. The two filtrations of the Cartan–Eilenberg double complex in the
blueprint are replaced by the truncation filtration (giving the `E₂`-page) and the
identification of the abutment through acyclic resolutions.

## Main definitions

- `CategoryTheory.Functor.IsAcyclicComposablePair`: a composable pair with acyclicity.
- `CategoryTheory.Functor.grothendieckSpectralObjectFunctor`,
  `CategoryTheory.Functor.grothendieckSpectralObject`: the spectral object of the Grothendieck
  spectral sequence, functorially in `X`.
- `CategoryTheory.Functor.grothendieckSpectralSequence`: the Grothendieck spectral sequence.
- `CategoryTheory.Functor.grothendieckBottomEdge`, `CategoryTheory.Functor.grothendieckLeftEdge`:
  the edge maps `R^n G (F X) ⟶ R^n (F ⋙ G) X ⟶ G (R^n F X)` (blueprint
  `lem-sp-grothendieck-edge-maps`).

## Main statements

- `CategoryTheory.Adjunction.isAcyclicComposablePair`: a right adjoint of an exact functor gives
  a composable pair with acyclicity.
- `CategoryTheory.Functor.nonempty_grothendieckSpectralSequence_page_two_iso`,
  `CategoryTheory.Functor.grothendieckSpectralSequence_abutsTo`: the `E₂`-page and the abutment.
- `CategoryTheory.Functor.exists_grothendieckSpectralObjectFunctor_baseChange`: base-change
  naturality (blueprint `thm-sp-grothendieck-base-change`; not proved yet).
- `CategoryTheory.Functor.exists_grothendieckSpectralSequence`: the Grothendieck spectral
  sequence of a composable pair with acyclicity.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory

open Limits ComposableArrows

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{v₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C]

/-- The pair of additive functors `A ⥤ B ⥤ C` is a *composable pair with acyclicity* if `F` sends
every injective object `I` of `A` to a `G`-acyclic object of `B`, that is, one at which all the
higher right derived functors `R^q G` for `q > 0` vanish. This is what makes an injective
resolution of `X : A` compute `R^n (F ⋙ G) X` after applying `F`, and hence what makes the
Grothendieck spectral sequence of `Functor.exists_grothendieckSpectralSequence` exist.

(blueprint: `sk-def-groth-ss`) -/
def Functor.IsAcyclicComposablePair (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] : Prop :=
  ∀ (I : A) [Injective I] (q : ℕ), 0 < q → IsZero ((G.rightDerived q).obj (F.obj I))

omit [IsGrothendieckAbelian.{v₁} A] in
/-- If `F` preserves injective objects, then `(F, G)` is a composable pair with acyclicity, since
the higher right derived functors of `G` vanish on injective objects. -/
theorem Functor.isAcyclicComposablePair_of_preservesInjectiveObjects (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] [F.PreservesInjectiveObjects] : F.IsAcyclicComposablePair G := by
  intro I _ q hq
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by lia⟩
  exact G.isZero_rightDerived_obj_injective_succ q (F.obj I)

omit [IsGrothendieckAbelian.{v₁} A] in
/-- **The acyclicity hypothesis for a right adjoint of an exact functor.** If `F : A ⥤ B` has a
left adjoint `u` which is exact (it is enough that `u` preserves finite limits), then `F` preserves
injective objects (`lem-sp-right-adjoint-preserves-injectives`), so `(F, G)` is a composable pair
with acyclicity for every `G`. This is the situation of `F = f_*`, `u = f⁻¹` for a morphism of
sites `f` (Step 1 of the proof of `sk-thm-groth-ss`). -/
theorem Adjunction.isAcyclicComposablePair {u : B ⥤ A} {F : A ⥤ B} (adj : u ⊣ F)
    [PreservesFiniteLimits u] (G : B ⥤ C) [F.Additive] [G.Additive] :
    F.IsAcyclicComposablePair G :=
  have := adj.preservesInjectiveObjects_of_preservesFiniteLimits
  F.isAcyclicComposablePair_of_preservesInjectiveObjects G

namespace Functor

variable (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

variable [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]

/-- The object `RF(X) = R⁺F(X[0])` of `D⁺(B)` is cohomologically `≥ 0`. -/
instance (X : A) : DerivedCategory.Plus.TStructure.t.IsGE
    (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)) 0 := by
  have : DerivedCategory.Plus.TStructure.t.IsGE
      (DerivedCategory.Plus.Q.obj (F.rightDerivedPlusComplex X)) 0 := by
    refine (DerivedCategory.Plus.isGE_ι_obj_iff _ 0).1 ?_
    have : (F.rightDerivedPlusComplex X).obj.IsStrictlyGE 0 :=
      inferInstanceAs (CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex _).obj
        (injectiveResolution X).cochainComplex) 0)
    exact DerivedCategory.TStructure.t.isGE_of_iso
      ((DerivedCategory.quotientCompQhIso B).app (F.rightDerivedPlusComplex X).obj).symm 0
  exact DerivedCategory.Plus.TStructure.t.isGE_of_iso
    (F.rightDerivedFunctorPlusObjSingleFunctorIsoQ X).symm 0

/-- The functor sending `X : A` to the spectral object in `C` whose spectral sequence is the
Grothendieck spectral sequence of `X`: to `a ≤ b` in `EInt` and `n : ℤ` it attaches
`H^n(RG(τ_{≥ a} τ_{< b} RF(X)))`, where `RF(X) = R⁺F(X[0])` and `τ` denotes the truncations for
the canonical t-structure on `D⁺(B)`. -/
noncomputable def grothendieckSpectralObjectFunctor : A ⥤ Abelian.SpectralObject C EInt :=
  DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.TStructure.t.spectralObjectFunctor ⋙
    G.rightDerivedFunctorPlus.mapTriangulatedSpectralObject EInt ⋙
    (DerivedCategory.Plus.homologyFunctor C 0).mapHomologicalSpectralObject EInt

/-- The spectral object of the Grothendieck spectral sequence of `X : A`, see
`Functor.grothendieckSpectralObjectFunctor`. -/
noncomputable abbrev grothendieckSpectralObject (X : A) : Abelian.SpectralObject C EInt :=
  (F.grothendieckSpectralObjectFunctor G).obj X

instance (X : A) : (F.grothendieckSpectralObject G X).IsFirstQuadrant where
  isZero₁ i j hij hj n := by
    let t := DerivedCategory.Plus.TStructure.t (C := B)
    let K := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)
    have := t.isZero_eTruncLT_obj_obj K 0 j hj
    change IsZero (((DerivedCategory.Plus.homologyFunctor C 0).shift n).obj
      (G.rightDerivedFunctorPlus.obj ((t.eTruncGE.obj i).obj ((t.eTruncLT.obj j).obj K))))
    exact Functor.map_isZero _ (Functor.map_isZero _ (Functor.map_isZero _ this))
  isZero₂ i j hij n hi := by
    let t := DerivedCategory.Plus.TStructure.t (C := B)
    let K := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)
    have := t.isGE_eTruncGE_obj_obj (n + 1) i (by
      induction i using WithBotTop.rec with
      | bot => simp at hi
      | coe i => simp at hi ⊢; lia
      | top => simp) ((t.eTruncLT.obj j).obj K)
    exact G.isZero_homology_rightDerivedFunctorPlus_obj_of_isGE
      ((t.eTruncGE.obj i).obj ((t.eTruncLT.obj j).obj K)) (n + 1) n (by lia)

/-- The Grothendieck spectral sequence of `X : A`, the first quadrant `E₂` spectral sequence of
the spectral object `Functor.grothendieckSpectralObject`. -/
noncomputable def grothendieckSpectralSequence (X : A) : E₂CohomologicalSpectralSequenceNat C :=
  (F.grothendieckSpectralObject G X).E₂SpectralSequenceNat

/-- The terms `H^{p+q}(RG(τ_{≥ q} τ_{< q+1} RF(X)))` of the spectral object of the Grothendieck
spectral sequence, which give its `E₂`-page, are `R^p G (R^q F X)`. Indeed
`τ_{≥ q} τ_{< q+1} RF(X) ≅ (R^q F X)[-q]`. -/
theorem nonempty_grothendieckSpectralObject_H_iso (X : A) (p q : ℕ) (n a b : ℤ)
    (hn : n = p + q) (ha : a = q) (hb : b = q + 1) :
    Nonempty (((F.grothendieckSpectralObject G X).H n).obj
        (mk₁ (homOfLE (show (a : EInt) ≤ b by simp [ha, hb]))) ≅
      (G.rightDerived p).obj ((F.rightDerived q).obj X)) := by
  subst hn ha hb
  let K := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)
  let H₀ := DerivedCategory.Plus.homologyFunctor C 0
  let M := (DerivedCategory.Plus.homologyFunctor B q).obj K
  obtain ⟨e₁⟩ := DerivedCategory.Plus.nonempty_eTruncGE_eTruncLT_iso_singleFunctor K q
  let e₂ : M ≅ (F.rightDerived q).obj X :=
    F.homologyRightDerivedFunctorPlusObjSingleFunctorIso X q
  let e₃ := G.homologyRightDerivedFunctorPlusObjSingleFunctorIso M p
  let e₄ := ((DerivedCategory.Plus.singleFunctors B).shiftIso (-(q : ℤ)) q 0 (by simp)).app M
  let e₅ := (G.rightDerivedFunctorPlus.commShiftIso (-(q : ℤ))).app
    ((DerivedCategory.Plus.singleFunctor B 0).obj M)
  let e₆ := (H₀.shiftIso (-(q : ℤ)) ((p : ℤ) + q) p (by ring)).app
    (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj M))
  exact ⟨(H₀.shift ((p : ℤ) + q)).mapIso
    (G.rightDerivedFunctorPlus.mapIso (e₁ ≪≫ e₄.symm) ≪≫ e₅) ≪≫
    e₆ ≪≫ e₃ ≪≫ (G.rightDerived p).mapIso e₂⟩

/-- The `E₂`-page of the Grothendieck spectral sequence is `E₂^{p,q} = R^p G (R^q F X)`. -/
theorem nonempty_grothendieckSpectralSequence_page_two_iso (X : A) (p q : ℕ) :
    Nonempty (((F.grothendieckSpectralSequence G X).page 2).X (p, q) ≅
      (G.rightDerived p).obj ((F.rightDerived q).obj X)) := by
  obtain ⟨e⟩ := F.nonempty_grothendieckSpectralObject_H_iso G X p q (p + q : ℕ) q (q + 1)
    (by push_cast; rfl) rfl rfl
  exact ⟨(F.grothendieckSpectralObject G X).E₂SpectralSequenceNatPageTwoXIso p q ≪≫ e⟩

/-- For a composable pair with acyclicity, the term `Hⁿ(RG(RF(X)))` of the spectral object of
the Grothendieck spectral sequence, to which it abuts, is `R^n (F ⋙ G) X`. -/
theorem nonempty_grothendieckSpectralObject_H_bot_top_iso [PreservesFiniteLimits G]
    (hFG : F.IsAcyclicComposablePair G) (X : A) (n : ℕ) :
    Nonempty (((F.grothendieckSpectralObject G X).H n).obj
        (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≅ ((F ⋙ G).rightDerived n).obj X) := by
  let t := DerivedCategory.Plus.TStructure.t (C := B)
  let K := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)
  have hK : (t.eTruncGE.obj ⊥).obj ((t.eTruncLT.obj ⊤).obj K) = K := by
    rw [t.eTruncGE_obj_bot, t.eTruncLT_obj_top]
    rfl
  have hL (k : ℤ) : G.rightAcyclic ((F.rightDerivedPlusComplex X).obj.X k) :=
    fun q ↦ hFG _ (q + 1) (by lia)
  obtain ⟨e⟩ := G.nonempty_homology_rightDerivedFunctorPlus_obj_Q_iso _ hL n
  exact ⟨(DerivedCategory.Plus.homologyFunctor C n).mapIso
    (G.rightDerivedFunctorPlus.mapIso (eqToIso hK ≪≫
      F.rightDerivedFunctorPlusObjSingleFunctorIsoQ X)) ≪≫ e ≪≫
      ((injectiveResolution X).isoRightDerivedObjCochainComplex (F ⋙ G) n).symm⟩

/-- The Grothendieck spectral sequence of a composable pair with acyclicity abuts to
`R^n (F ⋙ G) X`. -/
theorem grothendieckSpectralSequence_abutsTo [PreservesFiniteLimits G]
    (hFG : F.IsAcyclicComposablePair G) (X : A) :
    (F.grothendieckSpectralSequence G X).AbutsTo (fun n ↦ ((F ⋙ G).rightDerived n).obj X) :=
  (F.grothendieckSpectralObject G X).abutsTo_E₂SpectralSequenceNat.of_nonempty_iso
    (F.nonempty_grothendieckSpectralObject_H_bot_top_iso G hFG X)

/-- The *bottom edge map* `E₂^{n,0} ⟶ Hⁿ` of the Grothendieck spectral sequence, as a natural
transformation in `X : A`. Its source `H^n(RG(τ_{≥ 0} τ_{< 1} RF(X)))` is `R^n G (F X)` when `F`
is left exact (`Functor.nonempty_grothendieckSpectralObject_H_zero_one_iso`) and its target
`H^n(RG(RF(X)))` is `R^n (F ⋙ G) X` for a composable pair with acyclicity
(`Functor.nonempty_grothendieckSpectralObject_H_bot_top_iso`): this is the edge map
`R^n G (F X) ⟶ R^n (F ⋙ G) X`. It is the composite `E₂^{n,0} ↠ E∞^{n,0} = Fⁿ Hⁿ ↪ Hⁿ`, its image
being the last step of the abutment filtration
(`Abelian.SpectralObject.imageSubobject_bottomEdge`).

(blueprint: `lem-sp-grothendieck-edge-maps`) -/
noncomputable def grothendieckBottomEdge (n : ℤ) :
    F.grothendieckSpectralObjectFunctor G ⋙ Abelian.SpectralObject.hFunctor n
        (mk₁ (homOfLE (show ((0 : ℤ) : EInt) ≤ ((1 : ℤ) : EInt) by simp))) ⟶
      F.grothendieckSpectralObjectFunctor G ⋙ Abelian.SpectralObject.hFunctor n
        (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) where
  app X := (F.grothendieckSpectralObject G X).bottomEdge n
  naturality _ _ f :=
    Abelian.SpectralObject.bottomEdge_naturality ((F.grothendieckSpectralObjectFunctor G).map f) n

/-- The *left edge map* `Hⁿ ⟶ E₂^{0,n}` of the Grothendieck spectral sequence, as a natural
transformation in `X : A`. Its source `H^n(RG(RF(X)))` is `R^n (F ⋙ G) X` for a composable pair
with acyclicity (`Functor.nonempty_grothendieckSpectralObject_H_bot_top_iso`) and its target
`H^n(RG(τ_{≥ n} τ_{< n+1} RF(X)))` is `G (R^n F X)` when `G` is left exact
(`Functor.nonempty_grothendieckSpectralObject_H_self_succ_iso`): this is the edge map
`R^n (F ⋙ G) X ⟶ G (R^n F X)`.

(blueprint: `lem-sp-grothendieck-edge-maps`) -/
noncomputable def grothendieckLeftEdge (n : ℤ) :
    F.grothendieckSpectralObjectFunctor G ⋙ Abelian.SpectralObject.hFunctor n
        (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ⟶
      F.grothendieckSpectralObjectFunctor G ⋙ Abelian.SpectralObject.hFunctor n
        (mk₁ (homOfLE (show ((n : ℤ) : EInt) ≤ ((n + 1 : ℤ) : EInt) by simp))) where
  app X := (F.grothendieckSpectralObject G X).leftEdge n
  naturality _ _ f :=
    Abelian.SpectralObject.leftEdge_naturality ((F.grothendieckSpectralObjectFunctor G).map f) n

/-- The source of the bottom edge map is `R^n G (F X)`. -/
theorem nonempty_grothendieckSpectralObject_H_zero_one_iso [PreservesFiniteLimits F] (X : A)
    (n : ℕ) :
    Nonempty (((F.grothendieckSpectralObject G X).H n).obj
        (mk₁ (homOfLE (show ((0 : ℤ) : EInt) ≤ ((1 : ℤ) : EInt) by simp))) ≅
      (G.rightDerived n).obj (F.obj X)) := by
  obtain ⟨e⟩ := F.nonempty_grothendieckSpectralObject_H_iso G X n 0 n 0 1 (by simp) rfl rfl
  exact ⟨e ≪≫ (G.rightDerived n).mapIso (F.rightDerivedZeroIsoSelf.app X)⟩

/-- The target of the left edge map is `G (R^n F X)`. -/
theorem nonempty_grothendieckSpectralObject_H_self_succ_iso [PreservesFiniteLimits G] (X : A)
    (n : ℕ) :
    Nonempty (((F.grothendieckSpectralObject G X).H n).obj
        (mk₁ (homOfLE (show ((n : ℤ) : EInt) ≤ ((n + 1 : ℤ) : EInt) by simp))) ≅
      G.obj ((F.rightDerived n).obj X)) := by
  obtain ⟨e⟩ := F.nonempty_grothendieckSpectralObject_H_iso G X 0 n n n (n + 1) (by simp) rfl rfl
  exact ⟨e ≪≫ G.rightDerivedZeroIsoSelf.app _⟩

section BaseChange

variable {A' : Type u₄} [Category.{v₄} A'] [Abelian A'] [IsGrothendieckAbelian.{v₄} A']
  {B' : Type u₅} [Category.{v₅} B'] [Abelian B'] [IsGrothendieckAbelian.{v₅} B']
  {C' : Type u₆} [Category.{v₆} C'] [Abelian C']
  [HasDerivedCategory A'] [HasDerivedCategory B'] [HasDerivedCategory C']
  (F' : A' ⥤ B') (G' : B' ⥤ C') [F'.Additive] [G'.Additive]

/-- **Base-change naturality of the Grothendieck spectral sequence.** Let `α : A ⥤ A'`,
`β : B ⥤ B'` and `γ : C ⥤ C'` be exact functors making the squares
```
    A ──F──▶ B ──G──▶ C
    │α       │β       │γ
    ▼        ▼        ▼
    A' ─F'─▶ B' ─G'─▶ C'
```
commute up to the natural isomorphisms `eF : F ⋙ β ≅ α ⋙ F'` and `eG : G ⋙ γ ≅ β ⋙ G'`. Then
there is a morphism, natural in `X : A`, from the image under `γ` of the spectral object of the
Grothendieck spectral sequence of `X` to the spectral object of the Grothendieck spectral
sequence of `α X`; it induces the morphism of spectral sequences between `γ` applied to the
Grothendieck spectral sequence of `(F, G, X)` and that of `(F', G', α X)`. It is built from the
base-change morphisms `γ ∘ RG ⟶ RG' ∘ β` and `β ∘ RF ⟶ RF' ∘ α` of the right derived functors,
using that the exact functor `β` commutes with the truncations of the canonical t-structures.
When `α` and `β` preserve injective objects these base-change morphisms are isomorphisms, and so
is the morphism of spectral objects.

In the base-change situation of the proper-base-change chapter the vertical functors are the
inverse images along the maps of a cartesian square.

(blueprint: `thm-sp-grothendieck-base-change`) -/
theorem exists_grothendieckSpectralObjectFunctor_baseChange
    (α : A ⥤ A') (β : B ⥤ B') (γ : C ⥤ C') [α.Additive] [β.Additive] [γ.Additive]
    [PreservesFiniteLimits α] [PreservesFiniteColimits α]
    [PreservesFiniteLimits β] [PreservesFiniteColimits β] [γ.PreservesHomology]
    (eF : F ⋙ β ≅ α ⋙ F') (eG : G ⋙ γ ≅ β ⋙ G') :
    ∃ φ : F.grothendieckSpectralObjectFunctor G ⋙ γ.mapAbelianSpectralObject EInt ⟶
        α ⋙ F'.grothendieckSpectralObjectFunctor G',
      α.PreservesInjectiveObjects → β.PreservesInjectiveObjects → IsIso φ := by
  sorry

end BaseChange

end Functor

/-- **The Grothendieck spectral sequence.** If `F : A ⥤ B` and `G : B ⥤ C` are left exact
additive functors forming a composable pair with acyclicity

```
    A ───── F ─────▶ B ───── G ─────▶ C
     ╲                                ▲
      ╲───────────── F ⋙ G ──────────╱
```

then for every `X : A` there is a first quadrant cohomological spectral sequence with
`E₂^{p, q} ≅ R^p G (R^q F X)` abutting to `R^{p + q} (F ⋙ G) X`.

For `A` the abelian sheaves on a site `X`, `F = f_*` and `G = h_*` along morphisms of sites
`X ⥤ Y ⥤ Z`, the acyclicity hypothesis holds because `f_*` is right adjoint to the exact functor
`f^{-1}` and hence preserves injectives, and the statement specializes to
`R^p h_* R^q f_* F ⟹ R^{p + q} (h ∘ f)_* F`. Taking `Z` to be the punctual site, so that
`h_* = Γ(Y, -)`, it specializes further to the Leray spectral sequence
`H^p(Y, R^q f_* F) ⟹ H^{p + q}(X, F)`.

(blueprint: `sk-thm-groth-ss`) -/
theorem Functor.exists_grothendieckSpectralSequence (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : F.IsAcyclicComposablePair G) (X : A) :
    ∃ E : E₂CohomologicalSpectralSequenceNat C,
      (∀ p q : ℕ,
        Nonempty ((E.page 2).X (p, q) ≅ (G.rightDerived p).obj ((F.rightDerived q).obj X))) ∧
      E.AbutsTo (fun n ↦ ((F ⋙ G).rightDerived n).obj X) := by
  let := HasDerivedCategory.standard A
  let := HasDerivedCategory.standard B
  let := HasDerivedCategory.standard C
  exact ⟨F.grothendieckSpectralSequence G X,
    F.nonempty_grothendieckSpectralSequence_page_two_iso G X,
    F.grothendieckSpectralSequence_abutsTo G hFG X⟩

end CategoryTheory
