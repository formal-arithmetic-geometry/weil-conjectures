/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.Compactification.OverRefinement
public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import all Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!

# Independence of the lower shriek of `E`- and `ℚ̄_ℓ`-sheaves from the compactification

Let `ℓ` be a prime and `E` a finite extension of `ℚ_ℓ`, with condensed ring `E̲ = C(-, E)`
(`Profinite.continuousMapRingObj E`), and let `ℚ̲̄_ℓ = Profinite.padicAlgClRingObj ℓ`. For a
compactification `c = (X ⟶[i] Z ⟶[p] Y)` of `f`, the lower shriek on bounded constructible
complexes is `Rf_!^c := i_! ⋙ Rp_*`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactification`). This file shows
that, for the coefficient rings `E̲` and `ℚ̲̄_ℓ`, it does not depend on the compactification: for
two compactifications `c₁` and `c₂` of `f`, `Rf_!^{c₁} ≅ Rf_!^{c₂}`.

These isomorphisms identify the lower shriek attached to an arbitrary compactification with the
lower shriek `Rf_!` for the chosen compactification
(`ProEtale.CondensedRing.boundedConstructibleLowerShriek`), as used in the compact-support
base-change morphism `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange`.

As for the bounded constructible six functors
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`), all schemes
are separated and of finite type over a field `k` of characteristic `p > 0` with `p ≠ ℓ`, and all
morphisms are morphisms of `Over (Spec (.of k))`.

## The construction

Let `h : Z ⟶ Z₁` be a morphism over `Y` from a compactification `c = (X ⟶[i] Z ⟶[p] Y)` to a
compactification `c₁ = (X ⟶[i₁] Z₁ ⟶[p₁] Y)`, with `i ≫ h = i₁` and `h ≫ p₁ = p`.

1. The *restriction comparison* `i_! ⟶ i₁_! ⋙ Lh^*` is the transpose under `i_! ⊣ Li^*` of the
   unit `𝟭 ⟶ i₁_! ⋙ Li₁^*` of `i₁_! ⊣ Li₁^*`, followed by `Li₁^* ≅ L(i ≫ h)^* ≅ Lh^* ⋙ Li^*`
   (`boundedConstructibleOpenImmersionLowerShriekRefinement`). It is an isomorphism when the
   square of `i`, `i₁` and `h` is cartesian, that is when `h⁻¹(X) = X`: then `h^* i₁_! K` is the
   extension by zero of `K` from `X ⊆ Z`.
2. For such a cartesian square, the *pushforward comparison* `i₁_! ⟶ i_! ⋙ Rh_*` is the unit of
   `Lh^* ⊣ Rh_*` followed by the inverse of the restriction comparison
   (`boundedConstructibleOpenImmersionLowerShriekRefinementPushforward`). It is an isomorphism
   when `h` is proper, by proper base change along the closed complement of `X ⊆ Z₁`, over which
   `Rh_*(i_! K)` vanishes.
3. Then `Rf_!^{c₁} = i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rh_* ⋙ Rp₁_* ≅ i_! ⋙ Rp_* = Rf_!^c`, through the
   composition isomorphism `Rh_* ⋙ Rp₁_* ≅ R(h ≫ p₁)_*`
   (`boundedConstructibleLowerShriekRefinementIso`).

Any two compactifications `c₁` and `c₂` of `f` have a common refinement `c`
(`Compactification.exists_overRefinement`), and `Rf_!^{c₁} ≅ Rf_!^c ≅ Rf_!^{c₂}`.

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleLowerShriekRefinementIso`: `Rf_!^{c₁} ≅ Rf_!^c`
  along a refinement, for any `Λ` for which the pushforward comparison is an isomorphism.
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso` and
  `ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl`: the
  isomorphism `Rf_!^{c₁} ≅ Rf_!^{c₂}` for `E`- and `ℚ̄_ℓ`-sheaves.

## Sorried input

- `ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekRefinement`: the
  restriction comparison is an isomorphism for a cartesian square.
- `ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward`
  and its `_padicAlgCl` version: the pushforward comparison is an isomorphism for `h` proper.
- `Compactification.exists_overRefinement`: the existence of common refinements.

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

/-- For a commutative square whose top morphism is an identity, the left morphism followed by the
right morphism is the bottom morphism. -/
lemma CategoryTheory.CommSq.snd_comp_eq_of_fst_eq_id {C : Type*} [Category C] {X Z Z₁ : C}
    {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁} (sq : CommSq (𝟙 X) i i₁ h) : i ≫ h = i₁ := by
  simpa using sq.w.symm

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### The comparisons along a refinement -/

section Refinement

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Z Z₁ : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom]
  {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left]

include ℓ k

/-- The *triangle comparison* `Li₁^* ≅ Lh^* ⋙ Li^*` on bounded constructible complexes for
morphisms `i : X ⟶ Z`, `h : Z ⟶ Z₁` and `i₁ : X ⟶ Z₁` with `i ≫ h = i₁`: the composition
isomorphism `boundedConstructibleUpperStarComp` for `i₁ = i ≫ h`. It plays the role of the
pullback comparison `boundedConstructiblePullbackSquareComparison` of the square with top `𝟙 X`,
without the pullback along `𝟙 X`. -/
noncomputable def boundedConstructibleUpperStarTriangleComparison (w : i ≫ h = i₁) :
    boundedConstructibleUpperStar Λ ℓ i₁ ≅
      boundedConstructibleUpperStar Λ ℓ h ⋙ boundedConstructibleUpperStar Λ ℓ i :=
  eqToIso (by rw [w]) ≪≫ boundedConstructibleUpperStarComp Λ ℓ i h

/-- The *unit insertion* step of the restriction comparison: the natural transformation
`i_! ⟶ (i₁_! ⋙ Li₁^*) ⋙ i_!` obtained by inserting the unit of the adjunction
`i₁_! ⊣ Li₁^*`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekRefinementUnitStep :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ i ⟶
      (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁ ⋙
        boundedConstructibleUpperStar Λ ℓ i₁) ⋙
        boundedConstructibleOpenImmersionLowerShriek Λ ℓ i :=
  (Functor.leftUnitor _).inv ≫ Functor.whiskerRight
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i₁).unit
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i)

/-- The *triangle transport* step of the restriction comparison: `Functor.squareTransport`
applied to the triangle comparison `Li₁^* ≅ Lh^* ⋙ Li^*`, under `i₁_!` on the left and `i_!`
on the right. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekRefinementTriangleStep
    (w : i ≫ h = i₁) :
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁ ⋙
        boundedConstructibleUpperStar Λ ℓ i₁) ⋙
        boundedConstructibleOpenImmersionLowerShriek Λ ℓ i ≅
      (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁ ⋙
        boundedConstructibleUpperStar Λ ℓ h) ⋙
        (boundedConstructibleUpperStar Λ ℓ i ⋙
          boundedConstructibleOpenImmersionLowerShriek Λ ℓ i) :=
  Functor.squareTransport (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁)
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i)
    (Functor.rightUnitor _ ≪≫ boundedConstructibleUpperStarTriangleComparison Λ ℓ w)

/-- The *counit contraction* step of the restriction comparison: the natural transformation
`(i₁_! ⋙ Lh^*) ⋙ (Li^* ⋙ i_!) ⟶ i₁_! ⋙ Lh^*` obtained by contracting the counit of the
adjunction `i_! ⊣ Li^*`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekRefinementCounitStep :
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁ ⋙
        boundedConstructibleUpperStar Λ ℓ h) ⋙
        (boundedConstructibleUpperStar Λ ℓ i ⋙
          boundedConstructibleOpenImmersionLowerShriek Λ ℓ i) ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁ ⋙ boundedConstructibleUpperStar Λ ℓ h :=
  Functor.whiskerLeft _
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i).counit ≫
    (Functor.rightUnitor _).hom

/-- The *restriction comparison* `i_! ⟶ i₁_! ⋙ Lh^*` on bounded constructible complexes, for open
immersions `i : X ⟶ Z` and `i₁ : X ⟶ Z₁` and a morphism `h : Z ⟶ Z₁` with `i ≫ h = i₁`,
assembled as the composite of the unit insertion, the triangle transport along
`Li₁^* ≅ Lh^* ⋙ Li^*`, and the counit contraction:
`i_! ⟶ i₁_! ⋙ Li₁^* ⋙ i_! ≅ i₁_! ⋙ Lh^* ⋙ Li^* ⋙ i_! ⟶ i₁_! ⋙ Lh^*`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekRefinement (w : i ≫ h = i₁) :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ i ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁ ⋙ boundedConstructibleUpperStar Λ ℓ h :=
  boundedConstructibleOpenImmersionLowerShriekRefinementUnitStep Λ ℓ ≫
    (boundedConstructibleOpenImmersionLowerShriekRefinementTriangleStep Λ ℓ w).hom ≫
    boundedConstructibleOpenImmersionLowerShriekRefinementCounitStep Λ ℓ

/-- The restriction comparison `i_! ⟶ i₁_! ⋙ Lh^*` is an isomorphism when the square
```
X --i--> Z
|𝟙       |h
v        v
X --i₁-> Z₁
```
is cartesian: since `h⁻¹(X) = X`, on stalks at points of `Z_proét` both sides are the stalk of
`K` at points of `X` and vanish outside `X`. -/
theorem isIso_boundedConstructibleOpenImmersionLowerShriekRefinement
    (sq : IsPullback (𝟙 X) i i₁ h) :
    IsIso (boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ
      sq.toCommSq.snd_comp_eq_of_fst_eq_id) := by
  have : IsIso (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i₁).unit :=
    sharedBoundedOpenUnitIsIso Λ ℓ i₁
  have hcomponent (K : _) :
      IsIso ((boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ
        sq.toCommSq.snd_comp_eq_of_fst_eq_id).app K) := by
    have : IsIso ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
        Λ ℓ i).counit.app ((boundedConstructibleUpperStar Λ ℓ h).obj
          ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K))) :=
      boundedCartesianCounit Λ ℓ sq K
    have : IsIso ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
        Λ ℓ i₁).unit.app K) := inferInstance
    have : IsIso ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i).map
        ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
          Λ ℓ i₁).unit.app K)) := Functor.map_isIso _ _
    unfold boundedConstructibleOpenImmersionLowerShriekRefinement
      boundedConstructibleOpenImmersionLowerShriekRefinementUnitStep
      boundedConstructibleOpenImmersionLowerShriekRefinementCounitStep
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.comp_obj]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The *pushforward comparison* `i₁_! ⟶ i_! ⋙ Rh_*` on bounded constructible complexes for a
cartesian square `sq` of open immersions `i`, `i₁` and a morphism `h` as in
`isIso_boundedConstructibleOpenImmersionLowerShriekRefinement`: the unit of `Lh^* ⊣ Rh_*`
followed by the inverse of the restriction comparison,
`i₁_! ⟶ i₁_! ⋙ Lh^* ⋙ Rh_* ≅ i_! ⋙ Rh_*`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekRefinementPushforward
    (sq : IsPullback (𝟙 X) i i₁ h) :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁ ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ i ⋙ boundedConstructibleLowerStar Λ ℓ h :=
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ sq
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ h).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (inv (boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ
      sq.toCommSq.snd_comp_eq_of_fst_eq_id)) _

open scoped CategoryTheory.Obj in
open CategoryTheory.Limits in
/-- A proper refinement is an isomorphism on the open. On the complement, proper
base change sends the extension-by-zero object to zero. -/
private theorem refinementUnitIsIsoOfComplement
    (sq : IsPullback (𝟙 X) i i₁ h)
    {C P : Over (Spec (.of k))}
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    (c : C ⟶ Z₁) [IsClosedImmersion c.left] (r : P ⟶ Z) (q : P ⟶ C)
    (sqc : IsPullback r q h c)
    (hc : Set.range c.left.base = (Set.range i₁.left.base)ᶜ)
    [QuasiCompact i₁.left]
    [IsIso (boundedConstructibleBaseChange Λ ℓ sqc.toCommSq)]
    (K : Dᵇc(X.left)⟦Λ⟧) :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ h).unit.app
      ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K)) := by
  have hu₁ := sharedBoundedOpenUnitIsIso Λ ℓ i₁
  have hu := sharedBoundedOpenUnitIsIso Λ ℓ i
  have ff₁ := Adjunction.fullyFaithfulLOfIsIsoUnit
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i₁)
  have ff := Adjunction.fullyFaithfulLOfIsIsoUnit
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i)
  have := ff₁.full
  have := ff₁.faithful
  have := ff.full
  have := ff.faithful
  have hres := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ sq
  let e := asIso (boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ
    sq.toCommSq.snd_comp_eq_of_fst_eq_id)
  have : (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁ ⋙
      boundedConstructibleUpperStar Λ ℓ h).Full := Functor.Full.of_iso e
  have : (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁ ⋙
      boundedConstructibleUpperStar Λ ℓ h).Faithful := Functor.Faithful.of_iso e
  let f := (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ h).unit.app
    ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K)
  have hopen : IsIso ((boundedConstructibleUpperStar Λ ℓ i₁).map f) :=
    Adjunction.isIso_map_unit_app_obj
      (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ h)
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i₁) K
  have hdisj : Disjoint (Set.range c.left.base) (Set.range i₁.left.base) := by
    rw [hc]
    exact disjoint_compl_left
  have hdisj' : Disjoint (Set.range r.left.base) (Set.range i.left.base) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, rfl⟩ ⟨u, hu⟩
    refine Set.disjoint_left.1 hdisj ⟨q.left.base a, rfl⟩ ⟨u, ?_⟩
    have hw := congrArg Over.Hom.left sq.toCommSq.snd_comp_eq_of_fst_eq_id
    have hwc := congrArg Over.Hom.left sqc.w
    simp only [Over.comp_left] at hw hwc
    rw [← Scheme.Hom.comp_apply, ← hw, Scheme.Hom.comp_apply, hu,
      ← Scheme.Hom.comp_apply, hwc, Scheme.Hom.comp_apply]
  suffices hmap : IsIso ((boundedConstructible _).ι.map f) from
    isIso_of_reflects_iso f (boundedConstructible _).ι
  apply JointlyReflectIsomorphisms.isIso_of_pairFunctor
    (sharedDerivedModuleJointIso Λ c.left i₁.left (by rw [hc]; simp))
  · refine isIso_of_source_target_iso_zero _
      (sharedDerivedPullbackExtensionZero Λ i₁.left c.left hdisj K.obj).isoZero
      (IsZero.isoZero ?_)
    have hN₀ : IsZero ((boundedConstructibleUpperStar Λ ℓ r).obj
        ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i).obj K)) :=
      IsZero.of_full_of_faithful_of_isZero (boundedConstructible _).ι _
        (sharedDerivedPullbackExtensionZero Λ i.left r.left hdisj' K.obj)
    have hN : IsZero ((boundedConstructibleUpperStar Λ ℓ r).obj
        ((boundedConstructibleUpperStar Λ ℓ h).obj
          ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K))) :=
      hN₀.of_iso ((boundedConstructibleUpperStar Λ ℓ r).mapIso (e.app K)).symm
    have htarget : IsZero ((boundedConstructibleUpperStar Λ ℓ c).obj
        ((boundedConstructibleLowerStar Λ ℓ h).obj
          ((boundedConstructibleUpperStar Λ ℓ h).obj
            ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K)))) :=
      ((boundedConstructibleLowerStar Λ ℓ q).map_isZero hN).of_iso
        (asIso ((boundedConstructibleBaseChange Λ ℓ sqc.toCommSq).app
          ((boundedConstructibleUpperStar Λ ℓ h).obj
            ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K))))
    exact (boundedConstructible _).ι.map_isZero htarget
  · exact (NatIso.isIso_map_iff
      (boundedConstructibleUpperStarCompatibility Λ ℓ i₁) f).1 (by
        change IsIso ((boundedConstructible _).ι.map
          ((boundedConstructibleUpperStar Λ ℓ i₁).map f))
        infer_instance)

open scoped CategoryTheory.Obj in
open CategoryTheory.Limits in
private theorem refinementPushforwardIsIsoOfProperBC
    [IsProper h.left] (sq : IsPullback (𝟙 X) i i₁ h)
    (hBC : ∀ {C P : Over (Spec (.of k))}
      [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
      [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
      (c : C ⟶ Z₁) (r : P ⟶ Z) (q : P ⟶ C) (sqc : IsPullback r q h c),
      IsIso (boundedConstructibleBaseChange Λ ℓ sqc.toCommSq)) :
    IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ ℓ sq) := by
  let C : Over (Spec (.of k)) := Over.mk (i₁.left.closedComplement ≫ Z₁.hom)
  let c : C ⟶ Z₁ := Over.homMk i₁.left.closedComplement
  have : IsClosedImmersion c.left := inferInstanceAs (IsClosedImmersion i₁.left.closedComplement)
  have : LocallyOfFiniteType C.hom := by dsimp [C]; infer_instance
  have : QuasiCompact C.hom := by dsimp [C]; infer_instance
  have : IsSeparated C.hom := by dsimp [C]; infer_instance
  let P : Over (Spec (.of k)) := Over.mk (pullback.snd h.left c.left ≫ C.hom)
  let r : P ⟶ Z := Over.homMk (pullback.fst h.left c.left) (by
    change pullback.fst h.left c.left ≫ Z.hom = pullback.snd h.left c.left ≫ C.hom
    rw [← Over.w h, pullback.condition_assoc, Over.w c])
  let q : P ⟶ C := Over.homMk (pullback.snd h.left c.left)
  have : LocallyOfFiniteType P.hom := by dsimp [P]; infer_instance
  have : QuasiCompact P.hom := by dsimp [P]; infer_instance
  have : IsSeparated P.hom := by dsimp [P]; infer_instance
  have sqc : IsPullback r q h c :=
    IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext pullback.condition)
      (IsPullback.of_hasPullback h.left c.left)
  have := hBC c r q sqc
  have : QuasiCompact (i₁.left ≫ Z₁.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact i₁.left := QuasiCompact.of_comp i₁.left Z₁.hom
  have hunit (K : Dᵇc(X.left)⟦Λ⟧) :
      IsIso ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ h).unit.app
        ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K)) :=
    refinementUnitIsIsoOfComplement Λ ℓ sq c r q sqc i₁.left.range_closedComplement K
  have hres := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ sq
  have hpoint (K : Dᵇc(X.left)⟦Λ⟧) :
      IsIso ((boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ ℓ sq).app K) := by
    unfold boundedConstructibleOpenImmersionLowerShriekRefinementPushforward
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom]

/-- The isomorphism `i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rp_*` along a refinement `h : Z ⟶ Z₁` with
`h ≫ p₁ = p`, for a cartesian square `sq` as in
`isIso_boundedConstructibleOpenImmersionLowerShriekRefinement`, when the pushforward comparison
`i₁_! ⟶ i_! ⋙ Rh_*` is an isomorphism: `i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rh_* ⋙ Rp₁_* ≅ i_! ⋙ Rp_*`. For
compactifications `c` and `c₁` of `f` with `i = c.overI`, `p = c.overG`, `i₁ = c₁.overI` and
`p₁ = c₁.overG`, it is an isomorphism `Rf_!^{c₁} ≅ Rf_!^c`. -/
noncomputable def boundedConstructibleLowerShriekRefinementIso (sq : IsPullback (𝟙 X) i i₁ h)
    {p₁ : Z₁ ⟶ Y} {p : Z ⟶ Y} (wp : h ≫ p₁ = p)
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ ℓ sq)] :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁ ⋙ boundedConstructibleLowerStar Λ ℓ p₁ ≅
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ i ⋙ boundedConstructibleLowerStar Λ ℓ p :=
  Functor.isoWhiskerRight
      (asIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ ℓ sq)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarComp Λ ℓ h p₁ ≪≫ eqToIso (by rw [wp]))

end Refinement

/-! ### The `ℓ`-adic coefficient rings -/

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

section Pushforward

variable {X Z Z₁ : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom]
  {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left]
  [IsProper h.left]

/-- For bounded constructible `E`-sheaves, the pushforward comparison `i₁_! ⟶ i_! ⋙ Rh_*` of a
cartesian square `sq` with `h` proper is an isomorphism: over `X ⊆ Z₁` both sides restrict to the
identity, and over the closed complement `Z₁ ∖ X` the stalks of `Rh_*(i_! K)` are, by proper base
change, the cohomology of the fibres of `h` over `Z₁ ∖ X`, which do not meet `X ⊆ Z`, with
coefficients in `i_! K`, hence vanish. -/
theorem isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward
    (sq : IsPullback (𝟙 X) i i₁ h) :
    IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward
      (Profinite.continuousMapRingObj E) ℓ sq) := by
  apply refinementPushforwardIsIsoOfProperBC _ ℓ sq
  intro C P _ _ _ _ _ _ c r q sqc
  exact isIso_boundedConstructibleBaseChange_of_isProper ℓ E sqc

/-- For bounded constructible `ℚ̄_ℓ`-sheaves, the pushforward comparison `i₁_! ⟶ i_! ⋙ Rh_*` of a
cartesian square `sq` with `h` proper is an isomorphism. -/
theorem isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl
    (sq : IsPullback (𝟙 X) i i₁ h) :
    IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward
      (Profinite.padicAlgClRingObj ℓ) ℓ sq) := by
  apply refinementPushforwardIsIsoOfProperBC _ ℓ sq
  intro C P _ _ _ _ _ _ c r q sqc
  exact isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ sqc

end Pushforward

/-! ### Independence of the compactification -/

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y}

/-- The *independence of the lower shriek from the compactification* for bounded constructible
`E`-sheaves: for two compactifications `c₁` and `c₂` of `f`, the isomorphism
`Rf_!^{c₁} ≅ Rf_!^{c₂}` between `i₁_! ⋙ Rp₁_*` and `i₂_! ⋙ Rp₂_*` on `Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y)⟦E̲⟧`:
for a common refinement `c` of `c₁` and `c₂` (`Compactification.exists_overRefinement`), the
composite `Rf_!^{c₁} ≅ Rf_!^c ≅ Rf_!^{c₂}` of the isomorphisms
`boundedConstructibleLowerShriekRefinementIso` along the refinements. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekOfCompactificationIso
    (c₁ c₂ : Compactification f.left) :
    boundedConstructibleLowerShriekOfCompactification (Profinite.continuousMapRingObj E) ℓ c₁ ≅
      boundedConstructibleLowerShriekOfCompactification (Profinite.continuousMapRingObj E) ℓ c₂ :=
  have hc := Compactification.exists_overRefinement c₁ c₂
  let r₁ := hc.choose_spec.1.some
  let r₂ := hc.choose_spec.2.some
  have := r₁.isProper
  have := r₂.isProper
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ E r₁.isPullback
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ E r₂.isPullback
  boundedConstructibleLowerShriekRefinementIso _ ℓ r₁.isPullback r₁.hom_overG ≪≫
    (boundedConstructibleLowerShriekRefinementIso _ ℓ r₂.isPullback r₂.hom_overG).symm

/-- The *independence of the lower shriek from the compactification* for bounded constructible
`ℚ̄_ℓ`-sheaves: for two compactifications `c₁` and `c₂` of `f`, the isomorphism
`Rf_!^{c₁} ≅ Rf_!^{c₂}` on `Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧`, through a common refinement as in
`boundedConstructibleLowerShriekOfCompactificationIso`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl
    (c₁ c₂ : Compactification f.left) :
    boundedConstructibleLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) ℓ c₁ ≅
      boundedConstructibleLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) ℓ c₂ :=
  have hc := Compactification.exists_overRefinement c₁ c₂
  let r₁ := hc.choose_spec.1.some
  let r₂ := hc.choose_spec.2.some
  have := r₁.isProper
  have := r₂.isProper
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl ℓ
    r₁.isPullback
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl ℓ
    r₂.isPullback
  boundedConstructibleLowerShriekRefinementIso _ ℓ r₁.isPullback r₁.hom_overG ≪≫
    (boundedConstructibleLowerShriekRefinementIso _ ℓ r₂.isPullback r₂.hom_overG).symm

end AlgebraicGeometry.ProEtale.CondensedRing
