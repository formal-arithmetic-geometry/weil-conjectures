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
import Sheaf.SixFunctors.ProEtale.ModuleObject.OpenRefinementSupport
import Sheaf.SixFunctors.ProEtale.ModuleObject.OpenClosedConservative
import all Sheaf.Paper.CondensedOpenClosedRecollement
import Sheaf.SixFunctors.ProEtale.ModuleObject.DisjointOpenExtension
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

## Remaining input

The three comparison-isomorphism theorems in this file have complete proofs. The
pushforward comparisons use proper base change for the two coefficient rings through
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper`.
The bounded-constructible preservation properties and
`Compactification.exists_overRefinement` remain inputs from other modules.

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

open scoped CategoryTheory.Obj in
private noncomputable def fullyFaithful_boundedOpenShriek (j : X ⟶ Z)
    [IsOpenImmersion j.left] :
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).FullyFaithful := by
  have := openUnitIsIso Λ j.left
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).unit :=
    (openImmersionLowerShriekUpperStarAdjunction Λ j.left).isIso_mapDerivedCategoryAdjunction_unit
  have ff := (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).fullyFaithfulLOfIsIsoUnit
  exact ((ObjectProperty.fullyFaithfulι _).comp ff |>.ofIso
    (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ j).symm).ofCompFaithful

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

set_option backward.isDefEq.respectTransparency false in
/-- The restriction comparison `i_! ⟶ i₁_! ⋙ Lh^*` is an isomorphism when the square
```
X --i--> Z
|𝟙       |h
v        v
X --i₁-> Z₁
```
is cartesian. The unit insertion is invertible by full faithfulness of open extension.
Underived abelian open base change shows that `h^* i₁_!` is supported on `X`; forgetting
module actions and transporting along the coefficient equivalence gives the same support
for module objects. Exact derived functors preserve this support isomorphism. Thus the
`i`-counit at `Lh^* i₁_! K` is invertible, also after restricting to bounded constructible
complexes. The triangle transport is an isomorphism, so all three factors are invertible. -/
theorem isIso_boundedConstructibleOpenImmersionLowerShriekRefinement
    (sq : IsPullback (𝟙 X) i i₁ h) :
    IsIso (boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ
      sq.toCommSq.snd_comp_eq_of_fst_eq_id) := by
  obtain ⟨e⟩ := openImmersionLowerShriek_refinement_support Λ sq.overLeft
  let ed := Functor.isoWhiskerLeft (openImmersionLowerShriek Λ i₁.left).mapDerivedCategory
      (leftDerivedUpperStarIsoMapDerivedCategory Λ h.left) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso e
  have ffi := fullyFaithful_boundedOpenShriek Λ ℓ i
  have ffi₁ := fullyFaithful_boundedOpenShriek Λ ℓ i₁
  have := ffi.full
  have := ffi.faithful
  have := ffi₁.full
  have := ffi₁.faithful
  have : IsIso (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i₁).unit :=
    Adjunction.unit_isIso_of_L_fully_faithful _
  have hε (K) : IsIso
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i).counit.app
        ((boundedConstructibleUpperStar Λ ℓ h).obj
          ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K))) := by
    let eK : (boundedConstructibleUpperStar Λ ℓ h).obj
          ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K) ≅
        (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i).obj K :=
      (ObjectProperty.fullyFaithfulι _).preimageIso (ed.app K.obj)
    exact Adjunction.isIso_counit_app_of_iso _ eK
  have : IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementCounitStep Λ ℓ
      (i := i) (i₁ := i₁) (h := h)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    dsimp only [boundedConstructibleOpenImmersionLowerShriekRefinementCounitStep,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
    dsimp only [Functor.comp_obj]
    exact IsIso.comp_isIso' (hε K) (IsIso.id _)
  unfold boundedConstructibleOpenImmersionLowerShriekRefinement
    boundedConstructibleOpenImmersionLowerShriekRefinementUnitStep
  infer_instance

set_option backward.isDefEq.respectTransparency false in
-- The open test is categorical full faithfulness. On the closed complement, proper
-- base change and disjoint support make both terms zero; exact restriction detects the unit.
open scoped CategoryTheory.Obj in
private theorem isIso_unit_openExtension_of_baseChange
    {W P : Over (Spec (.of k))}
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    (a : W ⟶ Z₁) [IsClosedImmersion a.left] (b : P ⟶ Z) (q : P ⟶ W)
    (sqc : IsPullback b q h a)
    (hrange : Set.range i₁.left.base = (Set.range a.left.base)ᶜ)
    [QuasiCompact i₁.left]
    [IsIso (boundedConstructibleBaseChange Λ ℓ sqc.toCommSq)]
    (sq : IsPullback (𝟙 X) i i₁ h) (K : ProEtale.BoundedConstructible (condensedRingObj Λ X.left)) :
    IsIso ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ h).unit.app
      ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K)) := by
  have ffi := fullyFaithful_boundedOpenShriek Λ ℓ i
  have ffi₁ := fullyFaithful_boundedOpenShriek Λ ℓ i₁
  have := ffi.full
  have := ffi.faithful
  have := ffi₁.full
  have := ffi₁.faithful
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ sq
  have : (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁ ⋙
      boundedConstructibleUpperStar Λ ℓ h).Full :=
    Functor.Full.of_iso
      (asIso (boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ
        sq.toCommSq.snd_comp_eq_of_fst_eq_id))
  have : (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁ ⋙
      boundedConstructibleUpperStar Λ ℓ h).Faithful :=
    Functor.Faithful.of_iso
      (asIso (boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ
        sq.toCommSq.snd_comp_eq_of_fst_eq_id))
  have hopen := Adjunction.isIso_map_unit_app_obj
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ h)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i₁) K
  have hdisj : Disjoint (Set.range a.left.base) (Set.range i₁.left.base) := by
    rw [hrange]
    exact disjoint_compl_right
  have hsource : Limits.IsZero ((boundedConstructibleUpperStar Λ ℓ a).obj
      ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K)) := by
    apply Limits.IsZero.of_full_of_faithful_of_isZero (boundedConstructible _).ι
    exact isZero_module_derived_pullback_openExtension_of_disjoint Λ i₁.left a.left hdisj K.obj
  have hN : Limits.IsZero ((boundedConstructibleUpperStar Λ ℓ b).obj
      ((boundedConstructibleUpperStar Λ ℓ h).obj
        ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K))) := by
    apply Limits.IsZero.of_full_of_faithful_of_isZero (boundedConstructible _).ι
    refine Limits.IsZero.of_iso ?_ ((leftDerivedUpperStarComp Λ b.left h.left).app _).symm
    refine isZero_module_derived_pullback_openExtension_of_disjoint Λ i₁.left _
      (hdisj.mono_left ?_) K.obj
    rw [show b.left ≫ h.left = q.left ≫ a.left from congrArg Over.Hom.left sqc.w,
      Scheme.Hom.comp_base, TopCat.coe_comp]
    exact Set.range_comp_subset_range _ _
  have htarget : Limits.IsZero ((boundedConstructibleUpperStar Λ ℓ a).obj
      ((boundedConstructibleLowerStar Λ ℓ h).obj
        ((boundedConstructibleUpperStar Λ ℓ h).obj
          ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K)))) :=
    Limits.IsZero.of_iso ((boundedConstructibleLowerStar Λ ℓ q).map_isZero hN)
      (asIso ((boundedConstructibleBaseChange Λ ℓ sqc.toCommSq).app _))
  suffices IsIso ((boundedConstructible _).ι.map
      ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ h).unit.app
        ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K))) from
    isIso_of_fully_faithful (boundedConstructible _).ι _
  apply isIso_of_isIso_module_derived_open_closed Λ a.left i₁.left hrange
  · exact (inferInstance : IsIso ((boundedConstructible _).ι.map
      ((boundedConstructibleUpperStar Λ ℓ i₁).map
        ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ h).unit.app
          ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K)))))
  · have := hsource.isIso htarget
      ((boundedConstructibleUpperStar Λ ℓ a).map
        ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ h).unit.app
          ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K)))
    exact (inferInstance : IsIso ((boundedConstructible _).ι.map
      ((boundedConstructibleUpperStar Λ ℓ a).map
        ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ h).unit.app
          ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K)))))

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

set_option backward.isDefEq.respectTransparency false in
open scoped CategoryTheory.Obj in
private theorem isIso_refinementPushforward_of_baseChange
    (hbc : ∀ {W P : Over (Spec (.of k))}
      [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
      [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
      (a : W ⟶ Z₁) (b : P ⟶ Z) (q : P ⟶ W) (sqc : IsPullback b q h a),
      IsIso (boundedConstructibleBaseChange Λ ℓ sqc.toCommSq))
    (sq : IsPullback (𝟙 X) i i₁ h) :
    IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ ℓ sq) := by
  let W : Over (Spec (.of k)) := Over.mk (i₁.left.closedComplement ≫ Z₁.hom)
  let a : W ⟶ Z₁ := Over.homMk i₁.left.closedComplement rfl
  have : IsClosedImmersion a.left := inferInstanceAs
    (IsClosedImmersion i₁.left.closedComplement)
  have : LocallyOfFiniteType W.hom := inferInstanceAs
    (LocallyOfFiniteType (i₁.left.closedComplement ≫ Z₁.hom))
  have : QuasiCompact W.hom := inferInstanceAs
    (QuasiCompact (i₁.left.closedComplement ≫ Z₁.hom))
  have : IsSeparated W.hom := inferInstanceAs
    (IsSeparated (i₁.left.closedComplement ≫ Z₁.hom))
  let P : Over (Spec (.of k)) :=
    Over.mk (Limits.pullback.fst h.left a.left ≫ Z.hom)
  let b : P ⟶ Z := Over.homMk (Limits.pullback.fst h.left a.left) rfl
  let q : P ⟶ W := Over.homMk (Limits.pullback.snd h.left a.left) (by
    change Limits.pullback.snd h.left a.left ≫ W.hom = Limits.pullback.fst h.left a.left ≫ Z.hom
    rw [← Over.w a, ← Category.assoc, ← Limits.pullback.condition, Category.assoc, Over.w h])
  have : LocallyOfFiniteType P.hom := inferInstanceAs
    (LocallyOfFiniteType (Limits.pullback.fst h.left a.left ≫ Z.hom))
  have : QuasiCompact P.hom := inferInstanceAs
    (QuasiCompact (Limits.pullback.fst h.left a.left ≫ Z.hom))
  have : IsSeparated P.hom := inferInstanceAs
    (IsSeparated (Limits.pullback.fst h.left a.left ≫ Z.hom))
  have sqc : IsPullback b q h a :=
    IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext Limits.pullback.condition)
      (IsPullback.of_hasPullback h.left a.left)
  have := hbc a b q sqc
  have : QuasiCompact (i₁.left ≫ Z₁.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact i₁.left := QuasiCompact.of_comp i₁.left Z₁.hom
  have hrange : Set.range i₁.left.base = (Set.range a.left.base)ᶜ := by
    change Set.range i₁.left.base = (Set.range i₁.left.closedComplement.base)ᶜ
    rw [i₁.left.range_closedComplement, compl_compl]
  have hu (K) : IsIso ((Functor.whiskerLeft
      (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁)
      (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ h).unit).app K) :=
    isIso_unit_openExtension_of_baseChange Λ ℓ a b q sqc hrange sq K
  have : IsIso (Functor.whiskerLeft
      (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁)
      (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ h).unit) :=
    NatIso.isIso_of_isIso_app _
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ sq
  unfold boundedConstructibleOpenImmersionLowerShriekRefinementPushforward
  infer_instance

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
cartesian square `sq` with `h` proper is an isomorphism. The unit of `Lh^* ⊣ Rh_*` at
`i₁_! K` is invertible after open restriction by full faithfulness of `i₁_!` and
`i₁_! ⋙ Lh^*`. After restriction to the closed complement both terms are zero: the source
by disjoint support, and the target by proper base change followed by disjoint support on
the pulled-back complement. Exact open and closed inverse images jointly detect derived
isomorphisms. The remaining factors in the pushforward comparison are isomorphisms. -/
theorem isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward
    (sq : IsPullback (𝟙 X) i i₁ h) :
    IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward
      (Profinite.continuousMapRingObj E) ℓ sq) := by
  apply isIso_refinementPushforward_of_baseChange _ ℓ (sq := sq)
  intro W P _ _ _ _ _ _ a b q sqc
  exact isIso_boundedConstructibleBaseChange_of_isProper ℓ E sqc

/-- For bounded constructible `ℚ̄_ℓ`-sheaves, the pushforward comparison `i₁_! ⟶ i_! ⋙ Rh_*` of a
cartesian square `sq` with `h` proper is an isomorphism. Apply the same coefficient-independent
open–closed unit argument as for `E`, using proper base change for `ℚ̄_ℓ`. -/
theorem isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl
    (sq : IsPullback (𝟙 X) i i₁ h) :
    IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward
      (Profinite.padicAlgClRingObj ℓ) ℓ sq) := by
  apply isIso_refinementPushforward_of_baseChange _ ℓ (sq := sq)
  intro W P _ _ _ _ _ _ a b q sqc
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
