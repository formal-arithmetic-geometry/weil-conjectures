/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange

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

## Proof inputs

The restriction comparison follows from cartesian extension by zero, first for abelian sheaves,
then module objects, derived categories and bounded constructible categories. The pushforward
comparisons follow from proper interchange: its factors other than the adjunction unit are
isomorphisms, so that unit is an isomorphism on extension-by-zero objects.
The final comparison uses `Compactification.exists_overRefinement` for common refinements.

-/

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

open scoped CategoryTheory.Functor

/-- For a commutative square whose top morphism is an identity, the left morphism followed by the
right morphism is the bottom morphism. -/
lemma CategoryTheory.CommSq.snd_comp_eq_of_fst_eq_id {C : Type*} [Category C] {X Z Z₁ : C}
    {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁} (sq : CommSq (𝟙 X) i i₁ h) : i ≫ h = i₁ := by
  simpa using sq.w.symm

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

private theorem openUnitIsIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U V : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j] :
    IsIso (openImmersionLowerShriekUpperStarAdjunction Λ j).unit := by
  infer_instance

private theorem linearCounitOfAbelian
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : IsIso ((ProEtale.openImmersionLowerShriekUpperStarAdjunction
      Ab.{u + 1} j).counit.app M.X)) :
    IsIso ((linearOpenImmersionLowerShriekAdjunction Λ j).counit.app M) := by
  have hh : IsIso ((Mod.forget _).map
      ((linearOpenImmersionLowerShriekAdjunction Λ j).counit.app M)) := by
    change IsIso (((ProEtale.openImmersionLowerShriekUpperStarAdjunction
      Ab.{u + 1} j).homEquiv _ M.X).symm (𝟙 _))
    rw [Adjunction.homEquiv_symm_id]
    exact h
  exact isIso_of_reflects_iso _ (Mod.forget _)

private theorem moduleCounitOfLinear
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : IsIso ((linearOpenImmersionLowerShriekAdjunction Λ j).counit.app M)) :
    IsIso ((openImmersionLowerShriekUpperStarAdjunction Λ j).counit.app M) := by
  let scalar := Mod.restrictCoextendAdjunction (condensedPullbackHom Λ j)
  have ff := Functor.FullyFaithful.ofIso
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ j)).fullyFaithfulInverse
    ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ j)).symm ≪≫
      Mod.extendScalarsIsoCoextendScalars (condensedPullbackHom Λ j))
  have := ff.full
  have := ff.faithful
  have : IsIso scalar.counit := scalar.counit_isIso_of_R_fully_faithful
  dsimp only [openImmersionLowerShriekUpperStarAdjunction]
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Functor.whiskerRight_app,
    Adjunction.comp_counit_app]
  infer_instance

private theorem cartesianModuleCounit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z X' Z' : Scheme.{u}}
    {j : X ⟶ Z} {g : Z' ⟶ Z} {j' : X' ⟶ Z'} {g' : X' ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback g' j' j g)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsIso ((openImmersionLowerShriekUpperStarAdjunction Λ j').counit.app
      ((upperStar Λ g).obj ((openImmersionLowerShriek Λ j).obj M))) := by
  let e := upperStarObjXIso Λ g ((openImmersionLowerShriek Λ j).obj M) ≪≫
    ((ProEtale.openImmersionLowerShriekBaseChangeIso Ab.{u + 1} sq).app M.X).symm
  have hAb := (ProEtale.openImmersionLowerShriekUpperStarAdjunction
    Ab.{u + 1} j').isIso_counit_app_of_iso e
  exact moduleCounitOfLinear Λ j' _ (linearCounitOfAbelian Λ j' _ hAb)

private theorem cartesianDerivedCounit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z X' Z' : Scheme.{u}}
    {j : X ⟶ Z} {g : Z' ⟶ Z} {j' : X' ⟶ Z'} {g' : X' ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback g' j' j g)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    IsIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j').counit.app
      ((D(openImmersionLowerShriek Λ j ⋙ upperStar Λ g)).obj K)) := by
  let F := openImmersionLowerShriek Λ j ⋙ upperStar Λ g
  let L := openImmersionLowerShriek Λ j'
  let R := upperStar Λ j'
  let adj := openImmersionLowerShriekUpperStarAdjunction Λ j'
  have : IsIso adj.unit := openUnitIsIso Λ j'
  have ff := adj.mapDerivedCategoryAdjunction.fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  let α : F ⋙ (R ⋙ L) ⟶ F :=
    Functor.whiskerLeft F adj.counit ≫ (Functor.rightUnitor F).hom
  have hαapp (M) : IsIso (α.app M) := by
    have : IsIso (adj.counit.app (F.obj M)) := cartesianModuleCounit Λ sq M
    dsimp only [α, NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let e : D(F) ⋙ (D(R) ⋙ D(L)) ≅ D(F) :=
    Functor.isoWhiskerLeft D(F) (Functor.mapDerivedCategoryCompIso R L).symm ≪≫
      (Functor.mapDerivedCategoryCompIso F (R ⋙ L)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso α)
  exact adj.mapDerivedCategoryAdjunction.isIso_counit_app_of_iso (e.app K).symm

section
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
include ℓ k

variable {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  (j : X ⟶ Z) (g : Z' ⟶ Z) (j' : X' ⟶ Z') (g' : X' ⟶ X)
  [IsOpenImmersion j.left] [IsOpenImmersion j'.left]

variable {j g j' g'}

private theorem boundedCartesianCounit (sq : IsPullback g' j' j g)
    (K : Dᵇc(X.left)⟦Λ⟧) :
    IsIso ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j').counit.app
      ((boundedConstructibleUpperStar Λ ℓ g).obj
        ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj K))) := by
  let B := (boundedConstructibleUpperStar Λ ℓ g).obj
    ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj K)
  let e : B.obj ≅ (D(openImmersionLowerShriek Λ j.left ⋙ upperStar Λ g.left)).obj K.obj :=
    (boundedConstructibleUpperStarCompatibility Λ ℓ g).app
        ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj K) ≪≫
      (leftDerivedUpperStarIsoMapDerivedCategory Λ g.left).app _ ≪≫
      (D(upperStar Λ g.left)).mapIso
        ((boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ j).app K) ≪≫
      (Functor.mapDerivedCategoryCompIso
        (openImmersionLowerShriek Λ j.left) (upperStar Λ g.left)).symm.app K.obj
  have hder := cartesianDerivedCounit Λ sq.overLeft K.obj
  have hB : IsIso
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j'.left).counit.app B.obj) :=
    (NatTrans.isIso_app_iff_of_iso _ e).mpr hder
  let a := (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j'.left).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j'.left).symm
  have hA : IsIso (a.counit.app B.obj) := by
    dsimp only [a]
    simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Functor.whiskerRight_app]
    infer_instance
  have hm : IsIso ((boundedConstructible _).ι.map
      ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j').counit.app
        B)) := by
    change IsIso ((boundedConstructible _).ι.map
      ((a.restrictFullyFaithful (ObjectProperty.fullyFaithfulι _)
        (ObjectProperty.fullyFaithfulι _)
        (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ j').symm
        (boundedConstructibleUpperStarCompatibility Λ ℓ j').symm).counit.app B))
    rw [Adjunction.map_restrictFullyFaithful_counit_app]
    have : IsIso (a.counit.app ((boundedConstructible _).ι.obj B)) := hA
    infer_instance
  exact isIso_of_reflects_iso _ (boundedConstructible _).ι

end

/-! ### The comparisons along a refinement -/

section Refinement

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsFinitenessCoefficient ℓ Λ]
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
  have hunit : IsIso
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i₁).unit := by
    have := openUnitIsIso Λ i₁.left
    have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i₁.left).unit :=
      Adjunction.isIso_mapDerivedCategoryAdjunction_unit
        (openImmersionLowerShriekUpperStarAdjunction Λ i₁.left)
    have ff := Adjunction.fullyFaithfulLOfIsIsoUnit
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i₁.left)
    have := ff.full
    have := ff.faithful
    have : (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).Full := by
      unfold boundedConstructibleOpenImmersionLowerShriek
      infer_instance
    have : (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).Faithful := by
      unfold boundedConstructibleOpenImmersionLowerShriek
      infer_instance
    exact Adjunction.unit_isIso_of_L_fully_faithful _
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  have hc := boundedCartesianCounit Λ ℓ sq K
  have hu : IsIso ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      Λ ℓ i₁).unit.app K) := inferInstance
  let e := ((Functor.leftUnitor
      (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i)).symm.app K) ≪≫
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i).mapIso
      (asIso ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
        Λ ℓ i₁).unit.app K)) ≪≫
    (boundedConstructibleOpenImmersionLowerShriekRefinementTriangleStep Λ ℓ
      sq.toCommSq.snd_comp_eq_of_fst_eq_id).app K ≪≫
    asIso ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      Λ ℓ i).counit.app
        ((boundedConstructibleUpperStar Λ ℓ h).obj
          ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K))) ≪≫
    (Functor.rightUnitor
      (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁ ⋙
        boundedConstructibleUpperStar Λ ℓ h)).app K
  simpa only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom,
    Iso.app,
    boundedConstructibleOpenImmersionLowerShriekRefinement,
    boundedConstructibleOpenImmersionLowerShriekRefinementUnitStep,
    boundedConstructibleOpenImmersionLowerShriekRefinementCounitStep,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj, Category.assoc] using e.isIso_hom


/-- The *pushforward comparison* `i₁_! ⟶ i_! ⋙ Rh_*` on bounded constructible complexes for a
cartesian square `sq` of open immersions `i`, `i₁` and a morphism `h` as in
`isIso_boundedConstructibleOpenImmersionLowerShriekRefinement`: the unit of `Lh^* ⊣ Rh_*`
followed by the inverse of the restriction comparison,
`i₁_! ⟶ i₁_! ⋙ Lh^* ⋙ Rh_* ≅ i_! ⋙ Rh_*`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekRefinementPushforward
    [IsFinitenessCoefficient ℓ Λ] (sq : IsPullback (𝟙 X) i i₁ h) :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁ ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ i ⋙ boundedConstructibleLowerStar Λ ℓ h :=
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ sq
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ h).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (inv (boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ
      sq.toCommSq.snd_comp_eq_of_fst_eq_id)) _

private theorem refinementPushforwardIsIsoOfExchange
    (sq : IsPullback (𝟙 X) i i₁ h)
    (he : IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' Λ ℓ sq)) :
    IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ ℓ sq) := by
  let aid := boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ (𝟙 X)
  have : IsIso aid.counit := by
    have : (boundedConstructibleLowerStar Λ ℓ (𝟙 X)).Full :=
      Functor.Full.of_iso (boundedConstructibleLowerStarId Λ ℓ X).symm
    have : (boundedConstructibleLowerStar Λ ℓ (𝟙 X)).Faithful :=
      Functor.Faithful.of_iso (boundedConstructibleLowerStarId Λ ℓ X).symm
    exact aid.counit_isIso_of_R_fully_faithful
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  have hex : IsIso ((Adjunction.exchangeRight aid
      (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ h)
      (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso' Λ ℓ sq)).app K) := by
    rw [← boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_eq_exchangeRight]
    infer_instance
  rw [Adjunction.exchangeRight_app] at hex
  have hu : IsIso ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ h).unit.app
      ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj
        ((boundedConstructibleLowerStar Λ ℓ (𝟙 X)).obj K))) := by
    exact IsIso.of_isIso_comp_right _
      ((boundedConstructibleLowerStar Λ ℓ h).map
          ((boundedConstructibleOpenImmersionLowerShriekBaseChangeIso' Λ ℓ sq).hom.app
            ((boundedConstructibleLowerStar Λ ℓ (𝟙 X)).obj K)) ≫
        (boundedConstructibleLowerStar Λ ℓ h).map
          ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i).map (aid.counit.app K)))
  have hunit : IsIso ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ h).unit.app
      ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K)) :=
    (NatTrans.isIso_app_iff_of_iso _
      ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).mapIso
        ((boundedConstructibleLowerStarId Λ ℓ X).app K))).mp hu
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ sq
  dsimp only [boundedConstructibleOpenImmersionLowerShriekRefinementPushforward,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom]

/-- The isomorphism `i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rp_*` along a refinement `h : Z ⟶ Z₁` with
`h ≫ p₁ = p`, for a cartesian square `sq` as in
`isIso_boundedConstructibleOpenImmersionLowerShriekRefinement`, when the pushforward comparison
`i₁_! ⟶ i_! ⋙ Rh_*` is an isomorphism: `i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rh_* ⋙ Rp₁_* ≅ i_! ⋙ Rp_*`. For
compactifications `c` and `c₁` of `f` with `i = c.overI`, `p = c.overG`, `i₁ = c₁.overI` and
`p₁ = c₁.overG`, it is an isomorphism `Rf_!^{c₁} ≅ Rf_!^c`. -/
noncomputable def boundedConstructibleLowerShriekRefinementIso
    [IsFinitenessCoefficient ℓ Λ] (sq : IsPullback (𝟙 X) i i₁ h)
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
  exact refinementPushforwardIsIsoOfExchange _ ℓ sq
    (isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange' ℓ E sq)

/-- For bounded constructible `ℚ̄_ℓ`-sheaves, the pushforward comparison `i₁_! ⟶ i_! ⋙ Rh_*` of a
cartesian square `sq` with `h` proper is an isomorphism. -/
theorem isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl
    (sq : IsPullback (𝟙 X) i i₁ h) :
    IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward
      (Profinite.padicAlgClRingObj ℓ) ℓ sq) := by
  exact refinementPushforwardIsIsoOfExchange _ ℓ sq
    (isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ sq)

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
