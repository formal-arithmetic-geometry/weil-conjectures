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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriekUnit
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange

/-!

# Independence of the lower shriek of `E`- and `ℚ̄_ℓ`-sheaves from the compactification

Let `ℓ` be a prime and `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`, with condensed ring `E̲ = C(-, E)`
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

## Main statements

- `ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekRefinement`: the
  restriction comparison is an isomorphism for a cartesian square.
- `ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward`
  and its `_padicAlgCl` version: the pushforward comparison is an isomorphism for `h` proper, by
  proper base change (`ProEtale.CondensedRing.isIso_unit_app_openImmersionLowerShriek`).

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

/-- For an open immersion `j : U ⟶ X` and a module object `M` on `X`, the counit of the
`Λ`-linear adjunction `j_! ⊣ j^*` at `M` is an isomorphism if the counit of the abelian-sheaf
adjunction `j_! ⊣ j^*` is an isomorphism at the underlying sheaf of `M`. -/
private theorem isIso_linearOpenImmersionLowerShriekAdjunction_counit_app_of_isIso
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

/-- For an open immersion `j : U ⟶ X` and a module object `M` on `X`, the counit of the
module-object adjunction `j_! ⊣ j^*` at `M` is an isomorphism if the counit of the `Λ`-linear
adjunction is: the two differ by the counit of a change of scalars along an isomorphism of
condensed rings. -/
private theorem isIso_openImmersionLowerShriekUpperStarAdjunction_counit_app_of_isIso
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

/-- For a cartesian square of schemes
```
X' --j'--> Z'
|g'        |g
v          v
X  --j---> Z
```
with `j` and `j'` open immersions, and a module object `M` on `X`, the counit of `j'_! ⊣ j'^*`
at `g^* j_! M` is an isomorphism: `g^* j_! M` is an extension by zero along `j'`. -/
private theorem isIso_counit_app_upperStar_obj_openImmersionLowerShriek
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
  exact isIso_openImmersionLowerShriekUpperStarAdjunction_counit_app_of_isIso Λ j' _
    (isIso_linearOpenImmersionLowerShriekAdjunction_counit_app_of_isIso Λ j' _ hAb)

/-- The derived version of `isIso_counit_app_upperStar_obj_openImmersionLowerShriek`: for a
cartesian square as there, the counit of the derived adjunction `j'_! ⊣ j'^*` at
`D(j_! ⋙ g^*) K` is an isomorphism. -/
private theorem isIso_derivedCounit_app_upperStar_obj_openImmersionLowerShriek
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
  have : IsIso adj.unit := inferInstance
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j').unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  have ff := (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j').fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  let α : F ⋙ (R ⋙ L) ⟶ F :=
    Functor.whiskerLeft F adj.counit ≫ (Functor.rightUnitor F).hom
  have hαapp (M) : IsIso (α.app M) := by
    have : IsIso (adj.counit.app (F.obj M)) :=
      isIso_counit_app_upperStar_obj_openImmersionLowerShriek Λ sq M
    dsimp only [α, NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let e : D(F) ⋙ (D(R) ⋙ D(L)) ≅ D(F) :=
    Functor.isoWhiskerLeft D(F) (Functor.mapDerivedCategoryCompIso R L).symm ≪≫
      (Functor.mapDerivedCategoryCompIso F (R ⋙ L)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso α)
  exact (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j').isIso_counit_app_of_iso
    (e.app K).symm

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

/-- The bounded constructible version of
`isIso_counit_app_upperStar_obj_openImmersionLowerShriek`: for a cartesian square of open
immersions `j`, `j'` and morphisms `g`, `g'` over `Spec k`, the counit of `j'_! ⊣ Lj'^*` at
`Lg^* j_! K` is an isomorphism. -/
private theorem isIso_boundedConstructibleCounit_app_upperStar_obj_openImmersionLowerShriek
    (sq : IsPullback g' j' j g)
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
  have hder := isIso_derivedCounit_app_upperStar_obj_openImmersionLowerShriek Λ sq.overLeft K.obj
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

/-- Compatibility required from `sec-proetale-coefficients` (to be proved there): blueprint
`sk-lem-nagata-density-normalization`.

The restriction comparison `i_! ⟶ i₁_! ⋙ Lh^*` is an isomorphism when the square
```
X --i--> Z
|𝟙       |h
v        v
X --i₁-> Z₁
```
is cartesian: then `Lh^* i₁_! K` is the extension by zero of `K` along `i`, so the counit of
`i_! ⊣ Li^*` is an isomorphism at it, and the unit of `i₁_! ⊣ Li₁^*` is an isomorphism since
`i₁_!` is fully faithful. -/
theorem isIso_boundedConstructibleOpenImmersionLowerShriekRefinement
    (sq : IsPullback (𝟙 X) i i₁ h) :
    IsIso (boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ
      sq.toCommSq.snd_comp_eq_of_fst_eq_id) :=
  by
  have : QuasiCompact (i.left ≫ Z.hom) := by
    rw [Over.w i]
    infer_instance
  have : QuasiCompact i.left := QuasiCompact.of_comp i.left Z.hom
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  let c := overClosedComplement i
  refine isIso_of_isIso_boundedConstructibleUpperStar_map_of_isCompl Λ ℓ c i
    (isCompl_range_overClosedComplement i) _ ?_ ?_
  · -- Over `X`, by the triangle identity of `i_! ⊣ Li^*`, whose unit is an isomorphism.
    let adj := boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i
    have hε : IsIso ((boundedConstructibleUpperStar Λ ℓ i).map (adj.counit.app
        ((boundedConstructibleUpperStar Λ ℓ h).obj
          ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K)))) := by
      have : IsIso (adj.unit.app _ ≫ (boundedConstructibleUpperStar Λ ℓ i).map (adj.counit.app
          ((boundedConstructibleUpperStar Λ ℓ h).obj
            ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K)))) := by
        rw [adj.right_triangle_components]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_left (adj.unit.app _) _
    simp only [boundedConstructibleOpenImmersionLowerShriekRefinement,
      boundedConstructibleOpenImmersionLowerShriekRefinementUnitStep,
      boundedConstructibleOpenImmersionLowerShriekRefinementCounitStep, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.leftUnitor_inv_app,
      Functor.rightUnitor_hom_app, Category.id_comp, Functor.map_comp]
    have a₁ : IsIso ((boundedConstructibleUpperStar Λ ℓ i).map
        ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i).map
          ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i₁).unit.app K))) :=
      have := NatIso.isIso_app_of_isIso
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i₁).unit K
      have := Functor.map_isIso (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i)
        ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i₁).unit.app K)
      Functor.map_isIso _ _
    have a₂ : IsIso ((boundedConstructibleUpperStar Λ ℓ i).map
        ((boundedConstructibleOpenImmersionLowerShriekRefinementTriangleStep Λ ℓ
          sq.toCommSq.snd_comp_eq_of_fst_eq_id).hom.app K)) :=
      Functor.map_isIso _ _
    exact IsIso.comp_isIso' a₁ (IsIso.comp_isIso' a₂ (by
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact hε))
  · -- Over the closed complement of `X ⊆ Z` both sides vanish, since `h⁻¹(X) = X`.
    have hS : Limits.IsZero ((boundedConstructibleUpperStar Λ ℓ c).obj
        ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i).obj K)) :=
      isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek Λ ℓ i c
        (isCompl_range_overClosedComplement i).disjoint.symm K
    have hsq : IsPullback (𝟙 X.left) i.left i₁.left h.left := by
      simpa using sq.map (Over.forget _)
    have hr : Set.range i.left.base = h.left.base ⁻¹' Set.range i₁.left.base := by
      rw [← hsq.isoPullback_hom_snd, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.2 hsq.isoPullback.hom.surjective, Set.image_univ]
      exact Scheme.Pullback.range_snd i₁.left h.left
    have hdisj : Disjoint (Set.range i₁.left.base) (Set.range (c ≫ h).left.base) := by
      rw [Set.disjoint_right]
      rintro _ ⟨z, rfl⟩ hz
      have hz' : c.left.base z ∈ Set.range i.left.base := by
        rw [hr]
        exact hz
      exact Set.disjoint_left.1 (isCompl_range_overClosedComplement i).disjoint ⟨z, rfl⟩ hz'
    have hT : Limits.IsZero ((boundedConstructibleUpperStar Λ ℓ c).obj
        ((boundedConstructibleUpperStar Λ ℓ h).obj
          ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K))) :=
      (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek Λ ℓ i₁ (c ≫ h) hdisj
        K).of_iso ((boundedConstructibleUpperStarComp Λ ℓ c h).app _).symm
    exact ⟨⟨hT.to_ _, hS.eq_of_src _ _, hT.eq_of_src _ _⟩⟩

/-- The pushforward comparison `i₁_! ⟶ i_! ⋙ Rh_*` (for any right adjoint `Rh_*` of `Lh^*`) is
an isomorphism if the proper interchange `Adjunction.exchangeRight` of the cartesian square `sq`
under `L(𝟙 X)^* ⊣ R(𝟙 X)_*` and `Lh^* ⊣ Rh_*` is: its other factors are isomorphisms, so the
unit of `Lh^* ⊣ Rh_*` is an isomorphism on `i₁_! K`. -/
private theorem isIso_refinementPushforward_of_isIso_exchangeRight
    (sq : IsPullback (𝟙 X) i i₁ h)
    {Rh : Dᵇc(Z.left)⟦Λ⟧ ⥤ Dᵇc(Z₁.left)⟦Λ⟧} (adj : boundedConstructibleUpperStar Λ ℓ h ⊣ Rh)
    {Rid : Dᵇc(X.left)⟦Λ⟧ ⥤ Dᵇc(X.left)⟦Λ⟧}
    (aid : boundedConstructibleUpperStar Λ ℓ (𝟙 X) ⊣ Rid)
    (he : IsIso (Adjunction.exchangeRight aid adj
      (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso' Λ ℓ sq)))
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ
      sq.toCommSq.snd_comp_eq_of_fst_eq_id)] :
    IsIso ((Functor.rightUnitor _).inv ≫ Functor.whiskerLeft _ adj.unit ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (inv (boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ
        sq.toCommSq.snd_comp_eq_of_fst_eq_id)) Rh) := by
  let eid : Rid ≅ 𝟭 _ := conjugateIsoEquiv aid Adjunction.id
    (boundedConstructibleUpperStarId Λ ℓ X).symm
  have : IsIso aid.counit := by
    have : Rid.Full := Functor.Full.of_iso eid.symm
    have : Rid.Faithful := Functor.Faithful.of_iso eid.symm
    exact aid.counit_isIso_of_R_fully_faithful
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  have hex : IsIso ((Adjunction.exchangeRight aid adj
      (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso' Λ ℓ sq)).app K) :=
    inferInstance
  rw [Adjunction.exchangeRight_app] at hex
  have hu : IsIso (adj.unit.app
      ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj (Rid.obj K))) := by
    exact IsIso.of_isIso_comp_right _
      (Rh.map ((boundedConstructibleOpenImmersionLowerShriekBaseChangeIso' Λ ℓ sq).hom.app
            (Rid.obj K)) ≫
        Rh.map ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i).map (aid.counit.app K)))
  have hunit : IsIso (adj.unit.app ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).obj K)) :=
    (NatTrans.isIso_app_iff_of_iso _
      ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁).mapIso (eid.app K))).mp hu
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- The *pushforward comparison* `i₁_! ⟶ i_! ⋙ Rh_*` on bounded constructible complexes for a
cartesian square `sq` of open immersions `i`, `i₁` and a morphism `h` as in
`isIso_boundedConstructibleOpenImmersionLowerShriekRefinement` (`ℚ̄_ℓ`-coefficient): the unit of
`Lh^* ⊣ Rh_*` followed by the inverse of the restriction comparison,
`i₁_! ⟶ i₁_! ⋙ Lh^* ⋙ Rh_* ≅ i_! ⋙ Rh_*`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekRefinementPushforward
    (sq : IsPullback (𝟙 X) i i₁ h) :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ i₁ ⟶
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ i ⋙
        boundedConstructibleLowerStar ℓ h :=
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement
    (Profinite.padicAlgClRingObj ℓ) ℓ sq
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (boundedConstructibleUpperStarLowerStarAdjunction ℓ h).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (inv (boundedConstructibleOpenImmersionLowerShriekRefinement
      (Profinite.padicAlgClRingObj ℓ) ℓ
      sq.toCommSq.snd_comp_eq_of_fst_eq_id)) _

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom]

/-- The isomorphism `i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rp_*` along a refinement `h : Z ⟶ Z₁` with
`h ≫ p₁ = p`, for a cartesian square `sq` as in
`isIso_boundedConstructibleOpenImmersionLowerShriekRefinement`, when the pushforward comparison
`i₁_! ⟶ i_! ⋙ Rh_*` is an isomorphism (`ℚ̄_ℓ`-coefficient): `i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rh_* ⋙ Rp₁_* ≅ i_!
⋙ Rp_*`. For compactifications `c` and `c₁` of `f` with `i = c.overI`, `p = c.overG`, `i₁ =
c₁.overI` and `p₁ = c₁.overG`, it is an isomorphism `Rf_!^{c₁} ≅ Rf_!^c`. -/
noncomputable def boundedConstructibleLowerShriekRefinementIso (sq : IsPullback (𝟙 X) i i₁ h)
    {p₁ : Z₁ ⟶ Y} {p : Z ⟶ Y} (wp : h ≫ p₁ = p)
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ sq)] :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ i₁ ⋙
      boundedConstructibleLowerStar ℓ p₁ ≅
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ i ⋙
        boundedConstructibleLowerStar ℓ p :=
  Functor.isoWhiskerRight
      (asIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ sq)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarComp ℓ h p₁ ≪≫ eqToIso (by rw [wp]))

/-! #### The coefficient ring `E̲`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` -/

namespace ContinuousMapRingObj

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The *pushforward comparison* `i₁_! ⟶ i_! ⋙ Rh_*` on bounded constructible complexes for a
cartesian square `sq` of open immersions `i`, `i₁` and a morphism `h` as in
`isIso_boundedConstructibleOpenImmersionLowerShriekRefinement` (`E`-coefficient): the unit of `Lh^*
⊣ Rh_*` followed by the inverse of the restriction comparison,
`i₁_! ⟶ i₁_! ⋙ Lh^* ⋙ Rh_* ≅ i_! ⋙ Rh_*`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekRefinementPushforward
    (sq : IsPullback (𝟙 X) i i₁ h) :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ i₁ ⟶
      boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ i ⋙
        boundedConstructibleLowerStar ℓ E h :=
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement
    (Profinite.continuousMapRingObj E) ℓ sq
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (boundedConstructibleUpperStarLowerStarAdjunction ℓ E h).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (inv (boundedConstructibleOpenImmersionLowerShriekRefinement
      (Profinite.continuousMapRingObj E) ℓ
      sq.toCommSq.snd_comp_eq_of_fst_eq_id)) _

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom]

/-- The isomorphism `i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rp_*` along a refinement `h : Z ⟶ Z₁` with
`h ≫ p₁ = p`, for a cartesian square `sq` as in
`isIso_boundedConstructibleOpenImmersionLowerShriekRefinement`, when the pushforward comparison
`i₁_! ⟶ i_! ⋙ Rh_*` is an isomorphism (`E`-coefficient): `i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rh_* ⋙ Rp₁_* ≅ i_! ⋙
Rp_*`. For compactifications `c` and `c₁` of `f` with `i = c.overI`, `p = c.overG`, `i₁ = c₁.overI`
and `p₁ = c₁.overG`, it is an isomorphism `Rf_!^{c₁} ≅ Rf_!^c`. -/
noncomputable def boundedConstructibleLowerShriekRefinementIso (sq : IsPullback (𝟙 X) i i₁ h)
    {p₁ : Z₁ ⟶ Y} {p : Z ⟶ Y} (wp : h ≫ p₁ = p)
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ E sq)] :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ i₁ ⋙
      boundedConstructibleLowerStar ℓ E p₁ ≅
      boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ i ⋙
        boundedConstructibleLowerStar ℓ E p :=
  Functor.isoWhiskerRight
      (asIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ E sq)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarComp ℓ E h p₁ ≪≫ eqToIso (by rw [wp]))

end ContinuousMapRingObj

/-! #### The coefficient ring `𝒪̲_E`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` -/

namespace PadicIntegersRingObj

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- The *pushforward comparison* `i₁_! ⟶ i_! ⋙ Rh_*` on bounded constructible complexes for a
cartesian square `sq` of open immersions `i`, `i₁` and a morphism `h` as in
`isIso_boundedConstructibleOpenImmersionLowerShriekRefinement` (`𝒪_E`-coefficient): the unit of
`Lh^* ⊣ Rh_*` followed by the inverse of the restriction comparison,
`i₁_! ⟶ i₁_! ⋙ Lh^* ⋙ Rh_* ≅ i_! ⋙ Rh_*`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekRefinementPushforward
    (sq : IsPullback (𝟙 X) i i₁ h) :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ i₁ ⟶
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ i ⋙
        boundedConstructibleLowerStar ℓ E h :=
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement
    (Profinite.padicIntegersRingObj ℓ E) ℓ sq
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (boundedConstructibleUpperStarLowerStarAdjunction ℓ E h).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (inv (boundedConstructibleOpenImmersionLowerShriekRefinement
      (Profinite.padicIntegersRingObj ℓ E) ℓ
      sq.toCommSq.snd_comp_eq_of_fst_eq_id)) _

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom]

/-- The isomorphism `i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rp_*` along a refinement `h : Z ⟶ Z₁` with
`h ≫ p₁ = p`, for a cartesian square `sq` as in
`isIso_boundedConstructibleOpenImmersionLowerShriekRefinement`, when the pushforward comparison
`i₁_! ⟶ i_! ⋙ Rh_*` is an isomorphism (`𝒪_E`-coefficient): `i₁_! ⋙ Rp₁_* ≅ i_! ⋙ Rh_* ⋙ Rp₁_* ≅ i_!
⋙ Rp_*`. For compactifications `c` and `c₁` of `f` with `i = c.overI`, `p = c.overG`, `i₁ =
c₁.overI` and `p₁ = c₁.overG`, it is an isomorphism `Rf_!^{c₁} ≅ Rf_!^c`. -/
noncomputable def boundedConstructibleLowerShriekRefinementIso (sq : IsPullback (𝟙 X) i i₁ h)
    {p₁ : Z₁ ⟶ Y} {p : Z ⟶ Y} (wp : h ≫ p₁ = p)
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ E sq)] :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ i₁ ⋙
      boundedConstructibleLowerStar ℓ E p₁ ≅
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ i ⋙
        boundedConstructibleLowerStar ℓ E p :=
  Functor.isoWhiskerRight
      (asIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ E sq)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarComp ℓ E h p₁ ≪≫ eqToIso (by rw [wp]))

end PadicIntegersRingObj

end Refinement

/-! ### The `ℓ`-adic coefficient rings -/

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

section Interchange

variable {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
  [IsOpenImmersion j.left] [IsOpenImmersion i'.left] [IsProper p'.left]

omit [IsProper p'.left] in
/-- The `E`-coefficient base-change morphism is the exchange morphism
`CategoryTheory.Adjunction.exchangeRight` of the pullback comparison. -/
private lemma continuousMap_boundedConstructibleBaseChange_eq_exchangeRight
    {X Y X' Y' : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g) :
    ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E sq =
      Adjunction.exchangeRight
        (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E f)
        (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E f')
        (boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ sq) := by
  rw [ContinuousMapRingObj.boundedConstructibleBaseChange_eq_squareExchange,
    Adjunction.squareExchange_eq_unit_square_counit]
  rfl

/-- **Interchanging proper direct image and extension by zero** for bounded constructible
`E`-sheaves: the exchange morphism `Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of a cartesian square with `p'`
proper (the mate of the extension-by-zero base-change isomorphism) is an isomorphism: over the
open `X` by the mate calculus and proper base change, over its closed complement both sides
vanish. -/
private theorem isIso_continuousMap_exchangeRight_openImmersionLowerShriekBaseChangeIso'
    (sq : IsPullback p i' j p') :
    IsIso (Adjunction.exchangeRight
      (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p)
      (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p')
      (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso'
        (Profinite.continuousMapRingObj E) ℓ sq)) := by
  have h₁ := isIso_boundedConstructibleBaseChange_of_isProper ℓ E sq.flip
  have h₂ := isIso_boundedConstructibleBaseChange_of_isProper ℓ E
    (isPullback_overPullbackFst_overPullbackSnd p' (overClosedComplement j))
  have : QuasiCompact (j.left ≫ Z.hom) := by
    rw [Over.w j]
    infer_instance
  have : QuasiCompact j.left := QuasiCompact.of_comp j.left Z.hom
  have hK (K : Dᵇc(X'.left)⟦Profinite.continuousMapRingObj E⟧) :
      IsIso ((Adjunction.exchangeRight
        (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p)
        (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p')
        (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso'
          (Profinite.continuousMapRingObj E) ℓ sq)).app K) := by
    refine isIso_of_isIso_boundedConstructibleUpperStar_map_of_isCompl
      (Profinite.continuousMapRingObj E) ℓ
      (overClosedComplement j) j (isCompl_range_overClosedComplement j) _ ?_ ?_
    · -- Over the open `X`, by the mate calculus and proper base change.
      have : IsIso ((Adjunction.exchangeRight
          (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p')
          (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p)
          (boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ
              sq.toCommSq.flip)).app
            ((boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ
              i').obj K)) := by
        rw [← continuousMap_boundedConstructibleBaseChange_eq_exchangeRight]
        infer_instance
      exact Adjunction.isIso_map_exchangeRight_app
        (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p)
        (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p')
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
            (Profinite.continuousMapRingObj E) ℓ j)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
            (Profinite.continuousMapRingObj E) ℓ i') _ _
        (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso'_inv
            (Profinite.continuousMapRingObj E) ℓ sq) K
    · -- Over the closed complement both sides vanish.
      have hS : Limits.IsZero ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (overClosedComplement j)).obj
          ((boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ
            j).obj ((ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E p).obj K))) :=
        isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek
            (Profinite.continuousMapRingObj E) ℓ j
          (overClosedComplement j) (isCompl_range_overClosedComplement j).disjoint.symm _
      have hT : Limits.IsZero ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (overClosedComplement j)).obj
          ((ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E p').obj
            ((boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ
              i').obj K))) :=
        ((ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E
          (overPullbackSnd p' (overClosedComplement j))).map_isZero
          (isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek
              (Profinite.continuousMapRingObj E) ℓ i'
            (overPullbackFst p' (overClosedComplement j))
            (disjoint_range_overPullbackFst_overClosedComplement sq.toCommSq) K)).of_iso
          (asIso ((ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E
            (isPullback_overPullbackFst_overPullbackSnd p' (overClosedComplement j)).toCommSq).app
              ((boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ
                  i').obj K)))
      exact ⟨⟨hT.to_ _, hS.eq_of_src _ _, hT.eq_of_src _ _⟩⟩
  exact NatIso.isIso_of_isIso_app _

end Interchange

section Pushforward

variable {X Z Z₁ : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom]
  {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left]
  [IsProper h.left]

/-- Compatibility required from `sec-proetale-coefficients` (to be proved there): blueprint
`sk-lem-nagata-density-normalization`.

For bounded constructible `E`-sheaves, the pushforward comparison `i₁_! ⟶ i_! ⋙ Rh_*` of a
cartesian square `sq` with `h` proper is an isomorphism: over `X ⊆ Z₁` both sides
restrict to the identity, and over the closed complement `Z₁ ∖ X` the stalks of `Rh_*(i_! K)` are,
by proper base change, the cohomology of the fibres of `h` over `Z₁ ∖ X`, which do not meet `X ⊆ Z`,
with coefficients in `i_! K`, hence vanish. -/
theorem isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward
    (sq : IsPullback (𝟙 X) i i₁ h) :
    IsIso (ContinuousMapRingObj.boundedConstructibleOpenImmersionLowerShriekRefinementPushforward
      ℓ E sq) :=
  by
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement
    (Profinite.continuousMapRingObj E) ℓ sq
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  have := isIso_unit_app_openImmersionLowerShriek _ ℓ
    (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E h)
    (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E (𝟙 X))
    (ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
      (overPullbackSnd h (overClosedComplement i₁))) sq
    (by
      rw [← ContinuousMapRingObj.boundedConstructibleBaseChange_eq_exchangeRight]
      exact isIso_boundedConstructibleBaseChange_of_isProper ℓ E sq.flip)
    (by
      rw [← ContinuousMapRingObj.boundedConstructibleBaseChange_eq_exchangeRight]
      exact isIso_boundedConstructibleBaseChange_of_isProper ℓ E
        (isPullback_overPullbackFst_overPullbackSnd h (overClosedComplement i₁))) K
  simp only [ContinuousMapRingObj.boundedConstructibleOpenImmersionLowerShriekRefinementPushforward,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- Compatibility required from `sec-proetale-coefficients` (to be proved there): blueprint
`sk-lem-nagata-density-normalization`.

For bounded constructible `ℚ̄_ℓ`-sheaves, the pushforward comparison `i₁_! ⟶ i_! ⋙ Rh_*` of a
cartesian square `sq` with `h` proper is an isomorphism. -/
theorem isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl
    (sq : IsPullback (𝟙 X) i i₁ h) :
    IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ sq) :=
  by
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement
    (Profinite.padicAlgClRingObj ℓ) ℓ sq
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  have := isIso_unit_app_openImmersionLowerShriek _ ℓ
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ h)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (𝟙 X))
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ
      (overPullbackSnd h (overClosedComplement i₁))) sq
    (by
      rw [← boundedConstructibleBaseChange_eq_exchangeRight]
      exact isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ sq.flip)
    (by
      rw [← boundedConstructibleBaseChange_eq_exchangeRight]
      exact isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ
        (isPullback_overPullbackFst_overPullbackSnd h (overClosedComplement i₁))) K
  simp only [boundedConstructibleOpenImmersionLowerShriekRefinementPushforward,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

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
    ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification ℓ E c₁ ≅
      ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification ℓ E c₂ :=
  have hc := Compactification.exists_overRefinement c₁ c₂
  let r₁ := hc.choose_spec.1.some
  let r₂ := hc.choose_spec.2.some
  have := r₁.isProper
  have := r₂.isProper
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ E r₁.isPullback
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ E r₂.isPullback
  ContinuousMapRingObj.boundedConstructibleLowerShriekRefinementIso ℓ E r₁.isPullback
    r₁.hom_overG ≪≫
    (ContinuousMapRingObj.boundedConstructibleLowerShriekRefinementIso ℓ E r₂.isPullback
      r₂.hom_overG).symm

/-- The *independence of the lower shriek from the compactification* for bounded constructible
`ℚ̄_ℓ`-sheaves: for two compactifications `c₁` and `c₂` of `f`, the isomorphism
`Rf_!^{c₁} ≅ Rf_!^{c₂}` on `Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧`: for a common refinement `c` of `c₁`
and `c₂` (`Compactification.exists_overRefinement`), the composite
`Rf_!^{c₁} ≅ Rf_!^c ≅ Rf_!^{c₂}` of the isomorphisms `boundedConstructibleLowerShriekRefinementIso`
along the refinements. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl
    (c₁ c₂ : Compactification f.left) :
    boundedConstructibleLowerShriekOfCompactification ℓ c₁ ≅
      boundedConstructibleLowerShriekOfCompactification ℓ c₂ :=
  have hc := Compactification.exists_overRefinement c₁ c₂
  let r₁ := hc.choose_spec.1.some
  let r₂ := hc.choose_spec.2.some
  have := r₁.isProper
  have := r₂.isProper
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl ℓ
    r₁.isPullback
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl ℓ
    r₂.isPullback
  boundedConstructibleLowerShriekRefinementIso ℓ r₁.isPullback r₁.hom_overG ≪≫
    (boundedConstructibleLowerShriekRefinementIso ℓ r₂.isPullback r₂.hom_overG).symm

/-- Unfolding `boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl`: the comparison
through the chosen common refinement. -/
lemma boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_eq_refinementIso
    (c₁ c₂ : Compactification f.left) :
    haveI := (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some.isProper
    haveI := (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some.isProper
    haveI := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl ℓ
      (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some.isPullback
    haveI := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl ℓ
      (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some.isPullback
    boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ c₁ c₂ =
      boundedConstructibleLowerShriekRefinementIso ℓ
          (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some.isPullback
          (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some.hom_overG ≪≫
        (boundedConstructibleLowerShriekRefinementIso ℓ
          (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some.isPullback
          (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some.hom_overG).symm := by
  unfold boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
