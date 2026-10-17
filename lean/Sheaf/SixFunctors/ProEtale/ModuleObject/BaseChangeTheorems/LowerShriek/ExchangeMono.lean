/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
import all Sheaf.Paper.CondensedOpenClosedRecollement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful

/-! Componentwise geometric inputs for cartesian extension by zero. -/

@[expose] public section

universe u

open scoped CategoryTheory.Obj
open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

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
  let e := (profinitePointModuleForgetPullbackIso Λ g).app
      ((openImmersionLowerShriek Λ j).obj M) ≪≫
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

/-- Source: blueprint `thm-sfb-dc-open-base-change-iso`, cartesian extension-by-zero
argument; compare `ProEtale.openImmersionLowerShriekBaseChangeIso` for abelian sheaves.

The equality parameter presents the canonical unit--square--counit composite without copying
its definition from the importing module. It is discharged there by reflexivity.

Proof: For abelian pro-etale sheaves, cartesian extension-by-zero base change identifies the
inverse image of the extension by zero with extension by zero from the pulled-back open.
The comparison is linear over the pulled-back coefficient ring: its map on the open is the
identity after the cartesian identification, and extension by zero gives the unique action
away from the open. The coefficient morphisms are isomorphisms, so scalar transport preserves
this identification. Under the canonical scalar-transport
isomorphisms, the adjunction units, counits and pullback composition comparisons on module
objects forget to these sheaf comparisons: expand the lifted adjunctions and cancel the
coefficient-isomorphism inverse pairs using their triangle identities. Their displayed mate
is therefore precisely the linear exchange map. All four functors are exact. Applying this
sheaf-level comparison and its inverse degreewise commutes with differentials and descends through
quasi-isomorphisms.
The compatibility isomorphisms defining the restricted bounded constructible functors and
adjunctions therefore identify the displayed composite on K with this derived exchange.
Thus its component is invertible, and in particular monic: if two arrows have equal
composites with it, composing with the inverse identifies the arrows. This needs no naturality
assertion for independently chosen component inverses.
(blueprint: stage3-sfb-open-base-change-component-mono) -/
theorem boundedConstructibleOpenImmersionLowerShriekBaseChange_app_mono
    (sq : IsPullback g' j' j g)
    (α : boundedConstructibleUpperStar Λ ℓ g' ⋙
        boundedConstructibleOpenImmersionLowerShriek Λ ℓ j' ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙
        boundedConstructibleUpperStar Λ ℓ g)
    (hα : α =
      ((Functor.leftUnitor _).inv ≫ Functor.whiskerRight
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).unit
        (boundedConstructibleUpperStar Λ ℓ g' ⋙
          boundedConstructibleOpenImmersionLowerShriek Λ ℓ j')) ≫
      (Functor.squareTransport (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j)
        (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j')
        (boundedConstructiblePullbackSquareComparison Λ ℓ sq.toCommSq.flip)).hom ≫
      (Functor.whiskerLeft
        (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⋙
          boundedConstructibleUpperStar Λ ℓ g)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j').counit ≫
        (Functor.rightUnitor _).hom))
    (K : Dᵇc(X.left)⟦Λ⟧) :
    Mono (α.app K) := by
  have :
      IsIso (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).unit := by
    have : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ j.left).unit :=
      openUnitIsIso Λ j.left
    have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).unit :=
      Adjunction.isIso_mapDerivedCategoryAdjunction_unit
        (openImmersionLowerShriekUpperStarAdjunction Λ j.left)
    have ff := Adjunction.fullyFaithfulLOfIsIsoUnit
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left)
    have := ff.full
    have := ff.faithful
    have : (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).Full := by
      unfold boundedConstructibleOpenImmersionLowerShriek
      infer_instance
    have : (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).Faithful := by
      unfold boundedConstructibleOpenImmersionLowerShriek
      infer_instance
    exact Adjunction.unit_isIso_of_L_fully_faithful
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j)
  -- Cartesian support makes the counit invertible on the target of the exchange.
  have := boundedCartesianCounit Λ ℓ sq K
  have : IsIso (α.app K) := by
    rw [hα]
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.comp_obj]
    infer_instance
  infer_instance

end
end AlgebraicGeometry.ProEtale.CondensedRing
