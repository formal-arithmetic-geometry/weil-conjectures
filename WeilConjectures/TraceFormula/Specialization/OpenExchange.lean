/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeClosedImmersion
public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructibleUnitIdentity
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
public import WeilConjectures.TraceFormula.Specialization.DeformationModel

/-!

# The pullback exchange of nearby cycles along open immersions

Let `φ : M ⟶ N` be a morphism of nearby cycles models over `f : X ⟶ Y` and `f' : X' ⟶ Y'`, with
morphism `t` of total spaces and `g` of geometric generic fibres. If `t` and `g` are weakly étale
(e.g. `t` an open immersion) and the square `g ≫ j_N = j_M ≫ t` of geometric generic fibres is
cartesian, then the pullback exchange `α_f : Lf'^* Ψ_N ⟶ Ψ_M Lf^*`
(`NearbyCyclesModel.Hom.pullbackExchange`) is an isomorphism (blueprint
`det-sp-nearby-cycles-exchanges` (1), the smooth exchange for open immersions): its only
non-invertible-by-construction factor is the base change map `Lt^* Rj_{N*} ⟶ Rj_{M*} Lg^*`, which
is an isomorphism by weakly étale base change
(`ProEtale.CondensedRing.isIso_baseChangeMap_of_weaklyEtale`).

We apply this to the deformation to the normal cone: for an open immersion `f : X ⟶ Y` of
`k`-schemes and `J = f⁻¹ I`, the morphism of models `deformationModelHom f hJ k'` satisfies these
hypotheses.

## Main results

- `NearbyCyclesModel.Hom.isIso_pullbackExchange_of_weaklyEtale`,
  `NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isOpenImmersion`: the pullback exchange of a
  morphism of models whose generic square is cartesian with weakly étale (resp. open immersion)
  total map is an isomorphism.
- `NearbyCyclesModel.Hom.isIso_boundedConstructiblePullbackExchange_of_isOpenImmersion`: the same
  on bounded constructible complexes.
- `isPullback_deformationGenericMap`: the square of geometric generic fibres of
  `deformationModelHom` is always cartesian.
- `isOpenImmersion_deformationTotalMap`: for an open immersion `f` and `J = f⁻¹ I`, the morphism of
  total spaces is an open immersion.
- `isIso_deformationModelHom_pullbackExchange`: the pullback exchange of the deformation model
  along an open immersion is an isomorphism.

## Implementation notes

The cartesian-ness of the square of special fibres is not needed: the pullback comparison of a
commutative square is always invertible.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

section Abstract

/-- A transformation of the shape of the pullback exchange is invertible when its middle factor
is. -/
private lemma isIso_pullbackExchange_aux
    {DY' DX' DTN DTM DGN DGM DY DX : Type*} [Category DY'] [Category DX'] [Category DTN]
    [Category DTM] [Category DGN] [Category DGM] [Category DY] [Category DX]
    {Fp' : DY' ⥤ DX'} {IN : DTN ⥤ DY'} {IM : DTM ⥤ DX'} {T : DTN ⥤ DTM}
    {JNs : DGN ⥤ DTN} {JMs : DGM ⥤ DTM} {G : DGN ⥤ DGM} {EN : DY ⥤ DGN} {EM : DX ⥤ DGM}
    {F : DY ⥤ DX} (θi : IN ⋙ Fp' ⟶ T ⋙ IM) [IsIso θi] (β : JNs ⋙ T ⟶ G ⋙ JMs) [IsIso β]
    (θε : EN ⋙ G ⟶ F ⋙ EM) [IsIso θε]
    (α : (EN ⋙ JNs ⋙ IN) ⋙ Fp' ⟶ F ⋙ EM ⋙ JMs ⋙ IM)
    (hα : α = Functor.whiskerLeft (EN ⋙ JNs) θi ≫
      Functor.whiskerRight (Functor.whiskerLeft EN β ≫ Functor.whiskerRight θε JMs) IM) :
    IsIso α := by
  subst hα
  infer_instance

/-- A transformation `χ` between functors preserving full subcategories which is an isomorphism
restricts to an isomorphism. -/
lemma isIso_liftExchange {DY DX DY' DX' : Type*} [Category DY] [Category DX]
    [Category DY'] [Category DX'] {PY : ObjectProperty DY} {PX : ObjectProperty DX}
    {PY' : ObjectProperty DY'} {PX' : ObjectProperty DX'} {Rf : DX ⥤ DY} {Rf' : DX' ⥤ DY'}
    {ΨN : DY ⥤ DY'} {ΨM : DX ⥤ DX'} (χ : Rf ⋙ ΨN ⟶ ΨM ⋙ Rf') [IsIso χ]
    (hR : ∀ Z : PX.FullSubcategory, PY ((PX.ι ⋙ Rf).obj Z))
    (hR' : ∀ Z : PX'.FullSubcategory, PY' ((PX'.ι ⋙ Rf').obj Z))
    (hN : ∀ Z : PY.FullSubcategory, PY' ((PY.ι ⋙ ΨN).obj Z))
    (hM : ∀ Z : PX.FullSubcategory, PX' ((PX.ι ⋙ ΨM).obj Z)) :
    IsIso (liftExchange χ hR hR' hN hM) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Z
  have : IsIso (PY'.ι.map ((liftExchange χ hR hR' hN hM).app Z)) :=
    inferInstanceAs (IsIso (χ.app Z.obj))
  exact isIso_of_reflects_iso _ PY'.ι

end Abstract

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

namespace Hom

variable (φ : M.Hom N f f')

/-- **The pullback exchange along a weakly étale morphism of models** (blueprint
`det-sp-nearby-cycles-exchanges` (1)): if the morphisms `t` of total spaces and `g` of geometric
generic fibres are weakly étale and the square `g ≫ j_N = j_M ≫ t` is cartesian, the pullback
exchange `α_f : Lf'^* Ψ_N ⟶ Ψ_M Lf^*` is an isomorphism. -/
theorem isIso_pullbackExchange_of_weaklyEtale [WeaklyEtale φ.total] [WeaklyEtale φ.generic]
    (hj : IsPullback φ.generic M.j N.j φ.total) : IsIso (φ.pullbackExchange Λ) := by
  have h := isIso_baseChangeMap_of_weaklyEtale Λ hj
  rw [baseChangeMap, Adjunction.exchangeRight_eq_mateEquiv] at h
  exact isIso_pullbackExchange_aux (pullbackSquareComparison Λ φ.commSq_i).hom
    (mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j)
      (pullbackSquareComparison Λ φ.commSq_j).hom).natTrans
    (pullbackSquareComparison Λ φ.commSq_ε).hom (φ.pullbackExchange Λ) rfl

/-- **The pullback exchange along an open immersion of models**: if the morphism of total spaces
is an open immersion and the square of geometric generic fibres is cartesian, the pullback
exchange `α_f : Lf'^* Ψ_N ⟶ Ψ_M Lf^*` is an isomorphism. -/
theorem isIso_pullbackExchange_of_isOpenImmersion [IsOpenImmersion φ.total]
    (hj : IsPullback φ.generic M.j N.j φ.total) : IsIso (φ.pullbackExchange Λ) := by
  have : IsOpenImmersion φ.generic := MorphismProperty.of_isPullback hj.flip inferInstance
  exact φ.isIso_pullbackExchange_of_weaklyEtale Λ hj

end Hom

section BoundedConstructible

variable {Λ} (ℓ : ℕ) [Fact ℓ.Prime] {k k' : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

namespace Hom

variable (φ : M.Hom N f.left f'.left) (hM : M.PreservesBoundedConstructible Λ)
  (hN : N.PreservesBoundedConstructible Λ)

/-- The restricted pullback exchange is an isomorphism whenever the ambient one is. -/
lemma isIso_boundedConstructiblePullbackExchange [IsIso (φ.pullbackExchange Λ)] :
    IsIso (φ.boundedConstructiblePullbackExchange ℓ hM hN) := by
  rw [boundedConstructiblePullbackExchange_eq_liftExchange]
  exact isIso_liftExchange _ _ _ _ _

/-- **The pullback exchange along an open immersion of models, on bounded constructible
complexes**: if the morphism of total spaces is an open immersion and the square of geometric
generic fibres is cartesian, the restricted pullback exchange is an isomorphism. -/
theorem isIso_boundedConstructiblePullbackExchange_of_isOpenImmersion [IsOpenImmersion φ.total]
    (hj : IsPullback φ.generic M.j N.j φ.total) :
    IsIso (φ.boundedConstructiblePullbackExchange ℓ hM hN) := by
  have := φ.isIso_pullbackExchange_of_isOpenImmersion Λ hj
  exact φ.isIso_boundedConstructiblePullbackExchange ℓ hM hN

end Hom

end BoundedConstructible

end NearbyCyclesModel

/-! ### The deformation to the normal cone along an open immersion -/

section Deformation

variable {k : Type u} [Field k] {X Y : Over (Spec (.of k))} (f : X ⟶ Y)
  {I : Y.left.IdealSheafData} {J : X.left.IdealSheafData}
  (hJ : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ f.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (f.left.appLE U.1 U'.1 hU).hom ≤
      J.siteIdeal U')
  (k' : Type u) [Field k'] [Algebra k k']

/-- The square of total spaces over the square of deformation spaces is cartesian:
`𝒳 = D_J X ×_{D_I Y} 𝒴`. -/
lemma isPullback_deformationTotalMap :
    IsPullback (deformationTotalMap f hJ k') (deformationTotalToSpace X J k')
      (deformationTotalToSpace Y I k') (IdealSheafData.deformationSpaceMap f.left I J hJ) := by
  refine IsPullback.of_right ?_ (deformationTotalMap_toSpace f hJ k')
    (isPullback_deformationTotal Y I k').flip
  rw [deformationTotalMap_toTrait, deformationSpaceMap_deformationSpaceToAffineLine]
  exact (isPullback_deformationTotal X J k').flip

/-- The square of geometric generic fibres of `deformationModelHom` is cartesian. -/
lemma isPullback_deformationGenericMap :
    IsPullback (deformationGenericMap f hJ k') (deformationGenericToTotal X J k')
      (deformationGenericToTotal Y I k') (deformationTotalMap f hJ k') := by
  refine IsPullback.of_right (h₁₂ := pullback.snd _ _) (h₂₂ := deformationTotalToTrait Y I k') ?_
    (deformationGenericMap_toTotal f hJ k') (IsPullback.of_hasPullback _ _).flip
  have e : deformationGenericMap f hJ k' ≫ pullback.snd _ _ =
      pullback.snd (deformationTotalToTrait X J k') (traitGenericPoint k') :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  rw [e, deformationTotalMap_toTrait]
  exact (IsPullback.of_hasPullback _ _).flip

/-- For an open immersion `f` and `J = f⁻¹ I`, the morphism of deformation spaces
`D_J X ⟶ D_I Y` is an open immersion. -/
lemma isOpenImmersion_deformationSpaceMap [IsOpenImmersion f.left]
    (hJI : J = I.comap f.left) :
    IsOpenImmersion (IdealSheafData.deformationSpaceMap f.left I J hJ) :=
  MorphismProperty.of_isPullback
    (IdealSheafData.isPullback_deformationSpaceMap_of_flat f.left I J hJ hJI).flip inferInstance

/-- For an open immersion `f` and `J = f⁻¹ I`, the morphism of total spaces `𝒳 ⟶ 𝒴` is an open
immersion. -/
lemma isOpenImmersion_deformationTotalMap [IsOpenImmersion f.left]
    (hJI : J = I.comap f.left) : IsOpenImmersion (deformationTotalMap f hJ k') :=
  have := isOpenImmersion_deformationSpaceMap f hJ hJI
  MorphismProperty.of_isPullback (isPullback_deformationTotalMap f hJ k').flip inferInstance

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **The pullback exchange of the deformation to the normal cone along an open immersion**
(blueprint `det-sp-nearby-cycles-exchanges` (1)): for an open immersion `f : X ⟶ Y` and
`J = f⁻¹ I`, the pullback exchange of `deformationModelHom f hJ k'` is an isomorphism. -/
theorem isIso_deformationModelHom_pullbackExchange [IsOpenImmersion f.left]
    (hJI : J = I.comap f.left) : IsIso ((deformationModelHom f hJ k').pullbackExchange Λ) := by
  have : IsOpenImmersion (deformationModelHom f hJ k').total :=
    isOpenImmersion_deformationTotalMap f hJ k' hJI
  exact (deformationModelHom f hJ k').isIso_pullbackExchange_of_isOpenImmersion Λ
    (isPullback_deformationGenericMap f hJ k')

end Deformation

end AlgebraicGeometry.ProEtale.CondensedRing
