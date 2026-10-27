/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Paper.AdicFiniteReductionData
public import Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules
import Sheaf.Paper.RelativeFiniteConstantSliceComparison
import Sheaf.Paper.RelativeFiniteScalarTransport
import Mathlib.RingTheory.Finiteness.Cardinality

/-! # Relative finite coefficients on the equivalent small site -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem finiteLocalModels_of_iso
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    (B : Type (u + 1)) [CommRing B]
    {F G : SheafOfModules.{u + 1} (SheafOfModules.constantCoefficientRing J B)}
    (e : F ≅ G) (h : SheafOfModules.IsLocallyConstantFiniteTypeModules J B F) :
    SheafOfModules.IsLocallyConstantFiniteTypeModules J B G := by
  intro V
  obtain ⟨S, hS, hs⟩ := h V
  refine ⟨S, hS, fun W f hf ↦ ?_⟩
  obtain ⟨M, hM, ⟨i⟩⟩ := hs W f hf
  exact ⟨M, hM, ⟨(SheafOfModules.overFunctor _ W).mapIso e.symm ≪≫ i⟩⟩

private theorem finiteLocalModels_iso_iff
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    (B : Type (u + 1)) [CommRing B]
    {F G : SheafOfModules.{u + 1} (SheafOfModules.constantCoefficientRing J B)}
    (e : F ≅ G) :
    SheafOfModules.IsLocallyConstantFiniteTypeModules J B F ↔
      SheafOfModules.IsLocallyConstantFiniteTypeModules J B G :=
  ⟨finiteLocalModels_of_iso J B e, finiteLocalModels_of_iso J B e.symm⟩

private theorem relativeFiniteLisse_iff {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] [Finite B]
    (F : pbcModules Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X B))) :
    IsRelativelyFiniteLisseModule g B F ↔
      SheafOfModules.IsLocallyConstantFiniteTypeModules (proEtaleModelTopology Y) B
        ((relativeFiniteModelModules g B).obj F) := by
  have : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).isEquivalence_inverse
  have : (AsSmall.up : Y.ProEt ⥤ proEtaleSiteModel Y).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).isEquivalence_functor
  have : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsDenseSubsite
      (proEtaleModelTopology Y) (ProEt.topology Y) := by
    change AsSmall.down.IsDenseSubsite (AsSmall.down.inducedTopology (ProEt.topology Y)) _
    infer_instance
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).inverse.IsDenseSubsite
      (proEtaleModelTopology Y) (ProEt.topology Y) :=
    inferInstanceAs (AsSmall.down.IsDenseSubsite _ _)
  have : (AsSmall.up : Y.ProEt ⥤ proEtaleSiteModel Y).IsDenseSubsite
      (ProEt.topology Y) (proEtaleModelTopology Y) :=
    inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).functor.IsDenseSubsite
      (ProEt.topology Y) (proEtaleModelTopology Y))
  constructor
  · rintro ⟨S, hS, hs⟩ V
    let S' := S.pullback (terminal.from (AsSmall.down.obj V))
    refine ⟨S'.functorPullback AsSmall.down, ?_, fun W a ha ↦ ?_⟩
    · exact AsSmall.down.cover_lift (proEtaleModelTopology Y) (ProEt.topology Y)
        ((ProEt.topology Y).pullback_stable _ hS)
    · obtain ⟨M, hM, hm⟩ := hs (AsSmall.down.obj W)
        (AsSmall.down.map a ≫ terminal.from (AsSmall.down.obj V)) ha
      have : Finite M := hM
      exact ⟨M, inferInstance, (relativeFiniteConstantSliceComparison g B F M W).mp hm⟩
  · intro hF
    obtain ⟨S, hS, hs⟩ := hF (AsSmall.up.obj (⊤_ Y.ProEt))
    refine ⟨S.functorPullback AsSmall.up, ?_, fun V a ha ↦ ?_⟩
    · exact AsSmall.up.cover_lift (ProEt.topology Y) (proEtaleModelTopology Y) hS
    · obtain ⟨M, hM, hm⟩ := hs (AsSmall.up.obj V) (AsSmall.up.map a) ha
      have : Module.Finite B M := hM
      exact ⟨M, Module.finite_of_finite B,
        (relativeFiniteConstantSliceComparison g B F M (AsSmall.up.obj V)).mpr hm⟩

attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientRingSheafify in
/-- Exact small-site models preserve relative finite lissity and coefficient extension.

Source: Stacks Project, Modules on Sites, Tags 03CY and 03A0; Cohomology on Sites,
Tags 06YY and 094I.
(blueprint: lem-weil-pbc-relative-finite-coefficient-model)

Proof: identify inverse-image constant coefficients with native constant coefficients
by the canonical constant-section isomorphism. Precompose native ring sheaves and
module sheaves with AsSmall.down. The site equivalence gives an exact equivalence of
module categories; the constant-sheaf comparison identifies the resulting coefficient
ring with the actual small-site constant commutative ring sheaf. Let L be the image
of the pulled-back complex under this exact equivalence. The homology comparison for
exact functors gives the displayed preservation of zero cohomology.

On every slice, these equivalences identify relative constant modules with constant
coefficient modules. Transport covering sieves along AsSmall.up and AsSmall.down.
A finite module is finitely generated, and over finite B a finitely generated module
has finite underlying set. This gives the first lissity equivalence, including empty
slices and the zero ring. Restriction of scalars commutes with site transport and the
canonical coefficient isomorphisms: on sections the comparison is the identity with
the scalar action identified by naturality of the constant-section map. Uniqueness
of left adjoints therefore identifies derived scalar extension with adicFiniteExtension,
including after pullback. Apply the same slice argument over R and the exact-functor
homology comparison to obtain the second equivalence. No nilpotence, surjectivity,
boundedness, normalization, tower, or stratification is used in this comparison. -/
theorem exists_relative_finite_coefficient_model {X Y : Scheme.{u}} (g : Y ⟶ X)
    {B R : Type (u + 1)} [CommRing B] [CommRing R] [Finite B] [Finite R]
    (f : B →+* R)
    (K : DerivedCategory (pbcModules X (adicLisseConstantRing X B))) :
    let J := proEtaleModelTopology Y
    ∃ L : CategoryTheory.ConstantCompletion.D
        (CategoryTheory.ConstantCompletion.constant J B),
      (∀ q : ℤ, IsZero ((DerivedCategory.homologyFunctor
          (pbcModules X (adicLisseConstantRing X B)) q).obj K) →
        IsZero ((coefficientModelCohomology _ q).obj L)) ∧
      (∀ q : ℤ, IsRelativelyFiniteLisseModule g B
          ((DerivedCategory.homologyFunctor
              (pbcModules Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X B))) q).obj
            ((adicTowerPullback g (adicLisseConstantRing X B)).obj K)) ↔
        SheafOfModules.IsLocallyConstantFiniteTypeModules J B
          ((coefficientModelCohomology _ q).obj L)) ∧
      (∀ q : ℤ, IsRelativelyFiniteLisseModule g R
          ((DerivedCategory.homologyFunctor
              (pbcModules Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X R))) q).obj
            ((adicTowerPullback g (adicLisseConstantRing X R)).obj
              ((pbcDerivedExtend ((constantSheaf (ProEt.topology X)
                CommRingCat.{u + 1}).map (CommRingCat.ofHom f))).obj K))) ↔
        SheafOfModules.IsLocallyConstantFiniteTypeModules J R
          ((coefficientModelCohomology _ q).obj
            ((adicFiniteExtension J f).obj L))) := by
  let P := (adicTowerPullback g (adicLisseConstantRing X B)).obj K
  let L := (relativeFiniteModelDerived g B).obj P
  refine ⟨L, ?_, ?_, ?_⟩
  · intro q hq
    let F := proEtaleRingModulePullback g (adicLisseConstantRing X B)
      ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)) (Iso.refl _)
    have hp : IsZero ((DerivedCategory.homologyFunctor _ q).obj P) :=
      (F.map_isZero hq).of_iso ((F.mapDerivedCategoryHomologyFunctorIso q).app K).symm
    exact ((relativeFiniteModelModules g B).map_isZero hp).of_iso
      (relativeFiniteModelHomologyIso g B P q).symm
  · intro q
    exact (relativeFiniteLisse_iff g B _).trans
      (finiteLocalModels_iso_iff (proEtaleModelTopology Y) B
        (relativeFiniteModelHomologyIso g B P q))
  · intro q
    obtain ⟨e⟩ := relativeFiniteScalarTransport g f
    let Kr := (pbcDerivedExtend ((constantSheaf (ProEt.topology X)
      CommRingCat.{u + 1}).map (CommRingCat.ofHom f))).obj K
    let Pr := (adicTowerPullback g (adicLisseConstantRing X R)).obj Kr
    let eh := relativeFiniteModelHomologyIso g R Pr q ≪≫
      (coefficientModelCohomology _ q).mapIso (e.app K)
    exact (relativeFiniteLisse_iff g R _).trans
      (finiteLocalModels_iso_iff (proEtaleModelTopology Y) R eh)

end AlgebraicGeometry.Scheme
