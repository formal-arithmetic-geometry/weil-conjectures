/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.RelativeFiniteCoefficientTransport
import Sheaf.Paper.RelativeFiniteScalarRestriction
import all Sheaf.Paper.AdicFiniteReductionData

/-! # Scalar extension commutes with explicit small-site coefficient transport -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

open CategoryTheory.ConstantCompletion

private def pullbackScalarIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    pbcDerivedExtend φ ⋙ adicTowerPullback g S ≅
      adicTowerPullback g R ⋙ pbcDerivedExtend ((adicTowerInverseImage g).map φ) := by
  let R' := (adicTowerInverseImage g).obj R
  let S' := (adicTowerInverseImage g).obj S
  let φ' := (adicTowerInverseImage g).map φ
  let adjR := (proEtaleRingDerivedOperations_adjunction g R R' (Iso.refl _)).some
  let adjS := (proEtaleRingDerivedOperations_adjunction g S S' (Iso.refl _)).some
  let δ := proEtaleRingRestrictionDerivedDirectImage g R S R' S' φ φ'
    (Iso.refl _) (Iso.refl _) ((Category.id_comp _).trans (Category.comp_id _).symm)
  exact ((pbcDerivedScalarAdjunction φ).comp adjS).leftAdjointUniq
    ((adjR.comp (pbcDerivedScalarAdjunction φ')).ofNatIsoRight δ.symm)

private def transportLeftAdjoints
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (E : A ≌ C) (F : B ≌ D) {L : A ⥤ B} {R : B ⥤ A}
    {L' : C ⥤ D} {R' : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R')
    (sq : R ⋙ E.functor ≅ F.functor ⋙ R') :
    E.functor ⋙ L' ≅ L ⋙ F.functor := by
  let r : F.inverse ⋙ R ≅ R' ⋙ E.inverse :=
    Functor.isoWhiskerLeft (F.inverse ⋙ R) E.unitIso ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft F.inverse sq) E.inverse ≪≫
      Functor.isoWhiskerRight F.counitIso (R' ⋙ E.inverse)
  exact ((E.toAdjunction.comp b).ofNatIsoRight r.symm).leftAdjointUniq
    (a.comp F.toAdjunction)

private theorem smallScalarAdjunction
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u + 1}} (f : R ⟶ S) : Nonempty (extend f ⊣ dres f) := by
  let : Abelian (Mod R) :=
    { (inferInstance : Abelian (Mod R)) with toPreadditive := inferInstance }
  let : Abelian (Mod S) :=
    { (inferInstance : Abelian (Mod S)) with toPreadditive := inferInstance }
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  let := (siteRestrictScalars_exact f).1
  let := (siteRestrictScalars_exact f).2
  have hpres {P Q : Cx R} (a : P ⟶ Q)
      (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
      (ha : QuasiIso a) :
      QuasiIso (((change f).mapHomologicalComplex (.up ℤ)).map a) :=
    change_preserves_kFlat_quasiIso J f a
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp hP)
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Q).mp hQ) ha
  obtain ⟨_, L, ε, hu, _, d, _⟩ := Adjunction.exists_leftDerived_adjunction
    (change f) (res f) (SheafOfModules.tensorAdjunction f)
    (CochainComplex.IsKFlatIndependentCoefficients (R := R))
    (fun P ↦ by
      obtain ⟨Y, s, hY, _, hs, _⟩ :=
        CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
      exact ⟨Y, s, hY, hs⟩) hpres
  have : L.IsLeftDerivedFunctor ε
      (HomologicalComplex.quasiIso (Mod R) (.up ℤ)) := hu
  have : (extend f).IsLeftDerivedFunctor (extendComparison f)
      (HomologicalComplex.quasiIso (Mod R) (.up ℤ)) := (derivedExtension f).universal
  exact ⟨d.ofNatIsoLeft (Functor.leftDerivedUnique (extend f) L ε (extendComparison f)
    (HomologicalComplex.quasiIso (Mod R) (.up ℤ)))⟩

attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientRingSheafify in
/-- Transport and inverse image commute with derived scalar extension, without any
assumption on cohomology, finite generation, or the coefficient homomorphism.

Source: Stacks Project, Cohomology on Sites, Tag 06YY; Modules on Sites, Tags 03CY and 03D1.
(blueprint: lem-weil-pbc-relative-finite-scalar-transport)

Proof: restriction of scalars and precomposition with AsSmall.down commute on
sections. Naturality of the two canonical constant-section isomorphisms identifies
the scalar actions as well, giving the commutative square of exact restriction
functors. The same holds for the restriction and inverse-image square, by the
canonical ring-sheaf change adjunction. Pass these exact functors and their
isomorphisms to the derived categories. The native scalar extension is left adjoint
to pbcDerivedRestrict and the small-site extension to ConstantCompletion.dres.
Compose the adjunctions with the inverse equivalences for relativeFiniteModelDerived
and with the inverse-image/direct-image adjunction. The two composite right adjoints
are isomorphic by the restriction squares. Uniqueness of left adjoints gives the
displayed isomorphism. On K-flat representatives it is the map identifying the same
pure tensors, so it agrees with the recorded adicFiniteExtension. No choice of a
new derived scalar extension is made. -/
theorem relativeFiniteScalarTransport {X Y : Scheme.{u}} (g : Y ⟶ X)
    {B R : Type (u + 1)} [CommRing B] [CommRing R] (f : B →+* R) :
    Nonempty ((pbcDerivedExtend ((constantSheaf (ProEt.topology X)
        CommRingCat.{u + 1}).map (CommRingCat.ofHom f)) ⋙
      adicTowerPullback g (adicLisseConstantRing X R) ⋙ relativeFiniteModelDerived g R) ≅
      (adicTowerPullback g (adicLisseConstantRing X B) ⋙
        relativeFiniteModelDerived g B ⋙
          adicFiniteExtension (proEtaleModelTopology Y) f)) := by
  let := HasDerivedCategory.standard (Mod (constant (proEtaleModelTopology Y) B))
  let := HasDerivedCategory.standard (Mod (constant (proEtaleModelTopology Y) R))
  let φ := (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom f)
  let φ' := (adicTowerInverseImage g).map φ
  let ψ := (constantSheaf (proEtaleModelTopology Y) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom f)
  obtain ⟨sq⟩ := relativeFiniteScalarRestriction g f
  let := (siteRestrictScalars_exact ψ).1
  let := (siteRestrictScalars_exact ψ).2
  let sqD := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso sq ≪≫ Functor.mapDerivedCategoryCompIso _ _
  obtain ⟨adj⟩ := smallScalarAdjunction ψ
  let E := (relativeFiniteModelModules g B).mapDerivedCategory.asEquivalence
  let F := (relativeFiniteModelModules g R).mapDerivedCategory.asEquivalence
  let e : relativeFiniteModelDerived g B ⋙
        adicFiniteExtension (proEtaleModelTopology Y) f ≅
      pbcDerivedExtend φ' ⋙ relativeFiniteModelDerived g R :=
    transportLeftAdjoints E F (pbcDerivedScalarAdjunction φ')
      adj sqD
  exact ⟨Functor.isoWhiskerRight (pullbackScalarIso g φ) _ ≪≫
    Functor.isoWhiskerLeft (adicTowerPullback g (adicLisseConstantRing X B)) e.symm⟩

end AlgebraicGeometry.Scheme
