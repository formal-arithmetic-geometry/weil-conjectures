/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap

/-! # Projection formula for native module coefficient restriction

Source: Stacks 06YY; the balanced tensor projection formula on K-flat complexes.
(blueprint: lem-sf-internal-scalar-projection-formula). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe v u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
namespace CategoryTheory.Mod
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
/-- Naturality of the balanced projection in the source module.
Source: Stacks 06YY (blueprint: lem-sf-internal-scalar-projection-formula).
Proof: precompose with the balanced tensor projection. Both resulting maps are
obtained by tensoring the naturality equation of the scalar extension unit. -/
theorem projection_naturality_right (Q : Mod C S) {P P' : Mod C R}
    (g : P ⟶ P') :
    (comap φ).obj Q ◁ g ≫ (projectionIso φ Q P').hom =
      (projectionIso φ Q P).hom ≫ (comap φ).map (Q ◁ (extendScalars φ).map g) := by
  apply Mod.hom_ext
  rw [← cancel_epi (tensorObjπ ((comap φ).obj Q) P)]
  simp only [comp_hom', projectionIso_hom, tensorObjπ_whiskerLeft_assoc,
    tensorObjπ_projectionHom_hom, tensorObjπ_projectionHom_hom_assoc, comap_map_hom]
  rw [tensorObjπ_whiskerLeft]
  change Q.X ◁ g.hom ≫ Q.X ◁ extendUnitHom φ P' ≫ _ = _
  rw [← whiskerLeft_comp_assoc, ← extendUnitHom_naturality, whiskerLeft_comp_assoc]
  rfl

/-- The ordinary balanced tensor projection, natural in both module arguments.
Source: Stacks 06YY (blueprint: lem-sf-internal-scalar-projection-formula).
Proof: the component is the balanced projection isomorphism. Naturality in the
first variable follows from tensor functoriality, and in the second from the
scalar extension unit's naturality. -/
def scalarProjectionNatIso :
    comap φ ⋙ curriedTensor (Mod C R) ≅
      curriedTensor (Mod C S) ⋙
        (Functor.whiskeringLeft _ _ _).obj (extendScalars φ) ⋙
        (Functor.whiskeringRight _ _ _).obj (comap φ) :=
  NatIso.ofComponents
    (fun Q ↦ NatIso.ofComponents (fun P ↦ projectionIso φ Q P)
      (fun g ↦ projection_naturality_right φ Q g))
    (fun f ↦ by ext P : 2; exact projectionHom_naturality φ f P)

/-- The balanced projection isomorphism for total tensor complexes.
Source: Stacks 06YY (blueprint: lem-sf-internal-scalar-projection-formula).
Proof: totalize the ordinary projection isomorphism term by term. Exact scalar
restriction preserves the coproducts defining total complexes. -/
def scalarProjectionComplexIso
    (Q : CochainComplex (Mod C S) ℤ) (P : CochainComplex (Mod C R) ℤ) :
    ((comap φ).mapHomologicalComplex (.up ℤ)).obj Q ⊗ P ≅
      ((comap φ).mapHomologicalComplex (.up ℤ)).obj
        (Q ⊗ ((extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P) := by
  letI (Q : Mod C S) :
      ((comap φ ⋙ curriedTensor (Mod C R)).obj Q).PreservesZeroMorphisms :=
    inferInstanceAs ((tensorLeft ((comap φ).obj Q)).PreservesZeroMorphisms)
  letI (Q : Mod C S) :
      ((curriedTensor (Mod C S) ⋙
        (Functor.whiskeringLeft _ _ _).obj (extendScalars φ) ⋙
        (Functor.whiskeringRight _ _ _).obj (comap φ)).obj Q).PreservesZeroMorphisms :=
    inferInstanceAs ((extendScalars φ ⋙ tensorLeft Q ⋙ comap φ).PreservesZeroMorphisms)
  letI : (comap φ ⋙ curriedTensor (Mod C R)).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ by ext; simp⟩
  letI : (curriedTensor (Mod C S) ⋙
      (Functor.whiskeringLeft _ _ _).obj (extendScalars φ) ⋙
      (Functor.whiskeringRight _ _ _).obj (comap φ)).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ by ext; simp⟩
  exact HomologicalComplex₂.total.mapIso
      (HomologicalComplex.mapBifunctorHomologicalComplexObjObjIso
        (scalarProjectionNatIso φ) Q P) (.up ℤ) ≪≫
    HomologicalComplex₂.mapTotalIso (comap φ)
      ((((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj Q).obj
        (((extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P)) (.up ℤ)

/-- Restriction of the derived tensor with scalar extension is the derived tensor
with the restricted object, for arbitrary unbounded complexes.
Source: Stacks 06YY (blueprint: lem-sf-internal-scalar-projection-formula).
Proof: choose K-flat representatives P of L and M of N. Ordinary extension of P
computes derived extension. On the source use the K-flatness of M to compute the
tensor, and on the target use that of P; no K-flatness of Res M is required.
Exact restriction commutes with localization. The projection isomorphism of
complexes then identifies the two computations. -/
theorem derived_scalarProjection (L : DerivedCategory (Mod C R))
    (N : DerivedCategory (Mod C S)) :
    Nonempty ((comap φ).mapDerivedCategory.obj
        (N ⊗ (extendScalars φ).leftDerivedFunctor.obj L) ≅
      (comap φ).mapDerivedCategory.obj N ⊗ L) := by
  let F : Mod C R ⥤ Mod C S := extendScalars φ
  let V : Mod C S ⥤ Mod C R := comap φ
  obtain ⟨P, hP, ⟨e⟩⟩ := DerivedCategory.exists_kFlat_iso L
  obtain ⟨P', rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  have hP' := (HomotopyCategory.kFlat_quotient_obj_iff P').1 hP
  obtain ⟨Q, hQ, ⟨eN⟩⟩ := DerivedCategory.exists_kFlat_iso N
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective Q
  have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat P' hP'
  have := DerivedCategory.isIso_tensorRightCounit _ hP
  have := DerivedCategory.isIso_tensorLeftCounit _ hQ
  let qF := (HomotopyCategory.quotient _ (.up ℤ)).obj
    ((F.mapHomologicalComplex _).obj P')
  let qM := (HomotopyCategory.quotient _ (.up ℤ)).obj M
  let qVM := (HomotopyCategory.quotient _ (.up ℤ)).obj
    ((V.mapHomologicalComplex _).obj M)
  let j₁ : F.leftDerivedFunctor.obj L ≅ DerivedCategory.Qh.obj qF :=
    F.leftDerivedFunctor.mapIso e.symm ≪≫
      asIso (F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P')) ≪≫
      DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors _).app P')
  let j₂ : V.mapDerivedCategory.obj N ≅ DerivedCategory.Qh.obj qVM :=
    V.mapDerivedCategory.mapIso (eN.symm ≪≫
        (DerivedCategory.quotientCompQhIso _).app M) ≪≫
      V.mapDerivedCategoryFactors.app M ≪≫
      ((DerivedCategory.quotientCompQhIso _).app ((V.mapHomologicalComplex _).obj M)).symm
  let k₁ := V.mapDerivedCategory.mapIso (tensorIso eN.symm j₁ ≪≫
      asIso ((DerivedCategory.tensorLeftCounit qM).app qF) ≪≫
      DerivedCategory.Qh.mapIso
        (Functor.Monoidal.μIso (HomotopyCategory.quotient _ (.up ℤ)) M _) ≪≫
      (DerivedCategory.quotientCompQhIso _).app
        (M ⊗ ((F.mapHomologicalComplex _).obj P')))
  let k₂ := V.mapDerivedCategoryFactors.app
    (M ⊗ ((F.mapHomologicalComplex _).obj P'))
  let k₃ := DerivedCategory.Q.mapIso (scalarProjectionComplexIso φ M P').symm
  let k₄ := ((DerivedCategory.quotientCompQhIso _).app
      ((V.mapHomologicalComplex _).obj M ⊗ P')).symm ≪≫
    DerivedCategory.Qh.mapIso
      (Functor.Monoidal.μIso (HomotopyCategory.quotient _ (.up ℤ)) _ P').symm ≪≫
    (asIso ((DerivedCategory.tensorRightCounit
      ((HomotopyCategory.quotient _ _).obj P')).app qVM)).symm ≪≫
    tensorIso j₂.symm e
  exact ⟨k₁ ≪≫ k₂ ≪≫ k₃ ≪≫ k₄⟩

/-- A bound for the restricted coefficient unit gives the change-of-rings Tor
bound for every complex.
Source: Stacks 06YY (blueprint: lem-sf-internal-scalar-projection-formula).
Proof: for an R-module G, the projection formula and the unit identify the
restriction of S tensor_R^L G with Res(S) tensor_R^L G, which has homology in
[c,d]. Faithful exact restriction reflects that bound. Tensoring this object
with N of S-Tor amplitude [a,b] gives homology in [a+c,b+d]. Apply exact
restriction and the projection formula once more to obtain the required Tor
test for Res(N). This does not require the coefficient map to be flat. -/
theorem torAmplitudeIn_restriction_of_unit {a b c d : ℤ}
    {N : DerivedCategory (Mod C S)}
    (hN : DerivedCategory.torAmplitudeIn _ a b N)
    (hS : DerivedCategory.torAmplitudeIn _ c d
      ((comap φ).mapDerivedCategory.obj (𝟙_ (DerivedCategory (Mod C S))))) :
    DerivedCategory.torAmplitudeIn _ (a + c) (b + d)
      ((comap φ).mapDerivedCategory.obj N) := by
  intro G
  let V : Mod C S ⥤ Mod C R := comap φ
  let E := (extendScalars φ).leftDerivedFunctor.obj
    ((DerivedCategory.singleFunctor (Mod C R) 0).obj G)
  obtain ⟨e⟩ := derived_scalarProjection φ
    ((DerivedCategory.singleFunctor (Mod C R) 0).obj G)
    (𝟙_ (DerivedCategory (Mod C S)))
  let e' : V.mapDerivedCategory.obj E ≅
      V.mapDerivedCategory.obj (𝟙_ (DerivedCategory (Mod C S))) ⊗
        (DerivedCategory.singleFunctor (Mod C R) 0).obj G :=
    V.mapDerivedCategory.mapIso (λ_ E).symm ≪≫ e
  obtain ⟨hGE, hLE⟩ := hS G
  have := hGE
  have := hLE
  have hVE' : DerivedCategory.homologyConcentratedIn c d
      (V.mapDerivedCategory.obj E) :=
    ⟨DerivedCategory.TStructure.t.isGE_of_iso e'.symm c,
      DerivedCategory.TStructure.t.isLE_of_iso e'.symm d⟩
  have hE := V.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj hVE'
  have hNE := DerivedCategory.homologyConcentratedIn_tensor_of_torAmplitudeIn_left hN hE
  have hVNE := V.homologyConcentratedIn_mapDerivedCategory_obj hNE
  obtain ⟨p⟩ := derived_scalarProjection φ
    ((DerivedCategory.singleFunctor (Mod C R) 0).obj G) N
  obtain ⟨_, _⟩ := hVNE
  exact ⟨DerivedCategory.TStructure.t.isGE_of_iso p (a + c),
    DerivedCategory.TStructure.t.isLE_of_iso p (b + d)⟩

end CategoryTheory.Mod
