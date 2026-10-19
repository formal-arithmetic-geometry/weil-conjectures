/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S8
-/
module

public import Sheaf.Paper.FiniteProjectiveTensorProducts
public import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Paper.CompletedReductionOrdinaryTensorComparison
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal

/-! # Tensor comparison for a specified perfect quotient model

Source: proper base change, finite-reduction-reconstruction, order 1249, step 1;
completed-constant-sheaf-reduction; Stacks Tags 06YU, 093M and 099M.
(blueprint: lem-weil-pbc-completed-reduction-tensor-model-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
variable (d : ProEtaleAdicCoefficientDatum A)

private theorem specialize_tensor_naturality
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (H : C ⥤ C ⥤ D) (Q : C ⥤ E) (L : D ⥤ E) (S : E × E ⥤ E)
    {X Y Z : C} (u : X ⟶ Y)
    (a : L.obj ((H.obj X).obj Z) ⟶ S.obj (Q.obj X, Q.obj Z))
    (b : L.obj ((H.obj Y).obj Z) ⟶ S.obj (Q.obj Y, Q.obj Z))
    (h : L.map ((Functor.uncurry.obj H).map (X := (X, Z)) (Y := (Y, Z)) (u, 𝟙 Z)) ≫ b =
      a ≫ S.map (X := (Q.obj X, Q.obj Z))
        (Y := (Q.obj Y, Q.obj Z)) (Q.map u, Q.map (𝟙 Z))) :
    L.map ((H.flip.obj Z).map u) ≫ b = a ≫ S.map (X := (Q.obj X, Q.obj Z))
      (Y := (Q.obj Y, Q.obj Z)) (Q.map u, 𝟙 (Q.obj Z)) := by
  change L.map ((H.map u).app Z ≫ (H.obj Y).map (𝟙 Z)) ≫ b = _ at h
  change L.map ((H.map u).app Z) ≫ b = _
  simpa only [(H.obj Y).map_id, Category.comp_id, Q.map_id] using h

private theorem compose_square {C : Type*} [Category* C]
    {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C}
    (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : Z₁ ⟶ Z₂)
    (a : X₁ ⟶ Y₁) (b : X₂ ⟶ Y₂) (c : Y₁ ⟶ Z₁) (d : Y₂ ⟶ Z₂)
    (ha : f ≫ b = a ≫ g) (hb : g ≫ d = c ≫ h) :
    f ≫ (b ≫ d) = (a ≫ c) ≫ h := by
  rw [← Category.assoc, ha, Category.assoc, hb, Category.assoc]

set_option maxHeartbeats 800000 in
-- Naturality combines the resolving-class localization and concrete sheaf tensors.
/-- Tensor by a specified bounded strict-perfect model of the quotient sheaf is
finite scalar extension followed by restriction. The model and its realization are
inputs; this theorem does not construct a finite-projective resolution.

Source: blueprint finite-reduction-reconstruction, order 1249, step 1;
completed-constant-sheaf-reduction, derived reduction clause; Stacks Tags 06YU and 093M.
(blueprint: lem-weil-pbc-completed-reduction-tensor-model-comparison).

Proof: a bounded complex of finite-free retracts is K-flat. On K-flat test complexes,
tensoring the given derived realization of P identifies tensor with P and tensor with
the degree-zero quotient module. Represent the realization by a roof and tensor its
two arrows; the denominator becomes a quasi-isomorphism by K-flatness of the test
complex. Common refinements show that the localized comparison is independent of
the roof, and commute with every map between K-flat test complexes. Apply
completedReductionOrdinaryTensorComparison to identify tensor with the
degree-zero quotient with termwise scalar extension followed by restriction. Its
ordinary scalar cancellation and signed totalization have been proved in Lean.
The normalized universal derived counit of extension is invertible on every K-flat
test complex, and restriction is exact, so these are comparisons with the specified
adicDatumReductionUnderlying functor. Localizing the category of K-flat test
complexes extends this natural isomorphism to the entire derived category. The
factorization comparison for finiteProjectiveTensorRight identifies its restriction
with the tensor functor just computed. Thus the resulting isomorphism has exactly
the two stated functors as endpoints. This uses no completeness of a test object,
nonzero quotient, nonempty site or positive rank in any degree. -/
theorem completedReductionTensorModelComparison (n : ℕ)
    (P : CochainComplex (adicDatumModules T d) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P.X j))
    (p : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget T).obj (adicDatumRing T d)) P)
    (e : (completedConstantQ _).obj P ≅
      (DerivedCategory.singleFunctor (adicDatumModules T d) 0).obj
        (CompletedConstantReduction.residue T d.ideal n)) :
    Nonempty (finiteProjectiveTensorRight T d P hb p ≅
      adicDatumReductionUnderlying T d n) := by
  classical
  let := HasDerivedCategory.standard (adicDatumModules T d)
  let R := adicDatumRing T d
  let := SheafOfModules.monoidalCategory R
  let φ := adicDatumProjection T d n
  let B := (adicLisseRingSystem T d.ideal).obj (Opposite.op n)
  let := HasDerivedCategory.standard (completedConstantModules T B)
  let E := completedConstantExtension T φ
  let U := SheafOfModules.restrictScalars ((adicLisseForget T).map φ)
  let := (adicDatumRestriction_exact T φ).1
  let := (adicDatumRestriction_exact T φ).2
  let Q := completedConstantQ (adicDatumModules T d)
  let Qh := adicDatumQh T R
  let F := finiteProjectiveTensorRight T d P hb p
  let G := adicDatumReductionUnderlying T d n
  obtain ⟨S, TM, β, ⟨coh⟩⟩ :=
    CategoryTheory.ringedDerived_closed_symmetric_monoidal.{t + 1, t, t + 1, t + 2}
      (ProEt.topology T) R
  obtain ⟨V, hV, ⟨L, hL, ⟨fac⟩⟩, _⟩ :=
    SheafOfModules.site_derived_tensor_descent_independentCoefficients.{t + 1, t, t + 1,
        t + 2, 0, 0}
      (ProEt.topology T) R
  let W := (HomotopyCategory.quasiIso (adicDatumModules T d) (.up ℤ)).inverseImage V.ι
  have : L.IsEquivalence := hL
  have : (V.ι ⋙ Qh).IsLocalization W := Functor.IsLocalization.of_iso W fac
  obtain ⟨hord, ⟨ord⟩⟩ := completedReductionOrdinaryTensorComparison T d n
  let := hord
  let O := (adicDatumOrdinaryReduction T d n).mapHomotopyCategory (.up ℤ) ⋙ Qh
  let γ : Qh ⋙ G ⟶ O :=
    Functor.whiskerRight (adicDatumExtensionCounit T φ) (adicDatumRestriction T φ) ≫
      Functor.whiskerLeft (E.mapHomotopyCategory (.up ℤ))
        (adicDatumRestrictionComparison T φ).hom ≫
      (Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (E ⋙ U)) (.up ℤ)) Qh).hom
  have hγ (X : V.FullSubcategory) : IsIso (γ.app X.obj) := by
    have hx := (hV X.obj).1 X.property
    have hc := adicDatumComplexCounit_isIso T φ X.obj.as
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 hx.1)
    have he : IsIso ((adicDatumExtensionCounit T φ).app X.obj) := by
      let a := (adicDatumExtension T φ).map
        ((DerivedCategory.quotientCompQhIso _).inv.app X.obj.as)
      let b := (adicDatumQh T B).map
        ((E.mapHomotopyCategoryFactors (.up ℤ)).hom.app X.obj.as) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app
          ((E.mapHomologicalComplex (.up ℤ)).obj X.obj.as)
      have : IsIso (a ≫ (adicDatumExtensionCounit T φ).app X.obj ≫ b) := hc
      have : IsIso ((adicDatumExtensionCounit T φ).app X.obj ≫ b) :=
        IsIso.of_isIso_comp_left a _
      exact IsIso.of_isIso_comp_right _ b
    dsimp [γ]
    infer_instance
  let γiso : V.ι ⋙ Qh ⋙ G ≅ V.ι ⋙ O :=
    NatIso.ofComponents (fun X ↦ letI := hγ X; asIso (γ.app X.obj))
      (by intro X Y f; exact γ.naturality f.hom)
  let Z := (CochainComplex.singleFunctor (adicDatumModules T d) 0).obj
    (CompletedConstantReduction.residue T d.ideal n)
  let τ (C : CochainComplex (adicDatumModules T d) ℤ)
      (hC : CochainComplex.IsKFlatIndependentCoefficients (R := R) C)
      (D : CochainComplex (adicDatumModules T d) ℤ) := coh.tensorIso C D (Or.inl hC)
  let c (X : V.FullSubcategory) : F.obj (Qh.obj X.obj) ≅ O.obj X.obj :=
    (finiteProjectiveTensorRightComparison T d P hb p).app X.obj.as ≪≫
      τ X.obj.as ((hV X.obj).1 X.property).1 P ≪≫
      S.tensor.mapIso ((Iso.refl (Qh.obj X.obj)).prod e) ≪≫
      (τ X.obj.as ((hV X.obj).1 X.property).1 Z).symm ≪≫
      ord.app X.obj.as
  let ciso : (V.ι ⋙ Qh) ⋙ F ≅ V.ι ⋙ O := NatIso.ofComponents c (by
    intro X Y f
    let u := f.hom.out
    have hx := ((hV X.obj).1 X.property).1
    have hy := ((hV Y.obj).1 Y.property).1
    have hq : Qh.map f.hom = Q.map u := by
      rw [← HomotopyCategory.quotient_map_out f.hom]
      rfl
    have ho : O.map f.hom =
        (completedConstantMapComplex (adicDatumOrdinaryReduction T d n) hord ⋙ Q).map u := by
      rw [← HomotopyCategory.quotient_map_out f.hom]
      rfl
    have hF := (finiteProjectiveTensorRightComparison T d P hb p).hom.naturality u
    have hP := coh.tensorIso_naturality X.obj.as P Y.obj.as P
      (Or.inl hx) (Or.inl hy) u (𝟙 P)
    have hZ := coh.tensorIso_naturality X.obj.as Z Y.obj.as Z
      (Or.inl hx) (Or.inl hy) u (𝟙 Z)
    have hp : Q.map (((completedConstantTensor T R).flip.obj P).map u) ≫
        (τ Y.obj.as hy P).hom = (τ X.obj.as hx P).hom ≫
          S.tensor.map (Q.map u, 𝟙 (Q.obj P)) := by
      exact specialize_tensor_naturality (completedConstantTensor T R) Q Q S.tensor u
        _ _ hP
    have hz : Q.map (((completedConstantTensor T R).flip.obj Z).map u) ≫
        (τ Y.obj.as hy Z).hom = (τ X.obj.as hx Z).hom ≫
          S.tensor.map (Q.map u, 𝟙 (Q.obj Z)) := by
      exact specialize_tensor_naturality (completedConstantTensor T R) Q Q S.tensor u
        _ _ hZ
    have hz' : S.tensor.map (Q.map u, 𝟙 (Q.obj Z)) ≫
        (τ Y.obj.as hy Z).inv = (τ X.obj.as hx Z).inv ≫
          Q.map (((completedConstantTensor T R).flip.obj Z).map u) := by
      apply (cancel_mono (τ Y.obj.as hy Z).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [hz, Iso.inv_hom_id_assoc]
    have he : S.tensor.map (Q.map u, 𝟙 (Q.obj P)) ≫
        S.tensor.map (X := (Q.obj Y.obj.as, Q.obj P))
          (Y := (Q.obj Y.obj.as, Q.obj Z)) (𝟙 (Q.obj Y.obj.as), e.hom) =
        S.tensor.map (X := (Q.obj X.obj.as, Q.obj P))
          (Y := (Q.obj X.obj.as, Q.obj Z)) (𝟙 (Q.obj X.obj.as), e.hom) ≫
          S.tensor.map (Q.map u, 𝟙 (Q.obj Z)) := by
      rw [← S.tensor.map_comp, ← S.tensor.map_comp]
      congr 1
      ext <;> simp
    have hordnat := ord.hom.naturality u
    change Q.map (((completedConstantTensor T R).flip.obj Z).map u) ≫
        (ord.app Y.obj.as).hom = (ord.app X.obj.as).hom ≫
          (completedConstantMapComplex (adicDatumOrdinaryReduction T d n) hord ⋙ Q).map u
      at hordnat
    have h₁ := compose_square _ _ _ _ _ _ _ hF hp
    have h₂ := compose_square _ _ _ _ _ _ _ h₁ he
    have h₃ := compose_square _ _ _ _ _ _ _ h₂ hz'
    have h₄ := compose_square _ _ _ _ _ _ _ h₃ hordnat
    change F.map (Qh.map f.hom) ≫ (c Y).hom = (c X).hom ≫ O.map f.hom
    rw [hq, ho]
    change F.map (Q.map u) ≫
        (finiteProjectiveTensorRightComparison T d P hb p).hom.app Y.obj.as ≫
        (τ Y.obj.as hy P).hom ≫ S.tensor.map (𝟙 (Q.obj Y.obj.as), e.hom) ≫
        (τ Y.obj.as hy Z).inv ≫ (ord.app Y.obj.as).hom =
      ((finiteProjectiveTensorRightComparison T d P hb p).hom.app X.obj.as ≫
        (τ X.obj.as hx P).hom ≫ S.tensor.map (𝟙 (Q.obj X.obj.as), e.hom) ≫
        (τ X.obj.as hx Z).inv ≫ (ord.app X.obj.as).hom) ≫
          (completedConstantMapComplex (adicDatumOrdinaryReduction T d n) hord ⋙ Q).map u
    simpa only [Functor.comp_map, Category.assoc] using h₄)
  exact ⟨(Localization.fullyFaithfulWhiskeringLeft (V.ι ⋙ Qh) W
    (adicDatumDerived T d)).preimageIso (ciso ≪≫ γiso.symm)⟩

end AlgebraicGeometry.Scheme
