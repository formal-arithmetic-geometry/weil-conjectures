/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.Algebra.Homology.CochainTensorModelRigidity
public import Sheaf.Algebra.Homology.RingIsomorphismTensorTransport
import all Sheaf.Algebra.Homology.RingIsomorphismTensorTransport
public import Sheaf.CategoryTheory.Monoidal.PrescribedTensor

/-! # Comparing the native localization tensor with the published tensor 
(blueprint: lem-pur-u2-published-derived-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  (R : Sheaf J CommRingCat.{r}) [HasDerivedCategory.{w} (scalarModules J R)]

set_option maxHeartbeats 800000 in
-- Compare the two cached total-complex structures without unfolding their coproducts.
/-- The native tensor represents the same K-flat tensor as the published bifunctor.
Source: literature/stacks-project/sites-cohomology.tex; Tags 06YS, 06YT and 06YU; native monoidal
localization and uniqueness on flat-term K-flat representatives.
(blueprint: lem-pur-u2-published-derived-tensor). -/
theorem ringIso_native_tensor :
    ∃ m : MonoidalCategory (DerivedCategory (scalarModules J R)), letI := m
    ∃ b : SymmetricCategory (DerivedCategory (scalarModules J R)), letI := b
    ∃ q : (DerivedCategory.Q (C := scalarModules J R)).LaxBraided, letI := q
      IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Q (C := scalarModules J R))) ∧
      (∀ P Q : CochainComplex (scalarModules J R) ℤ,
        Q.IsKFlatIndependentCoefficients →
          IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q)) ∧
      Nonempty (Functor.uncurry.obj (curriedTensor (DerivedCategory (scalarModules J R))) ≅
        siteDerivedTensorIndependentCoefficients J R) := by
  let W := HomologicalComplex.quasiIso (scalarModules J R) (.up ℤ)
  let : W.localizerMorphismKFlat.IsLeftDerivabilityStructure := scalarDerivability R
  let := scalarCochainSymmetric R
  obtain ⟨m, b, q, hε, hμ⟩ := CategoryTheory.nativeTensorPackage
    (DerivedCategory.Q (C := scalarModules J R)) W
  let := m
  let := b
  let := q
  have hμ' (P Q : CochainComplex (scalarModules J R) ℤ)
      (hQ : Q.IsKFlatIndependentCoefficients) :
      IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) :=
    hμ P Q ((scalar_kflat_test R Q).1 hQ)
  refine ⟨m, b, q, hε, hμ', ?_⟩
  obtain ⟨s, _, hs, _⟩ := cochain_tensor_model_rigidity.{u, v, r, w, 0, 0} J R
  let L := cochainTensorRepresentativeLocalization J R
  let T := Functor.uncurry.obj (curriedTensor (DerivedCategory (scalarModules J R)))
  let t : ((cochainTensorFlatRepresentatives J R).ι.prod
      (cochainTensorFlatRepresentatives J R).ι) ⋙ cochainTensorTotal J R ⋙
      DerivedCategory.Q ≅ L.prod L ⋙ T :=
    NatIso.ofComponents (fun X ↦ by
      have := hμ' X.1.obj X.2.obj X.2.property.1
      exact (asIso (Functor.LaxMonoidal.μ DerivedCategory.Q X.1.obj X.2.obj)).symm)
      (by
        intro X Y f
        have := hμ' X.1.obj X.2.obj X.2.property.1
        have := hμ' Y.1.obj Y.2.obj Y.2.property.1
        dsimp only [Functor.comp_map, Functor.prod_map, ObjectProperty.ι_map,
          cochainTensorRepresentativeLocalization, L, T, cochainTensorTotal,
          Functor.uncurry_obj_map, Functor.map₂HomologicalComplex,
          curriedTensor_obj_map, curriedTensor_map_app, Iso.symm_hom, asIso_inv]
        dsimp only [Functor.prod_obj, ObjectProperty.ι_obj]
        change DerivedCategory.Q.map ((f.1.hom ▷ X.2.obj) ≫ (Y.1.obj ◁ f.2.hom)) ≫
          inv (Functor.LaxMonoidal.μ DerivedCategory.Q Y.1.obj Y.2.obj) = _
        rw [← tensorHom_def, ← tensorHom_def]
        exact CategoryTheory.RingedDerivedNative.inverse_naturality
          DerivedCategory.Q f.1.hom f.2.hom)
  obtain ⟨e, _, _⟩ := hs T t
  exact ⟨e.symm⟩
/-- The published K-flat tensor admits a symmetric monoidal localization structure.
Source: literature/stacks-project/sites-cohomology.tex; Tags 06YS, 06YT and 06YU; native monoidal
localization and uniqueness on flat-term K-flat representatives.
(blueprint: lem-pur-u2-published-derived-tensor). -/
theorem ringIso_published_tensor :
    ∃ m : MonoidalCategory (DerivedCategory (scalarModules J R)), letI := m
    ∃ b : SymmetricCategory (DerivedCategory (scalarModules J R)), letI := b
    ∃ q : (DerivedCategory.Q (C := scalarModules J R)).LaxBraided, letI := q
      IsIso (Functor.LaxMonoidal.ε (DerivedCategory.Q (C := scalarModules J R))) ∧
      (∀ P Q : CochainComplex (scalarModules J R) ℤ,
        Q.IsKFlatIndependentCoefficients →
          IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q)) ∧
      Functor.uncurry.obj (curriedTensor (DerivedCategory (scalarModules J R))) =
        siteDerivedTensorIndependentCoefficients J R := by
  obtain ⟨m, b, q, hε, hμ, ⟨e⟩⟩ := ringIso_native_tensor J R
  let := m
  let := b
  let := q
  let T := siteDerivedTensorIndependentCoefficients J R
  let m' := @Monoidal.prescribedTensor _ _ m T e
  let b' := @Monoidal.prescribedTensorSymmetric _ _ m T e b
  let i := @Monoidal.prescribedTensorForwardBraided _ _ m T e b
  let ib := @Functor.Braided.toLaxBraided _ _ m b.toBraidedCategory
    _ _ m' b'.toBraidedCategory (𝟭 _) i
  let q' : @Functor.LaxBraided _ _ _ _ _ _ m' b'.toBraidedCategory
      (DerivedCategory.Q (C := scalarModules J R)) :=
    @Functor.LaxBraided.instComp _ _ _ _ _ _ m b.toBraidedCategory
      _ _ m' b'.toBraidedCategory DerivedCategory.Q (𝟭 _) q
      ib
  refine ⟨m', b', q', ?_, ?_, ?_⟩
  · change IsIso (i.toMonoidal.toLaxMonoidal.ε ≫ q.toLaxMonoidal.ε)
    have := hε
    have := (@Functor.Monoidal.εIso _ _ m _ _ m' (𝟭 _) i.toMonoidal).isIso_hom
    infer_instance
  · intro P Q hQ
    change IsIso (i.toMonoidal.toLaxMonoidal.μ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
      q.toLaxMonoidal.μ P Q)
    have := hμ P Q hQ
    have := (@Functor.Monoidal.μIso _ _ m _ _ m' (𝟭 _) i.toMonoidal
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).isIso_hom
    infer_instance
  · exact @Monoidal.prescribedTensor_eq _ _ m T e
end SheafOfModules

