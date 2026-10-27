module

public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Summands of a conjugated total oplax comparison

Source: Stacks Project, Tag 012Z, `definition-associated-simple-complex` and
`remark-triple-complex`; functor-square calculation in the blueprint proof
(blueprint: lem-pd-total-oplax-conjugation-summands).

The tensor and all single-functor comparisons are the published constructions.
The square isomorphism is arbitrary; no monoidality condition on it is imposed.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CategoryTheory.Functor
section
universe uA₀ vA₀ uA₁ vA₁ uB₀ vB₀ uB₁ vB₁

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex


private theorem tensor_injection_map {C : Type uA₀}
    [Category.{vA₀} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
    [HasColimitsOfSize.{0, 0} C]
    {P Q P' Q' : CochainComplex C ℤ} (f : P ⟶ P') (g : Q ⟶ Q')
    (p q n : ℤ) (h : p + q = n) :
    ιTensorObj P Q p q n h ≫ (HomologicalComplex.tensorHom f g).f n =
      (f.f p ⊗ₘ g.f q) ≫ ιTensorObj P' Q' p q n h := by
  exact GradedObject.Monoidal.ι_tensorHom _ _ p q n h

@[reassoc]
private theorem total_inv_component {C : Type uA₀} {D : Type uB₀}
    [Category.{vA₀} C] [Category.{vB₀} D] [Abelian C] [Abelian D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
    (G : C ⥤ D) [G.Additive] [G.Monoidal]
    [∀ (J : Type) [Countable J], PreservesColimitsOfShape (Discrete J) G]
    (P Q : CochainComplex C ℤ) (p q n : ℤ) (h : p + q = n) :
    G.map (ιTensorObj P Q p q n h) ≫ (G.mapCochainComplexμIso P Q).inv.f n =
      OplaxMonoidal.δ G (P.X p) (Q.X q) ≫
        ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj P)
          ((G.mapHomologicalComplex (.up ℤ)).obj Q) p q n h := by
  rw [mapCochainComplexμIso_inv]
  exact map_ιMapBifunctor_mapBifunctorComparisonX
    (OplaxMonoidal.δNatTrans G) (.up ℤ) P Q p q n h

variable {A₀ : Type uA₀} {A₁ : Type uA₁} {B₀ : Type uB₀} {B₁ : Type uB₁}
  [Category.{vA₀} A₀] [Category.{vA₁} A₁] [Category.{vB₀} B₀] [Category.{vB₁} B₁]
  [Abelian A₀] [Abelian A₁] [Abelian B₀] [Abelian B₁]
  [MonoidalCategory A₀] [MonoidalCategory A₁] [MonoidalCategory B₀] [MonoidalCategory B₁]
  [MonoidalPreadditive A₀] [MonoidalPreadditive A₁]
  [MonoidalPreadditive B₀] [MonoidalPreadditive B₁]
  [HasColimitsOfSize.{0, 0} A₀] [HasColimitsOfSize.{0, 0} A₁]
  [HasColimitsOfSize.{0, 0} B₀] [HasColimitsOfSize.{0, 0} B₁]
  [∀ X : A₀, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : A₀, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [∀ X : A₁, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : A₁, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [∀ X : B₀, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : B₀, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [∀ X : B₁, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : B₁, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (E₀ : A₀ ⥤ B₀) (E₁ : A₁ ⥤ B₁) (Fi : A₀ ⥤ A₁) (Fs : B₀ ⥤ B₁)
  [E₀.Additive] [E₁.Additive] [Fi.Additive] [Fs.Additive]
  [E₀.Monoidal] [E₁.Monoidal] [Fi.Monoidal] [hFsMonoidal : Fs.Monoidal]
  [E₀.IsEquivalence] [E₁.IsEquivalence]
  [hFi : ∀ (J : Type) [Countable J], PreservesColimitsOfShape (Discrete J) Fi]
  [hFs : ∀ (J : Type) [Countable J], PreservesColimitsOfShape (Discrete J) Fs]
  (a : Fi ⋙ E₁ ≅ E₀ ⋙ Fs)

/-- The ordinary five-factor conjugation, in order of application.
Source: Stacks Tag 012Z, functor-square calculation, Step 3
(blueprint: lem-pd-total-oplax-conjugation-summands). -/
private noncomputable def conjugatedOplaxTensorIso (M N : A₀) :
    Fs.obj (E₀.obj M ⊗ E₀.obj N) ≅ Fs.obj (E₀.obj M) ⊗ Fs.obj (E₀.obj N) :=
  Fs.mapIso (Monoidal.μIso E₀ M N) ≪≫ (a.app (M ⊗ N)).symm ≪≫
    E₁.mapIso (Monoidal.μIso Fi M N).symm ≪≫
    (Monoidal.μIso E₁ (Fi.obj M) (Fi.obj N)).symm ≪≫
    tensorIso (a.app M) (a.app N)

/-- The full conjugation of the canonical total comparisons as a chain isomorphism.
Here `mapCochainComplexμIso.symm` is `T`, and `NatIso.mapHomologicalComplex`
extends the arbitrary comparison termwise.
Source: Stacks Tag 012Z, functor-square calculation, Steps 2–4
(blueprint: lem-pd-total-oplax-conjugation-summands). -/
private noncomputable def conjugatedTotalOplaxIso (P Q : CochainComplex A₀ ℤ) :
    (Fs.mapHomologicalComplex (.up ℤ)).obj
        ((E₀.mapHomologicalComplex (.up ℤ)).obj P ⊗
          (E₀.mapHomologicalComplex (.up ℤ)).obj Q) ≅
      (Fs.mapHomologicalComplex (.up ℤ)).obj
          ((E₀.mapHomologicalComplex (.up ℤ)).obj P) ⊗
        (Fs.mapHomologicalComplex (.up ℤ)).obj
          ((E₀.mapHomologicalComplex (.up ℤ)).obj Q) :=
  (Fs.mapHomologicalComplex (.up ℤ)).mapIso (E₀.mapCochainComplexμIso P Q) ≪≫
    ((NatIso.mapHomologicalComplex a (.up ℤ)).app (P ⊗ Q)).symm ≪≫
    (E₁.mapHomologicalComplex (.up ℤ)).mapIso (Fi.mapCochainComplexμIso P Q).symm ≪≫
    (E₁.mapCochainComplexμIso ((Fi.mapHomologicalComplex (.up ℤ)).obj P)
      ((Fi.mapHomologicalComplex (.up ℤ)).obj Q)).symm ≪≫
    tensorIso ((NatIso.mapHomologicalComplex a (.up ℤ)).app P)
      ((NatIso.mapHomologicalComplex a (.up ℤ)).app Q)

/-- The bidegree component of the conjugated comparison, followed by the target injection.
Source: Stacks Tag 012Z, functor-square calculation, Step 4
(blueprint: lem-pd-total-oplax-conjugation-summands). -/
private noncomputable def conjugatedTotalOplaxComponent (P Q : CochainComplex A₀ ℤ)
    (p q n : ℤ) (h : p + q = n) :
    Fs.obj (E₀.obj (P.X p) ⊗ E₀.obj (Q.X q)) ⟶
      ((Fs.mapHomologicalComplex (.up ℤ)).obj
          ((E₀.mapHomologicalComplex (.up ℤ)).obj P) ⊗
        (Fs.mapHomologicalComplex (.up ℤ)).obj
          ((E₀.mapHomologicalComplex (.up ℤ)).obj Q)).X n :=
  (conjugatedOplaxTensorIso E₀ E₁ Fi Fs a (P.X p) (Q.X q)).hom ≫
    ιTensorObj ((Fs.mapHomologicalComplex (.up ℤ)).obj
        ((E₀.mapHomologicalComplex (.up ℤ)).obj P))
      ((Fs.mapHomologicalComplex (.up ℤ)).obj
        ((E₀.mapHomologicalComplex (.up ℤ)).obj Q)) p q n h

include hFi hFs

omit hFi hFs hFsMonoidal in
set_option linter.unusedSectionVars false in
/-- Naturality of the ordinary conjugated tensorator.
Source: Stacks Tag 012Z; (blueprint: lem-pd-total-oplax-conjugation-summands). -/
private theorem ordinary_naturality :
    ∀ (M M' N N' : A₀) (f : M ⟶ M') (g : N ⟶ N'),
      Fs.map (E₀.map f ⊗ₘ E₀.map g) ≫
          (conjugatedOplaxTensorIso E₀ E₁ Fi Fs a M' N').hom =
        (conjugatedOplaxTensorIso E₀ E₁ Fi Fs a M N).hom ≫
          (Fs.map (E₀.map f) ⊗ₘ Fs.map (E₀.map g)) := by
  intro M M' N N' f g
  simp only [conjugatedOplaxTensorIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_inv, Iso.app_hom, Monoidal.μIso_hom, Monoidal.μIso_inv,
    tensorIso_hom, Category.assoc]
  rw [← Fs.map_comp_assoc, LaxMonoidal.μ_natural, Fs.map_comp, Category.assoc]
  rw [reassoc_of% (a.inv.naturality (f ⊗ₘ g))]
  rw [← E₁.map_comp_assoc, ← OplaxMonoidal.δ_natural, E₁.map_comp, Category.assoc,
    ← OplaxMonoidal.δ_natural_assoc]
  simp only [tensorHom_comp_tensorHom]
  have hf := a.hom.naturality f
  have hg := a.hom.naturality g
  dsimp only [Functor.comp_map] at hf hg
  rw [hf, hg]

omit hFs hFsMonoidal in
/-- The bidegree expansion of the conjugated total comparison.
Source: Stacks Tag 012Z; (blueprint: lem-pd-total-oplax-conjugation-summands). -/
private theorem summand_expansion (P Q : CochainComplex A₀ ℤ) :
    ∀ (p q n : ℤ) (h : p + q = n),
      Fs.map (ιTensorObj ((E₀.mapHomologicalComplex (.up ℤ)).obj P)
          ((E₀.mapHomologicalComplex (.up ℤ)).obj Q) p q n h) ≫
        (conjugatedTotalOplaxIso E₀ E₁ Fi Fs a (hFi := hFi) P Q).hom.f n =
      conjugatedTotalOplaxComponent E₀ E₁ Fi Fs a P Q p q n h := by
  intro p q n h
  change Fs.map (ιTensorObj ((E₀.mapHomologicalComplex (.up ℤ)).obj P)
      ((E₀.mapHomologicalComplex (.up ℤ)).obj Q) p q n h) ≫
    (Fs.map ((E₀.mapCochainComplexμIso P Q).hom.f n) ≫
      a.inv.app ((P ⊗ Q).X n) ≫ E₁.map ((Fi.mapCochainComplexμIso P Q).inv.f n) ≫
        (E₁.mapCochainComplexμIso ((Fi.mapHomologicalComplex (.up ℤ)).obj P)
          ((Fi.mapHomologicalComplex (.up ℤ)).obj Q)).inv.f n ≫
            (tensorIso ((NatIso.mapHomologicalComplex a (.up ℤ)).app P)
              ((NatIso.mapHomologicalComplex a (.up ℤ)).app Q)).hom.f n) = _
  rw [← Fs.map_comp_assoc, ιTensorObj_mapCochainComplexμIso_hom_f,
    Fs.map_comp, Category.assoc]
  erw [reassoc_of% (a.inv.naturality (ιTensorObj P Q p q n h))]
  rw [← E₁.map_comp_assoc, total_inv_component, E₁.map_comp, Category.assoc]
  erw [total_inv_component_assoc]
  rw [show ιTensorObj
      ((E₁.mapHomologicalComplex (.up ℤ)).obj
        ((Fi.mapHomologicalComplex (.up ℤ)).obj P))
      ((E₁.mapHomologicalComplex (.up ℤ)).obj
        ((Fi.mapHomologicalComplex (.up ℤ)).obj Q)) p q n h ≫
      (tensorIso ((NatIso.mapHomologicalComplex a (.up ℤ)).app P)
        ((NatIso.mapHomologicalComplex a (.up ℤ)).app Q)).hom.f n =
    (a.hom.app (P.X p) ⊗ₘ a.hom.app (Q.X q)) ≫ _ from
      GradedObject.Monoidal.ι_tensorHom _ _ p q n h]
  simp only [conjugatedTotalOplaxComponent, conjugatedOplaxTensorIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Monoidal.μIso_hom, Monoidal.μIso_inv, tensorIso_hom, Category.assoc]
  rfl

omit hFsMonoidal in
/-- Naturality of the conjugated total comparison.
Source: Stacks Tag 012Z; (blueprint: lem-pd-total-oplax-conjugation-summands). -/
private theorem total_complex_naturality (P Q : CochainComplex A₀ ℤ) :
    ∀ (P' Q' : CochainComplex A₀ ℤ) (f : P ⟶ P') (g : Q ⟶ Q'),
      (Fs.mapHomologicalComplex (.up ℤ)).map
          ((E₀.mapHomologicalComplex (.up ℤ)).map f ⊗ₘ
            (E₀.mapHomologicalComplex (.up ℤ)).map g) ≫
        (conjugatedTotalOplaxIso E₀ E₁ Fi Fs a (hFi := hFi) P' Q').hom =
      (conjugatedTotalOplaxIso E₀ E₁ Fi Fs a (hFi := hFi) P Q).hom ≫
        ((Fs.mapHomologicalComplex (.up ℤ)).map
            ((E₀.mapHomologicalComplex (.up ℤ)).map f) ⊗ₘ
          (Fs.mapHomologicalComplex (.up ℤ)).map
            ((E₀.mapHomologicalComplex (.up ℤ)).map g)) := by
  intro P' Q' f g
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map Fs
  intro p q h
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  rw [← Fs.map_comp_assoc]
  erw [tensor_injection_map]
  rw [Fs.map_comp, Category.assoc]
  rw [summand_expansion E₀ E₁ Fi Fs a (hFi := hFi) P' Q' p q n h]
  rw [reassoc_of% (summand_expansion E₀ E₁ Fi Fs a (hFi := hFi) P Q p q n h)]
  simp only [conjugatedTotalOplaxComponent, Category.assoc]
  erw [tensor_injection_map]
  simp only [Functor.mapHomologicalComplex_map_f]
  rw [← Category.assoc, ordinary_naturality E₀ E₁ Fi Fs a]
  simp only [Category.assoc]

omit hFs hFsMonoidal in
/-- The signed differential equation for the conjugated total comparison.
Source: Stacks Tag 012Z; (blueprint: lem-pd-total-oplax-conjugation-summands). -/
private theorem total_differential (P Q : CochainComplex A₀ ℤ) :
    ∀ (p q n : ℤ) (h : p + q = n)
        (h₁ : (p + 1) + q = n + 1) (h₂ : p + (q + 1) = n + 1),
      conjugatedTotalOplaxComponent E₀ E₁ Fi Fs a P Q p q n h ≫
          (((Fs.mapHomologicalComplex (.up ℤ)).obj
              ((E₀.mapHomologicalComplex (.up ℤ)).obj P)) ⊗
            ((Fs.mapHomologicalComplex (.up ℤ)).obj
              ((E₀.mapHomologicalComplex (.up ℤ)).obj Q))).d n (n + 1) =
        Fs.map (E₀.map (P.d p (p + 1)) ▷ E₀.obj (Q.X q)) ≫
            conjugatedTotalOplaxComponent E₀ E₁ Fi Fs a P Q (p + 1) q (n + 1) h₁ +
          p.negOnePow •
            (Fs.map (E₀.obj (P.X p) ◁ E₀.map (Q.d q (q + 1))) ≫
              conjugatedTotalOplaxComponent E₀ E₁ Fi Fs a P Q p (q + 1) (n + 1) h₂) := by
  intro p q n h h₁ h₂
  rw [← summand_expansion E₀ E₁ Fi Fs a (hFi := hFi) P Q p q n h,
    Category.assoc, (conjugatedTotalOplaxIso E₀ E₁ Fi Fs a (hFi := hFi) P Q).hom.comm]
  rw [Functor.mapHomologicalComplex_obj_d, ← Fs.map_comp_assoc,
    CochainComplex.ιTensorObj_d _ _ p q n (n + 1) h rfl]
  simp only [Functor.map_add, Functor.map_units_smul, Functor.map_comp,
    Preadditive.add_comp, Linear.units_smul_comp, Category.assoc]
  rw [summand_expansion E₀ E₁ Fi Fs a (hFi := hFi) P Q (p + 1) q (n + 1) h₁,
    summand_expansion E₀ E₁ Fi Fs a (hFi := hFi) P Q p (q + 1) (n + 1) h₂]
  rfl


end
end CategoryTheory.Functor

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex

namespace CategoryTheory.Functor

variable {A₀ : Type u₀} {A₁ : Type u₁} {B₀ : Type u₂} {B₁ : Type u₃}
  [Category.{v₀} A₀] [Category.{v₁} A₁] [Category.{v₂} B₀] [Category.{v₃} B₁]
  [Abelian A₀] [Abelian A₁] [Abelian B₀] [Abelian B₁]
  [MonoidalCategory A₀] [MonoidalCategory A₁]
  [MonoidalCategory B₀] [MonoidalCategory B₁]
  [MonoidalPreadditive A₀] [MonoidalPreadditive A₁]
  [MonoidalPreadditive B₀] [MonoidalPreadditive B₁]
  [HasColimitsOfSize.{0, 0} A₀] [HasColimitsOfSize.{0, 0} A₁]
  [HasColimitsOfSize.{0, 0} B₀] [HasColimitsOfSize.{0, 0} B₁]
  [∀ X : A₀, PreservesColimitsOfSize.{0, 0} ((curriedTensor A₀).obj X)]
  [∀ X : A₀, PreservesColimitsOfSize.{0, 0} ((curriedTensor A₀).flip.obj X)]
  [∀ X : A₁, PreservesColimitsOfSize.{0, 0} ((curriedTensor A₁).obj X)]
  [∀ X : A₁, PreservesColimitsOfSize.{0, 0} ((curriedTensor A₁).flip.obj X)]
  [∀ X : B₀, PreservesColimitsOfSize.{0, 0} ((curriedTensor B₀).obj X)]
  [∀ X : B₀, PreservesColimitsOfSize.{0, 0} ((curriedTensor B₀).flip.obj X)]
  [∀ X : B₁, PreservesColimitsOfSize.{0, 0} ((curriedTensor B₁).obj X)]
  [∀ X : B₁, PreservesColimitsOfSize.{0, 0} ((curriedTensor B₁).flip.obj X)]
  (E₀ : A₀ ⥤ B₀) (E₁ : A₁ ⥤ B₁) (Fi : A₀ ⥤ A₁) (Fs : B₀ ⥤ B₁)
  [E₀.IsEquivalence] [E₁.IsEquivalence]
  [E₀.Additive] [E₁.Additive] [Fi.Additive] [Fs.Additive]
  [E₀.Monoidal] [E₁.Monoidal] [Fi.Monoidal] [mFs : Fs.Monoidal]
  [hFi : ∀ (I : Type) [Countable I], PreservesColimitsOfShape (Discrete I) Fi]
  [hFs : ∀ (I : Type) [Countable I], PreservesColimitsOfShape (Discrete I) Fs]
  (a : Fi ⋙ E₁ ≅ E₀ ⋙ Fs)

/-- The five ordinary factors defining the conjugated inverse tensorator.
Source: Stacks Tag 012Z, functor-square calculation, definition of gamma tilde
(blueprint: lem-pd-total-oplax-conjugation-summands). -/
noncomputable def conjugatedTensorIso (M N : A₀) :
    Fs.obj (E₀.obj M ⊗ E₀.obj N) ≅ Fs.obj (E₀.obj M) ⊗ Fs.obj (E₀.obj N) :=
  Fs.mapIso (Monoidal.μIso E₀ M N) ≪≫ (a.app (M ⊗ N)).symm ≪≫
    E₁.mapIso (Monoidal.μIso Fi M N).symm ≪≫
    (Monoidal.μIso E₁ (Fi.obj M) (Fi.obj N)).symm ≪≫
    tensorIso (a.app M) (a.app N)

/-- The full conjugation, using the canonical preserved-coproduct comparisons.
Source: Stacks Tag 012Z, functor-square calculation, definition of A
(blueprint: lem-pd-total-oplax-conjugation-summands). -/
noncomputable def conjugatedTotalTensorIso (P Q : CochainComplex A₀ ℤ) :
    (Fs.mapHomologicalComplex (.up ℤ)).obj
        ((E₀.mapHomologicalComplex (.up ℤ)).obj P ⊗
          (E₀.mapHomologicalComplex (.up ℤ)).obj Q) ≅
      ((E₀ ⋙ Fs).mapHomologicalComplex (.up ℤ)).obj P ⊗
        ((E₀ ⋙ Fs).mapHomologicalComplex (.up ℤ)).obj Q :=
  (Fs.mapHomologicalComplex (.up ℤ)).mapIso (E₀.mapCochainComplexμIso P Q) ≪≫
    ((NatIso.mapHomologicalComplex a (.up ℤ)).app (P ⊗ Q)).symm ≪≫
    (E₁.mapHomologicalComplex (.up ℤ)).mapIso (Fi.mapCochainComplexμIso P Q).symm ≪≫
    (E₁.mapCochainComplexμIso
      ((Fi.mapHomologicalComplex (.up ℤ)).obj P)
      ((Fi.mapHomologicalComplex (.up ℤ)).obj Q)).symm ≪≫
    tensorIso ((NatIso.mapHomologicalComplex a (.up ℤ)).app P)
      ((NatIso.mapHomologicalComplex a (.up ℤ)).app Q)

/-- The total degree fibre is countable and small.
Source: Stacks Tag 012Z, degree-n direct sum
(blueprint: lem-pd-total-oplax-conjugation-summands).

Proof (step 1): p maps to (p,n-p), inverse to projection onto p. This identifies
this subtype with the integers, hence gives countability and smallness. -/
theorem total_tensor_degree_countable (n : ℤ) :
    Countable {pq : ℤ × ℤ // pq.1 + pq.2 = n} ∧
      Small.{0} {pq : ℤ × ℤ // pq.1 + pq.2 = n} := by
  exact ⟨inferInstance, inferInstance⟩

/-- Preservation and inverse comparison on a degree coproduct for E₀.
Source: Stacks Tag 012Z, functor-square calculation, step 1
(blueprint: lem-pd-total-oplax-conjugation-summands).

Proof: The degree fibre is countable. Equivalences preserve all colimits
(lem-galois-equivalence-preserves-limits), and Fi and Fs preserve countable
coproducts by assumption. Apply preservation to the coproduct cocone.
The inverse comparison carries each image injection to its corresponding injection
by the universal property; the two composites are identities on every injection. -/
theorem total_oplax_coproduct_E₀ (n : ℤ)
    (Z : {pq : ℤ × ℤ // pq.1 + pq.2 = n} → A₀) :
    Nonempty (IsColimit (E₀.mapCocone (colimit.cocone (Discrete.functor Z)))) ∧
      (∀ i, E₀.map (Sigma.ι Z i) ≫ (PreservesCoproduct.iso E₀ Z).hom =
        Sigma.ι (fun j ↦ E₀.obj (Z j)) i) := by
  refine ⟨⟨isColimitOfPreserves E₀ (colimit.isColimit _)⟩, ?_⟩
  intro i
  apply (cancel_mono (PreservesCoproduct.iso E₀ Z).inv).1
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]

/-- Preservation and inverse comparison on a degree coproduct for E₁.
Source: Stacks Tag 012Z, functor-square calculation, step 1
(blueprint: lem-pd-total-oplax-conjugation-summands).

Proof: The degree fibre is countable. Equivalences preserve all colimits
(lem-galois-equivalence-preserves-limits), and Fi and Fs preserve countable
coproducts by assumption. Apply preservation to the coproduct cocone.
The inverse comparison carries each image injection to its corresponding injection
by the universal property; the two composites are identities on every injection. -/
theorem total_oplax_coproduct_E₁ (n : ℤ)
    (Z : {pq : ℤ × ℤ // pq.1 + pq.2 = n} → A₁) :
    Nonempty (IsColimit (E₁.mapCocone (colimit.cocone (Discrete.functor Z)))) ∧
      (∀ i, E₁.map (Sigma.ι Z i) ≫ (PreservesCoproduct.iso E₁ Z).hom =
        Sigma.ι (fun j ↦ E₁.obj (Z j)) i) := by
  refine ⟨⟨isColimitOfPreserves E₁ (colimit.isColimit _)⟩, ?_⟩
  intro i
  apply (cancel_mono (PreservesCoproduct.iso E₁ Z).inv).1
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]

/-- Preservation and inverse comparison on a degree coproduct for Fi.
Source: Stacks Tag 012Z, functor-square calculation, step 1
(blueprint: lem-pd-total-oplax-conjugation-summands).

Proof: The degree fibre is countable. Equivalences preserve all colimits
(lem-galois-equivalence-preserves-limits), and Fi and Fs preserve countable
coproducts by assumption. Apply preservation to the coproduct cocone.
The inverse comparison carries each image injection to its corresponding injection
by the universal property; the two composites are identities on every injection. -/
theorem total_oplax_coproduct_Fi (n : ℤ)
    (Z : {pq : ℤ × ℤ // pq.1 + pq.2 = n} → A₀) :
    Nonempty (IsColimit (Fi.mapCocone (colimit.cocone (Discrete.functor Z)))) ∧
      (∀ i, Fi.map (Sigma.ι Z i) ≫ (PreservesCoproduct.iso Fi Z).hom =
        Sigma.ι (fun j ↦ Fi.obj (Z j)) i) := by
  refine ⟨⟨isColimitOfPreserves Fi (colimit.isColimit _)⟩, ?_⟩
  intro i
  apply (cancel_mono (PreservesCoproduct.iso Fi Z).inv).1
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]

/-- Preservation and inverse comparison on a degree coproduct for Fs.
Source: Stacks Tag 012Z, functor-square calculation, step 1
(blueprint: lem-pd-total-oplax-conjugation-summands).

Proof: The degree fibre is countable. Equivalences preserve all colimits
(lem-galois-equivalence-preserves-limits), and Fi and Fs preserve countable
coproducts by assumption. Apply preservation to the coproduct cocone.
The inverse comparison carries each image injection to its corresponding injection
by the universal property; the two composites are identities on every injection. -/
theorem total_oplax_coproduct_Fs (n : ℤ)
    (Z : {pq : ℤ × ℤ // pq.1 + pq.2 = n} → B₀) :
    Nonempty (IsColimit (Fs.mapCocone (colimit.cocone (Discrete.functor Z)))) ∧
      (∀ i, Fs.map (Sigma.ι Z i) ≫ (PreservesCoproduct.iso Fs Z).hom =
        Sigma.ι (fun j ↦ Fs.obj (Z j)) i) := by
  refine ⟨⟨isColimitOfPreserves Fs (colimit.isColimit _)⟩, ?_⟩
  intro i
  apply (cancel_mono (PreservesCoproduct.iso Fs Z).inv).1
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]

include hFs mFs

set_option linter.unusedSectionVars false

/-- The conjugated total comparison restricts to the ordinary five-factor map.
Source: Stacks Tag 012Z, functor-square calculation, steps 2--4
(blueprint: lem-pd-total-oplax-conjugation-summands).

Proof: Step 1 gives preservation of the degree coproducts. Step 2 uses
lem-sfb-termwise-strong-monoidal to identify each total comparison by its summands.
For step 3, move the injection through the inverse E0 comparison, then through
termwise a inverse by naturality, then through E1 applied to the Fi comparison.
For step 4 move through the E1 comparison and tensor of the two a components.
The coefficient left after the target injection is exactly conjugatedTensorIso.
Coproduct uniqueness shows these restrictions determine the entire component. -/
theorem total_oplax_conjugation_summands (P Q : CochainComplex A₀ ℤ)
    (p q n : ℤ) (h : p + q = n) :
    Fs.map (ιTensorObj ((E₀.mapHomologicalComplex (.up ℤ)).obj P)
        ((E₀.mapHomologicalComplex (.up ℤ)).obj Q) p q n h) ≫
      (conjugatedTotalTensorIso E₀ E₁ Fi Fs (hFi := hFi) a P Q).hom.f n =
    (conjugatedTensorIso E₀ E₁ Fi Fs a (P.X p) (Q.X q)).hom ≫
      ιTensorObj (((E₀ ⋙ Fs).mapHomologicalComplex (.up ℤ)).obj P)
        (((E₀ ⋙ Fs).mapHomologicalComplex (.up ℤ)).obj Q) p q n h := by
  simpa only [conjugatedTotalTensorIso, conjugatedTotalOplaxIso,
    conjugatedTensorIso, conjugatedOplaxTensorIso, conjugatedTotalOplaxComponent,
    Functor.mapHomologicalComplex,
    Functor.comp_obj, Functor.comp_map] using
    summand_expansion E₀ E₁ Fi Fs a (hFi := hFi) P Q p q n h

/-- Ordinary naturality of the conjugated inverse tensorator.
Source: Stacks Tag 012Z, functor-square calculation, step 5
(blueprint: lem-pd-total-oplax-conjugation-summands).

Proof: Each of the five factors is natural in both variables. Compose their
naturality squares; inverse components of a are natural by cancellation. -/
theorem conjugatedTensorIso_naturality {M M' N N' : A₀} (f : M ⟶ M') (g : N ⟶ N') :
    Fs.map (E₀.map f ⊗ₘ E₀.map g) ≫
        (conjugatedTensorIso E₀ E₁ Fi Fs a M' N').hom =
      (conjugatedTensorIso E₀ E₁ Fi Fs a M N).hom ≫
        ((E₀ ⋙ Fs).map f ⊗ₘ (E₀ ⋙ Fs).map g) := by
  simpa only [conjugatedTensorIso, conjugatedOplaxTensorIso, Functor.comp_map] using
    ordinary_naturality E₀ E₁ Fi Fs a _ _ _ _ f g

/-- Naturality of the full conjugation as a map of total complexes.
Source: Stacks Tag 012Z, functor-square calculation, steps 2 and 5
(blueprint: lem-pd-total-oplax-conjugation-summands).

Proof: The single-functor comparisons and termwise a are natural chain
isomorphisms by lem-sfb-termwise-strong-monoidal and ordinary naturality of a.
Functoriality, tensoring and composition preserve these squares. Equivalently,
check the ordinary naturality equation on every bidegree injection. -/
theorem conjugatedTotalTensorIso_naturality
    {P P' Q Q' : CochainComplex A₀ ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    (Fs.mapHomologicalComplex (.up ℤ)).map
        (((E₀.mapHomologicalComplex (.up ℤ)).map f) ⊗ₘ
          ((E₀.mapHomologicalComplex (.up ℤ)).map g)) ≫
        (conjugatedTotalTensorIso E₀ E₁ Fi Fs (hFi := hFi) a P' Q').hom =
      (conjugatedTotalTensorIso E₀ E₁ Fi Fs (hFi := hFi) a P Q).hom ≫
        ((((E₀ ⋙ Fs).mapHomologicalComplex (.up ℤ)).map f) ⊗ₘ
          (((E₀ ⋙ Fs).mapHomologicalComplex (.up ℤ)).map g)) := by
  simpa only [conjugatedTotalTensorIso, conjugatedTotalOplaxIso, Functor.mapHomologicalComplex,
    Functor.comp_obj, Functor.comp_map] using
    total_complex_naturality E₀ E₁ Fi Fs a (hFi := hFi) (hFs := hFs) P Q P' Q' f g

/-- The chain equation on a summand is the two ordinary naturality equations,
with the second multiplied by the Koszul sign, including negative degrees.
Source: Stacks Tag 012Z, functor-square calculation, step 5
(blueprint: lem-pd-total-oplax-conjugation-summands).

Proof: Precompose the chain equation with Fs of the (p,q) injection. Expand both
total differentials as the horizontal term plus (-1)^p times the vertical term.
Use total_oplax_conjugation_summands on the three injections. Additivity preserves
the sum and its sign. Ordinary naturality with (dP,1) and (1,dQ) identifies the two
terms separately. The preserved coproduct cocone makes this the full chain equation.
There are only two outgoing terms at each bidegree; no boundedness or exactness is used. -/
theorem conjugatedTotalTensorIso_differential
    (P Q : CochainComplex A₀ ℤ) (p q : ℤ) :
    Fs.map (ιTensorObj ((E₀.mapHomologicalComplex (.up ℤ)).obj P)
        ((E₀.mapHomologicalComplex (.up ℤ)).obj Q) p q (p + q) rfl) ≫
      (conjugatedTotalTensorIso E₀ E₁ Fi Fs (hFi := hFi) a P Q).hom.f
        (p + q) ≫
        ((((E₀ ⋙ Fs).mapHomologicalComplex (.up ℤ)).obj P) ⊗
          (((E₀ ⋙ Fs).mapHomologicalComplex (.up ℤ)).obj Q)).d (p + q) (p + q + 1) =
    Fs.map (E₀.map (P.d p (p + 1)) ▷ E₀.obj (Q.X q)) ≫
        (conjugatedTensorIso E₀ E₁ Fi Fs a (P.X (p + 1)) (Q.X q)).hom ≫
        ιTensorObj (((E₀ ⋙ Fs).mapHomologicalComplex (.up ℤ)).obj P)
          (((E₀ ⋙ Fs).mapHomologicalComplex (.up ℤ)).obj Q)
          (p + 1) q (p + q + 1) (by omega) +
      p.negOnePow • (Fs.map (E₀.obj (P.X p) ◁ E₀.map (Q.d q (q + 1))) ≫
        (conjugatedTensorIso E₀ E₁ Fi Fs a (P.X p) (Q.X (q + 1))).hom ≫
        ιTensorObj (((E₀ ⋙ Fs).mapHomologicalComplex (.up ℤ)).obj P)
          (((E₀ ⋙ Fs).mapHomologicalComplex (.up ℤ)).obj Q)
          p (q + 1) (p + q + 1) (by omega)) := by
  erw [reassoc_of% (total_oplax_conjugation_summands E₀ E₁ Fi Fs
    (hFi := hFi) (hFs := hFs) a P Q p q (p + q) rfl)]
  simpa only [conjugatedTotalOplaxComponent, conjugatedOplaxTensorIso,
    conjugatedTensorIso, Category.assoc, Functor.mapHomologicalComplex,
    Functor.comp_obj, Functor.comp_map] using
    total_differential E₀ E₁ Fi Fs a (hFi := hFi) P Q p q (p + q) rfl
      (by omega) (by omega)

end CategoryTheory.Functor
