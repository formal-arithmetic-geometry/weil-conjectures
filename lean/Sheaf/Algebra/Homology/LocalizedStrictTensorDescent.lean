/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Algebra.Homology.LocalizedStrictTensorLinearEvaluation
import Sheaf.Algebra.Homology.LocalizedStrictTensorData
public import Sheaf.Algebra.Homology.RingedOpenTotalTensorKFlat
public import Sheaf.Algebra.Homology.SiteOneSidedTensorNormalization
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Sheaf.Paper.ReductionPullbackDerivedTower
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import all Sheaf.Paper.ReductionPullbackDerivedTower
import Sheaf.Algebra.Homology.RingedOpenFlatResolution
import Sheaf.CategoryTheory.SliceTensorGeneratorCoherence
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived


/-! # Normalized localized extension on derived strict coefficient towers

Source: Stacks Project, Modules on Sites, Tag 0E8I, lemma-j-shriek-and-tensor;
Cohomology on Sites, Tags 06YS and 06YU; Categories, Tags 04VG and 04VK.
(blueprint: lem-sf-cbc-localized-strict-tensor-descent).

Strict towers are localized after taking complexes. The reduction functor is the
universal left derived functor of the actual ordinary tensor tower, equivalently
the diagram-site tensor of the constant diagram with the coefficient tower.
The counit fixes all representative comparisons; no functorial resolution is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe c v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace SheafOfModules.LocalizedStrictTensor
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r}) (V : C)
  [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- The ordinary inverse-projection comparison of strict towers.
Source: Stacks 0E8I (blueprint: lem-sf-cbc-localized-strict-tensor-descent). -/
abbrev OrdinaryComparison (S : AlgebraTowers.{c, v, r} R) :=
  localizedSystemExtension.{c, v, r} R V ⋙ reduction.{c, v, r} R S ≅
    reduction.{max c v, v, r} (R.over V) (S ⋙ sliceAlgebras.{c, v, r} R V) ⋙
      towerExtension.{c, v, r} R V

/-- The derived comparison of the specified universal strict reductions.
Source: Stacks 06YU (blueprint: lem-sf-cbc-localized-strict-tensor-descent). -/
abbrev DerivedComparison (m : ReductionModel.{c, v, r} R)
    (mV : ReductionModel.{max c v, v, r} (R.over V)) (S : AlgebraTowers.{c, v, r} R) :=
  (localizedSystemExtension.{c, v, r} R V).mapDerivedCategory ⋙ m.F.obj S ≅
    mV.F.obj (S ⋙ sliceAlgebras.{c, v, r} R V) ⋙
      (towerExtension.{c, v, r} R V).mapDerivedCategory

/-- Precisely the normalized descent assertions for the two canonical reductions.
This is conclusion data, not a hypothesis supplying a comparison.
Source: Stacks 0E8I, 06YU, 04VG, 04VK
(blueprint: lem-sf-cbc-localized-strict-tensor-descent). -/
structure Descent (m : ReductionModel.{c, v, r} R)
    (mV : ReductionModel.{max c v, v, r} (R.over V)) where
  /-- The strict ordinary inverse projection. -/
  ordinary : ∀ S : AlgebraTowers.{c, v, r} R, OrdinaryComparison.{c, v, r} R V S
  /-- Its generator equation includes preservation of the scalar unit. -/
  ordinary_normalized : ∀ S, OrdinaryNormalized.{c, v, r} R V S (ordinary S)
  /-- The natural isomorphism on the unbounded derived categories of strict towers. -/
  derived : ∀ S : AlgebraTowers.{c, v, r} R, DerivedComparison.{c, v, r} R V m mV S
  /-- Every flat-term K-flat representative gives exactly the specified chain map. -/
  normalized : ∀ S, DerivedNormalized.{c, v, r} R V m mV S (ordinary S) (derived S)
  /-- Uniqueness among natural isomorphisms with this representative normalization. -/
  unique : ∀ (S : AlgebraTowers.{c, v, r} R)
    (ρ' : DerivedComparison.{c, v, r} R V m mV S),
    DerivedNormalized.{c, v, r} R V m mV S (ordinary S) ρ' → ρ' = derived S
  /-- Naturality in every coefficient-tower map already before localization. -/
  ordinary_natural : ∀ (S T : AlgebraTowers.{c, v, r} R) (a : S ⟶ T)
    (M : Modules.{max c v, v, r} (R.over V)),
    ((reductionFamily.{c, v, r} R).map a).app
        ((localizedSystemExtension.{c, v, r} R V).obj M) ≫ (ordinary T).hom.app M =
      (ordinary S).hom.app M ≫ (towerExtension.{c, v, r} R V).map
        (((reductionFamily.{max c v, v, r} (R.over V)).map
          (Functor.whiskerRight a (sliceAlgebras.{c, v, r} R V))).app M)
  /-- Naturality in every coefficient-tower map after localization. -/
  derived_natural : ∀ (S T : AlgebraTowers.{c, v, r} R) (a : S ⟶ T)
    (K : D.{max c v, v, r} (R.over V)),
    (m.F.map a).app ((localizedSystemExtension.{c, v, r} R V).mapDerivedCategory.obj K) ≫
        (derived T).hom.app K =
      (derived S).hom.app K ≫ (towerExtension.{c, v, r} R V).mapDerivedCategory.map
        ((mV.F.map (Functor.whiskerRight a (sliceAlgebras.{c, v, r} R V))).app K)
  /-- At every positive level the comparison is scalar restriction of an S_n-linear iso. -/
  linear : ∀ (S : AlgebraTowers.{c, v, r} R) (n : ℕᵒᵖ),
    LinearEvaluation.{c, v, r} R V m mV S n (ordinary S) (derived S)

private theorem reduction_models : Nonempty (ReductionModel.{c, v, r} R) := by
  classical
  have pairs (S : AlgebraTowers.{c, v, r} R) :
      ∃ (T : D.{c, v, r} R ⥤ DT.{c, v, r} R)
        (ε : DerivedCategory.Q ⋙ T ⟶
          (reduction.{c, v, r} R S).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
        T.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso _ (.up ℤ)) ∧
          ∀ P, Resolving.{c, v, r} R P → IsIso (ε.app P) := by
    let := cochainModulesPreadditive.{c, v, max c v r} R
    exact cochainDerivedExists
      (reduction.{c, v, r} R S) (Resolving.{c, v, r} R)
      (CategoryTheory.StrictReduction.resolves (R := R))
      (fun f hf hP hQ ↦ CategoryTheory.StrictReduction.reductionInverts
        (S ⋙ algebraModules.{c, v, r} R) f hf hP hQ)
  choose T ε hu hc using pairs
  let (S : AlgebraTowers.{c, v, r} R) := hu S
  let τ {S T : AlgebraTowers.{c, v, r} R} (a : S ⟶ T) :=
    Functor.whiskerRight
      (NatTrans.mapHomologicalComplex ((reductionFamily.{c, v, r} R).map a) (.up ℤ))
      DerivedCategory.Q
  let F : AlgebraTowers.{c, v, r} R ⥤ D.{c, v, r} R ⥤ DT.{c, v, r} R :=
    { obj := T
      map {S U} a := Functor.leftDerivedNatTrans (T S) (T U) (ε S) (ε U)
        (HomologicalComplex.quasiIso _ (.up ℤ)) (τ a)
      map_id S := by
        have he : τ (𝟙 S) = 𝟙 _ := by
          ext P
          simp [τ]
        rw [he]
        exact Functor.leftDerivedNatTrans_id (T S) (ε S)
          (HomologicalComplex.quasiIso _ (.up ℤ))
      map_comp {S U W} a b := by
        have he : τ (a ≫ b) = τ a ≫ τ b := by
          ext P
          simp [τ]
        rw [he, Functor.leftDerivedNatTrans_comp] }
  exact ⟨{ F := F
           ε := ε
           universal := hu
           computes := hc
           coefficient := fun S U a P ↦
             Functor.leftDerivedNatTrans_app (T S) (T U) (ε S) (ε U)
               (HomologicalComplex.quasiIso _ (.up ℤ)) (τ a) P }⟩

private theorem extension_resolving
    (P : CochainComplex (Modules.{max c v, v, r} (R.over V)) ℤ)
    (hP : Resolving.{max c v, v, r} (R.over V) P) :
    Resolving.{c, v, r} R
      (((localizedSystemExtension.{c, v, r} R V).mapHomologicalComplex (.up ℤ)).obj P) := by
  exact ⟨(ringedOpen_preserves_flat_resolution.{c, v, r} R V).1 P hP.1,
    (ringedOpen_preserves_flat_resolution.{c, v, r} R V).2.1 P hP.2⟩

private def coefficient_map (S T : AlgebraTowers.{c, v, r} R) (a : S ⟶ T) :
    reduction.{c, v, r} R S ⟶ reduction.{c, v, r} R T :=
  (reductionFamily.{c, v, r} R).map a

attribute [local irreducible] cochainRepresentativeWhiskering
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors

private theorem resolving_iso
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {B : Type*} [Category* B]
    (good : CochainComplex A ℤ → Prop)
    (res : ∀ K, ∃ (P : CochainComplex A ℤ) (p : P ⟶ K), good P ∧ QuasiIso p)
    (F G : DerivedCategory A ⥤ B) (H : CochainComplex A ℤ ⥤ B)
    (a : DerivedCategory.Q ⋙ F ⟶ H) (b : DerivedCategory.Q ⋙ G ⟶ H)
    (ha : ∀ P, good P → IsIso (a.app P))
    (hb : ∀ P, good P → IsIso (b.app P)) :
    ∃! e : F ≅ G, ∀ P, good P →
      e.hom.app (DerivedCategory.Q.obj P) ≫ b.app P = a.app P := by
  let P : ObjectProperty (CochainComplex A ℤ) := good
  let l := P.ι ⋙ DerivedCategory.Q
  let a' := Functor.whiskerLeft P.ι a
  let b' := Functor.whiskerLeft P.ι b
  have (X : P.FullSubcategory) : IsIso (a'.app X) := ha X.obj X.property
  have (X : P.FullSubcategory) : IsIso (b'.app X) := hb X.obj X.property
  have : IsIso a' := NatIso.isIso_of_isIso_app a'
  have : IsIso b' := NatIso.isIso_of_isIso_app b'
  let ff := cochainRepresentativeWhiskering good res B
  let e := ff.preimageIso (asIso a' ≪≫ (asIso b').symm)
  have he : Functor.whiskerLeft l e.hom ≫ b' = a' := by
    rw [show Functor.whiskerLeft l e.hom =
      (asIso a' ≪≫ (asIso b').symm).hom from ff.map_preimage _]
    simp
  refine ⟨e, fun K hK ↦ NatTrans.congr_app he ⟨K, hK⟩, ?_⟩
  intro e' he'
  apply Iso.ext
  apply ff.map_injective
  apply (cancel_mono b').1
  ext X
  exact (he' X.obj X.property).trans (NatTrans.congr_app he X).symm

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.cochainModulesMonoidal


private theorem insert_identity
    {A : Type*} [Category* A] {X Y Z W : A}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W) :
    a ≫ 𝟙 Y ≫ b ≫ c = a ≫ b ≫ c := by
  rw [Category.id_comp]

private theorem comparison_square
    {A : Type*} [Category* A]
    {X₀ X₁ Y₀ Y₁ U₀ U₁ W₀ W₁ : A}
    (a : X₀ ⟶ X₁) (b : Y₀ ⟶ Y₁)
    (c₀ : X₀ ⟶ U₀) (c₁ : X₁ ⟶ U₁)
    (d₀ : Y₀ ⟶ W₀) (d₁ : Y₁ ⟶ W₁) [Mono d₁]
    (r₀ : U₀ ⟶ W₀) (r₁ : U₁ ⟶ W₁)
    (ρ₀ : X₀ ⟶ Y₀) (ρ₁ : X₁ ⟶ Y₁)
    (u : U₀ ⟶ U₁) (w : W₀ ⟶ W₁)
    (h₀ : c₀ ≫ r₀ = ρ₀ ≫ d₀) (h₁ : c₁ ≫ r₁ = ρ₁ ≫ d₁)
    (hc : a ≫ c₁ = c₀ ≫ u) (hd : b ≫ d₁ = d₀ ≫ w)
    (hr : u ≫ r₁ = r₀ ≫ w) : a ≫ ρ₁ = ρ₀ ≫ b := by
  apply (cancel_mono d₁).1
  simp only [Category.assoc]
  rw [← h₁, ← Category.assoc, hc, Category.assoc, hr,
    ← Category.assoc, h₀, Category.assoc, ← hd]

private theorem exact_comparison
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (N : C ⥤ D) [N.Additive] [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    (E : B ⥤ D) [E.Additive] (F : A ⥤ C) [F.Additive]
    (T : DerivedCategory B ⥤ DerivedCategory D)
    (U : DerivedCategory A ⥤ DerivedCategory C)
    (ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (δ : DerivedCategory.Q ⋙ U ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (good : CochainComplex A ℤ → Prop)
    (res : ∀ K, ∃ (P : CochainComplex A ℤ) (p : P ⟶ K), good P ∧ QuasiIso p)
    (hε : ∀ P, good P → IsIso (ε.app ((L.mapHomologicalComplex (.up ℤ)).obj P)))
    (hδ : ∀ P, good P → IsIso (δ.app P)) (η : L ⋙ E ≅ F ⋙ N) :
    ∃! ρ : L.mapDerivedCategory ⋙ T ≅ U ⋙ N.mapDerivedCategory,
      NormalizedExactDescent L N E F T U ε δ good η ρ := by
  let LC := L.mapHomologicalComplex (.up ℤ)
  let FC := F.mapHomologicalComplex (.up ℤ)
  let a : DerivedCategory.Q ⋙ (L.mapDerivedCategory ⋙ T) ⟶
      FC ⋙ N.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight L.mapDerivedCategoryFactors.hom T ≫
      Functor.whiskerLeft LC ε ≫
      Functor.whiskerRight (NatIso.mapHomologicalComplex η (.up ℤ)).hom DerivedCategory.Q
  let b : DerivedCategory.Q ⋙ (U ⋙ N.mapDerivedCategory) ⟶
      FC ⋙ N.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight δ N.mapDerivedCategory ≫
      Functor.whiskerLeft FC N.mapDerivedCategoryFactors.hom
  have ha (P) (hP : good P) : IsIso (a.app P) := by
    have := hε P hP
    dsimp only [a, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.comp_obj]
    infer_instance
  have hb (P) (hP : good P) : IsIso (b.app P) := by
    have := hδ P hP
    dsimp only [b, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.comp_obj]
    infer_instance
  obtain ⟨ρ, hρ, hu⟩ := resolving_iso good res _ _ _ a b ha hb
  exact ⟨ρ, fun P hP ↦ (hρ P hP).symm, fun ρ' hρ' ↦ hu ρ' (fun P hP ↦ (hρ' P hP).symm)⟩

private def scalar_to_extend (A : Under R) (e : ScalarModel.{c, v, r} R A) :
    e.E ≅ SliceTensorGenerator.extend.{c, v, r} A.hom :=
  NatIso.ofComponents (fun M ↦ eqToIso (e.obj_eq M)) (by
    intro M N f
    change e.E.map f ≫ eqToHom (e.obj_eq N) =
      eqToHom (e.obj_eq M) ≫ changeOfRingsHom A.hom M f
    rw [e.map_eq]
    simp)

private def ordinary_evaluation
    (S : AlgebraTowers.{c, v, r} R) (n : ℕᵒᵖ)
    (t : SliceTensorGenerator.TensorLift.{c, v, r} R (S.obj n))
    (e : ScalarModel.{c, v, r} R (S.obj n)) :
    reduction.{c, v, r} R S ⋙ evaluation.{c, v, r} R n ≅
      e.E ⋙ scalars.{c, v, r} R (S.obj n) :=
  t ≪≫ (Functor.isoWhiskerRight (scalar_to_extend R (S.obj n) e)
    (scalars.{c, v, r} R (S.obj n))).symm

private theorem ordinary_evaluation_normalized
    (S : AlgebraTowers.{c, v, r} R) (n : ℕᵒᵖ)
    (t : SliceTensorGenerator.TensorLift.{c, v, r} R (S.obj n))
    (ht : SliceTensorGenerator.TensorLiftNormalized.{c, v, r} R (S.obj n) t)
    (e : ScalarModel.{c, v, r} R (S.obj n)) :
    EvaluationOrdinaryNormalized.{c, v, r} R S n e
      (ordinary_evaluation R S n t e) := by
  intro M W p s
  change ((scalars.{c, v, r} R (S.obj n)).map
      (eqToHom (e.obj_eq M).symm)).val.app W
        ((t.hom.app M).val.app W (pure R _ _ W p s)) = _
  erw [ht]
  rfl


private theorem evaluated_comparison
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (E : A ⥤ B) [E.Additive] (F : A ⥤ C) [F.Additive]
    (H : B ⥤ D) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (N : C ⥤ D) [N.Additive] [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    (T : DerivedCategory A ⥤ DerivedCategory B)
    (U : DerivedCategory A ⥤ DerivedCategory C)
    (ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (δ : DerivedCategory.Q ⋙ U ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (good : CochainComplex A ℤ → Prop)
    (res : ∀ K, ∃ (P : CochainComplex A ℤ) (p : P ⟶ K), good P ∧ QuasiIso p)
    (hε : ∀ P, good P → IsIso (ε.app P))
    (hδ : ∀ P, good P → IsIso (δ.app P)) (η : E ⋙ H ≅ F ⋙ N) :
    ∃! ρ : T ⋙ H.mapDerivedCategory ≅ U ⋙ N.mapDerivedCategory,
      ∀ P, good P → EvaluatedDescentEquation E F H N T U ε δ η ρ P := by
  let EC := E.mapHomologicalComplex (.up ℤ)
  let FC := F.mapHomologicalComplex (.up ℤ)
  let a : DerivedCategory.Q ⋙ (T ⋙ H.mapDerivedCategory) ⟶
      FC ⋙ N.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight ε H.mapDerivedCategory ≫
      Functor.whiskerLeft EC H.mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight (NatIso.mapHomologicalComplex η (.up ℤ)).hom DerivedCategory.Q
  let b : DerivedCategory.Q ⋙ (U ⋙ N.mapDerivedCategory) ⟶
      FC ⋙ N.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight δ N.mapDerivedCategory ≫
      Functor.whiskerLeft FC N.mapDerivedCategoryFactors.hom
  have ha (P) (hP : good P) : IsIso (a.app P) := by
    have := hε P hP
    dsimp only [a, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.comp_obj]
    infer_instance
  have hb (P) (hP : good P) : IsIso (b.app P) := by
    have := hδ P hP
    dsimp only [b, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.comp_obj]
    infer_instance
  obtain ⟨ρ, hρ, hu⟩ := resolving_iso good res _ _ _ a b ha hb
  exact ⟨ρ, fun P hP ↦ (hρ P hP).symm, fun ρ' hρ' ↦ hu ρ' (fun P hP ↦ (hρ' P hP).symm)⟩

private theorem exactDerivedSquare_fac
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : B ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : A ⥤ C) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (I : C ⥤ D) [I.Additive] [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (η : F ⋙ G ≅ H ⋙ I) (K : CochainComplex A ℤ) :
    (exactDerivedSquare F G H I η).hom.app (DerivedCategory.Q.obj K) ≫
      I.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
      I.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex η (.up ℤ)).hom.app K) := by
  have h1 := Functor.mapDerivedCategoryCompIso_fac F G K
  have hc1 : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
      (.up ℤ)).hom.app K = 𝟙 _ := rfl
  erw [hc1, DerivedCategory.Q.map_id, Category.comp_id] at h1
  have h2 := Functor.mapDerivedCategoryCompIso_fac H I K
  have hc2 : (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ I))
      (.up ℤ)).hom.app K = 𝟙 _ := rfl
  erw [hc2, DerivedCategory.Q.map_id, Category.comp_id] at h2
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F G).hom.app
    (DerivedCategory.Q.obj K))).1
  unfold exactDerivedSquare
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  erw [h2, Functor.mapDerivedCategoryNatIso_fac, ← h1]
  simp only [Category.assoc]
  rfl



section Pasting
variable {A B C D E F : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E] [Abelian F]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory F]
  (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (N : C ⥤ D) [N.Additive] [PreservesFiniteLimits N] [PreservesFiniteColimits N]
  (H : D ⥤ B) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (H' : C ⥤ A) [H'.Additive] [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
  (M : E ⥤ F) [M.Additive] [PreservesFiniteLimits M] [PreservesFiniteColimits M]
  (U : F ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (U' : E ⥤ A) [U'.Additive] [PreservesFiniteLimits U'] [PreservesFiniteColimits U']
  (X : B ⥤ D) [X.Additive] (Y : A ⥤ C) [Y.Additive]
  (Z : B ⥤ F) [Z.Additive] (Z' : A ⥤ E) [Z'.Additive]
  (T : DerivedCategory B ⥤ DerivedCategory D)
  (T' : DerivedCategory A ⥤ DerivedCategory C)
  (W : DerivedCategory B ⥤ DerivedCategory F)
  (W' : DerivedCategory A ⥤ DerivedCategory E)
  (a : DerivedCategory.Q ⋙ T ⟶ X.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (b : DerivedCategory.Q ⋙ T' ⟶ Y.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (e : DerivedCategory.Q ⋙ W ⟶ Z.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (f : DerivedCategory.Q ⋙ W' ⟶ Z'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (η : L ⋙ X ≅ Y ⋙ N) (p : X ⋙ H ≅ Z ⋙ U) (q : Y ⋙ H' ≅ Z' ⋙ U')
  (σ : L ⋙ Z ≅ Z' ⋙ M) (κ : N ⋙ H ≅ H' ⋙ L) (θ : U' ⋙ L ≅ M ⋙ U)
  (ρ : L.mapDerivedCategory ⋙ T ≅ T' ⋙ N.mapDerivedCategory)
  (pd : T ⋙ H.mapDerivedCategory ≅ W ⋙ U.mapDerivedCategory)
  (qd : T' ⋙ H'.mapDerivedCategory ≅ W' ⋙ U'.mapDerivedCategory)
  (β : L.mapDerivedCategory ⋙ W ≅ W' ⋙ M.mapDerivedCategory)

private theorem paste_at (P : CochainComplex A ℤ)
    (hf : IsIso (f.app P))
    (hρ : ExactDescentEquation L N X Y T T' a b η ρ P)
    (hp : EvaluatedDescentEquation X Z H U T W a e p pd
      ((L.mapHomologicalComplex (.up ℤ)).obj P))
    (hq : EvaluatedDescentEquation Y Z' H' U' T' W' b f q qd P)
    (hβ : ExactDescentEquation L M Z Z' W W' e f σ β P)
    (hord : ∀ K, H.map (η.hom.app K) ≫ κ.hom.app (Y.obj K) ≫
      L.map (q.hom.app K) ≫ θ.hom.app (Z'.obj K) =
      p.hom.app (L.obj K) ≫ U.map (σ.hom.app K)) :
    H.mapDerivedCategory.map (ρ.hom.app (DerivedCategory.Q.obj P)) ≫
      (exactDerivedSquare N H H' L κ).hom.app (T'.obj (DerivedCategory.Q.obj P)) ≫
      L.mapDerivedCategory.map (qd.hom.app (DerivedCategory.Q.obj P)) ≫
      (exactDerivedSquare U' L M U θ).hom.app (W'.obj (DerivedCategory.Q.obj P)) =
    pd.hom.app (L.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
      U.mapDerivedCategory.map (β.hom.app (DerivedCategory.Q.obj P)) := by
  dsimp only [EvaluatedDescentEquation] at hp hq
  dsimp only [ExactDescentEquation] at hρ hβ
  let LC := L.mapHomologicalComplex (.up ℤ)
  let YC := Y.mapHomologicalComplex (.up ℤ)
  let ZC := Z.mapHomologicalComplex (.up ℤ)
  let ZC' := Z'.mapHomologicalComplex (.up ℤ)
  let s := L.mapDerivedCategoryFactors.hom.app P
  let k := (exactDerivedSquare N H H' L κ).hom
  let t := (exactDerivedSquare U' L M U θ).hom
  let oc := (NatIso.mapHomologicalComplex η (.up ℤ)).hom.app P
  let pc := (NatIso.mapHomologicalComplex p (.up ℤ)).hom.app (LC.obj P)
  let qc := (NatIso.mapHomologicalComplex q (.up ℤ)).hom.app P
  let sc := (NatIso.mapHomologicalComplex σ (.up ℤ)).hom.app P
  let kc := (NatIso.mapHomologicalComplex κ (.up ℤ)).hom.app (YC.obj P)
  let tc := (NatIso.mapHomologicalComplex θ (.up ℤ)).hom.app (ZC'.obj P)
  have hordc : (H.mapHomologicalComplex (.up ℤ)).map oc ≫ kc ≫
      LC.map qc ≫ tc = pc ≫ (U.mapHomologicalComplex (.up ℤ)).map sc := by
    ext i
    exact hord (P.X i)
  have hq' := congrArg L.mapDerivedCategory.map hq
  simp only [Functor.map_comp] at hq'
  have hρ' := congrArg H.mapDerivedCategory.map hρ
  simp only [Functor.map_comp] at hρ'
  have hβ' := congrArg U.mapDerivedCategory.map hβ
  simp only [Functor.map_comp] at hβ'
  have ht := exactDerivedSquare_fac U' L M U θ (ZC'.obj P)
  have hk := exactDerivedSquare_fac N H H' L κ (YC.obj P)
  have hf' : IsIso (U.mapDerivedCategory.map (M.mapDerivedCategory.map (f.app P)) ≫
      U.mapDerivedCategory.map (M.mapDerivedCategoryFactors.hom.app (ZC'.obj P)) ≫
      U.mapDerivedCategoryFactors.hom.app
        ((M.mapHomologicalComplex (.up ℤ)).obj (ZC'.obj P))) := by
    let := hf
    infer_instance
  apply (cancel_mono (U.mapDerivedCategory.map (M.mapDerivedCategory.map (f.app P)) ≫
    U.mapDerivedCategory.map (M.mapDerivedCategoryFactors.hom.app (ZC'.obj P)) ≫
    U.mapDerivedCategoryFactors.hom.app
      ((M.mapHomologicalComplex (.up ℤ)).obj (ZC'.obj P)))).1
  change (H.mapDerivedCategory.map (ρ.hom.app (DerivedCategory.Q.obj P)) ≫
    k.app (T'.obj (DerivedCategory.Q.obj P)) ≫
    L.mapDerivedCategory.map (qd.hom.app (DerivedCategory.Q.obj P)) ≫
    t.app (W'.obj (DerivedCategory.Q.obj P))) ≫ _ = _
  with_unfolding_all simp only [Category.assoc]
  erw [← t.naturality_assoc (f.app P)]
  erw [ht]
  change H.mapDerivedCategory.map (ρ.hom.app (DerivedCategory.Q.obj P)) ≫
    k.app (T'.obj (DerivedCategory.Q.obj P)) ≫
    L.mapDerivedCategory.map (qd.hom.app (DerivedCategory.Q.obj P)) ≫
    L.mapDerivedCategory.map (U'.mapDerivedCategory.map (f.app P)) ≫
    L.mapDerivedCategory.map (U'.mapDerivedCategoryFactors.hom.app (ZC'.obj P)) ≫
    L.mapDerivedCategoryFactors.hom.app
      ((U'.mapHomologicalComplex (.up ℤ)).obj (ZC'.obj P)) ≫
    DerivedCategory.Q.map tc = _
  erw [← reassoc_of% hq']
  erw [L.mapDerivedCategoryFactors_hom_naturality_assoc]
  erw [← k.naturality_assoc (b.app P)]
  erw [reassoc_of% hk]
  erw [← reassoc_of% hρ']
  erw [H.mapDerivedCategoryFactors_hom_naturality_assoc]
  with_unfolding_all simp only [← DerivedCategory.Q.map_comp]
  erw [hordc, DerivedCategory.Q.map_comp]
  change H.mapDerivedCategory.map (T.map s) ≫
    H.mapDerivedCategory.map (a.app (LC.obj P)) ≫
    H.mapDerivedCategoryFactors.hom.app ((X.mapHomologicalComplex (.up ℤ)).obj (LC.obj P)) ≫
    DerivedCategory.Q.map pc ≫ DerivedCategory.Q.map
      ((U.mapHomologicalComplex (.up ℤ)).map sc) = _
  erw [reassoc_of% hp]
  have hn := pd.hom.naturality s
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  erw [← U.mapDerivedCategory.map_comp_assoc]
  erw [← U.mapDerivedCategoryFactors_hom_naturality sc]
  change pd.hom.app (L.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
    U.mapDerivedCategory.map (W.map s ≫ e.app (LC.obj P)) ≫
    U.mapDerivedCategory.map (DerivedCategory.Q.map sc) ≫
    U.mapDerivedCategoryFactors.hom.app
      ((M.mapHomologicalComplex (.up ℤ)).obj (ZC'.obj P)) = _
  have hh := congrArg (fun z ↦
    pd.hom.app (L.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫ z ≫
    U.mapDerivedCategoryFactors.hom.app
      ((M.mapHomologicalComplex (.up ℤ)).obj (ZC'.obj P))) hβ'
  simpa only [U.mapDerivedCategory.map_comp, Category.assoc] using hh

end Pasting

private theorem transport_square
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (L : A ⥤ B) (M : C ⥤ D) (U : D ⥤ B) (U' : C ⥤ A)
    (θ : U' ⋙ L ≅ M ⋙ U)
    {X : B} {Y : A} {S S' : D} {T T' : C}
    (a : S ≅ S') (b : T ≅ T') (t : X ≅ U.obj S') (q : Y ≅ U'.obj T')
    (l : S' ⟶ M.obj T') (o : X ⟶ L.obj Y)
    (h : o = t.hom ≫ U.map l ≫ θ.inv.app T' ≫ L.map q.inv) :
    o ≫ L.map (q.hom ≫ U'.map b.inv) ≫ θ.hom.app T =
      (t.hom ≫ U.map a.inv) ≫ U.map (a.hom ≫ l ≫ M.map b.inv) := by
  rw [h]
  simp only [Functor.map_comp, Category.assoc]
  rw [← L.map_comp_assoc, q.inv_hom_id, L.map_id, Category.id_comp]
  have hn := θ.hom.naturality b.inv
  dsimp only [Functor.comp_map] at hn
  rw [hn, Iso.inv_hom_id_app_assoc]
  simp only [← U.map_comp_assoc, Iso.inv_hom_id_assoc]

private def scalar_ordinary
    (g : SliceTensorGenerator.Coherence.{c, v, r} R V) (A : Under R)
    (e : ScalarModel.{c, v, r} R A)
    (eV : ScalarModel.{max c v, v, r} (R.over V)
      ((sliceAlgebras.{c, v, r} R V).obj A)) :
    localizedSystemExtension.{c, v, r} R V ⋙ e.E ≅
      eV.E ⋙ localizedSystemExtension.{c, v, r} A.right V :=
  Functor.isoWhiskerLeft (localizedSystemExtension.{c, v, r} R V)
      (scalar_to_extend R A e) ≪≫
    g.linear A ≪≫
      (Functor.isoWhiskerRight
        (scalar_to_extend.{max c v, v, r} (R.over V)
          ((sliceAlgebras.{c, v, r} R V).obj A) eV)
        (localizedSystemExtension.{c, v, r} A.right V)).symm

private theorem scalar_ordinary_square
    (g : SliceTensorGenerator.Coherence.{c, v, r} R V)
    (S : AlgebraTowers.{c, v, r} R) (n : ℕᵒᵖ)
    (e : ScalarModel.{c, v, r} R (S.obj n))
    (eV : ScalarModel.{max c v, v, r} (R.over V)
      ((sliceAlgebras.{c, v, r} R V).obj (S.obj n)))
    (M : Modules.{max c v, v, r} (R.over V)) :
    (evaluation.{c, v, r} R n).map ((g.ordinary S).hom.app M) ≫
      (localizedSystemExtension.{c, v, r} R V).map
        ((ordinary_evaluation.{max c v, v, r} (R.over V)
          (S ⋙ sliceAlgebras.{c, v, r} R V) n (g.sliceTensorLift (S.obj n)) eV).hom.app M) ≫
      (g.restrictionComparison (S.obj n)).hom.app (eV.E.obj M) =
    (ordinary_evaluation R S n (g.tensorLift (S.obj n)) e).hom.app
        ((localizedSystemExtension.{c, v, r} R V).obj M) ≫
      (scalars.{c, v, r} R (S.obj n)).map
        ((scalar_ordinary R V g (S.obj n) e eV).hom.app M) := by
  exact transport_square
    (A := Modules.{max c v, v, r} (R.over V)) (B := Modules.{c, v, r} R)
    (C := Modules.{max c v, v, r}
      ((sliceAlgebras.{c, v, r} R V).obj (S.obj n)).right)
    (D := Modules.{c, v, r} (S.obj n).right)
    (localizedSystemExtension.{c, v, r} R V)
    (localizedSystemExtension.{c, v, r} (S.obj n).right V)
    (scalars.{c, v, r} R (S.obj n))
    (scalars.{max c v, v, r} (R.over V)
      ((sliceAlgebras.{c, v, r} R V).obj (S.obj n)))
    (g.restrictionComparison (S.obj n))
    ((scalar_to_extend R (S.obj n) e).app
      ((localizedSystemExtension.{c, v, r} R V).obj M))
    ((scalar_to_extend.{max c v, v, r} (R.over V)
      ((sliceAlgebras.{c, v, r} R V).obj (S.obj n)) eV).app M)
    ((g.tensorLift (S.obj n)).app ((localizedSystemExtension.{c, v, r} R V).obj M))
    ((g.sliceTensorLift (S.obj n)).app M)
    ((g.linear (S.obj n)).hom.app M) (((g.ordinary S).hom.app M).app n)
    (g.ordinary_linear S M n)

private theorem comparison_natural
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (N : C ⥤ D) [N.Additive] [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    (E₀ E₁ : B ⥤ D) [E₀.Additive] [E₁.Additive]
    (F₀ F₁ : A ⥤ C) [F₀.Additive] [F₁.Additive]
    (T₀ T₁ : DerivedCategory B ⥤ DerivedCategory D)
    (U₀ U₁ : DerivedCategory A ⥤ DerivedCategory C)
    (ε₀ : DerivedCategory.Q ⋙ T₀ ⟶ E₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ε₁ : DerivedCategory.Q ⋙ T₁ ⟶ E₁.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (δ₀ : DerivedCategory.Q ⋙ U₀ ⟶ F₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (δ₁ : DerivedCategory.Q ⋙ U₁ ⟶ F₁.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (good : CochainComplex A ℤ → Prop)
    (res : ∀ K, ∃ (P : CochainComplex A ℤ) (p : P ⟶ K), good P ∧ QuasiIso p)
    (hδ₁ : ∀ P, good P → IsIso (δ₁.app P))
    (η₀ : L ⋙ E₀ ≅ F₀ ⋙ N) (η₁ : L ⋙ E₁ ≅ F₁ ⋙ N)
    (ρ₀ : L.mapDerivedCategory ⋙ T₀ ≅ U₀ ⋙ N.mapDerivedCategory)
    (ρ₁ : L.mapDerivedCategory ⋙ T₁ ≅ U₁ ⋙ N.mapDerivedCategory)
    (h₀ : NormalizedExactDescent L N E₀ F₀ T₀ U₀ ε₀ δ₀ good η₀ ρ₀)
    (h₁ : NormalizedExactDescent L N E₁ F₁ T₁ U₁ ε₁ δ₁ good η₁ ρ₁)
    (a : E₀ ⟶ E₁) (b : F₀ ⟶ F₁) (t : T₀ ⟶ T₁) (u : U₀ ⟶ U₁)
    (ht : ∀ P, t.app (DerivedCategory.Q.obj P) ≫ ε₁.app P =
      ε₀.app P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex a (.up ℤ)).app P))
    (hu : ∀ P, u.app (DerivedCategory.Q.obj P) ≫ δ₁.app P =
      δ₀.app P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex b (.up ℤ)).app P))
    (hη : Functor.whiskerLeft L a ≫ η₁.hom =
      η₀.hom ≫ Functor.whiskerRight b N) :
    ∀ K, t.app (L.mapDerivedCategory.obj K) ≫ ρ₁.hom.app K =
      ρ₀.hom.app K ≫ N.mapDerivedCategory.map (u.app K) := by
  let α := Functor.whiskerLeft L.mapDerivedCategory t ≫ ρ₁.hom
  let β := ρ₀.hom ≫ Functor.whiskerRight u N.mapDerivedCategory
  let ff := cochainRepresentativeWhiskering good res (DerivedCategory D)
  have he : α = β := by
    apply ff.map_injective
    ext X
    let P := X.obj
    let LP := (L.mapHomologicalComplex (.up ℤ)).obj P
    let da := (NatTrans.mapHomologicalComplex a (.up ℤ)).app LP
    let db := (NatTrans.mapHomologicalComplex b (.up ℤ)).app P
    have := hδ₁ P X.property
    have : IsIso (N.mapDerivedCategory.map (δ₁.app P) ≫
        N.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj P)) := by
      infer_instance
    apply comparison_square
      (t.app (L.mapDerivedCategory.obj (DerivedCategory.Q.obj P)))
      (N.mapDerivedCategory.map (u.app (DerivedCategory.Q.obj P)))
      (T₀.map (L.mapDerivedCategoryFactors.hom.app P) ≫ ε₀.app LP)
      (T₁.map (L.mapDerivedCategoryFactors.hom.app P) ≫ ε₁.app LP)
      (N.mapDerivedCategory.map (δ₀.app P) ≫
        N.mapDerivedCategoryFactors.hom.app ((F₀.mapHomologicalComplex (.up ℤ)).obj P))
      (N.mapDerivedCategory.map (δ₁.app P) ≫
        N.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj P))
      (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex η₀ (.up ℤ)).hom.app P))
      (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex η₁ (.up ℤ)).hom.app P))
      (ρ₀.hom.app (DerivedCategory.Q.obj P)) (ρ₁.hom.app (DerivedCategory.Q.obj P))
      (DerivedCategory.Q.map da)
      (DerivedCategory.Q.map ((N.mapHomologicalComplex (.up ℤ)).map db))
    · simpa only [ExactDescentEquation, Category.assoc] using h₀ P X.property
    · simpa only [ExactDescentEquation, Category.assoc] using h₁ P X.property
    · erw [← Category.assoc, ← t.naturality (L.mapDerivedCategoryFactors.hom.app P),
        Category.assoc, ht]
      simp only [Category.assoc]
      rfl
    · rw [← N.mapDerivedCategory.map_comp_assoc, hu]
      simp only [N.mapDerivedCategory.map_comp, Category.assoc]
      rw [N.mapDerivedCategoryFactors_hom_naturality]
    · simp only [← DerivedCategory.Q.map_comp]
      apply DerivedCategory.Q.congr_map
      ext i
      exact NatTrans.congr_app hη (P.X i)
  intro K
  exact NatTrans.congr_app he K

attribute [local irreducible] CategoryTheory.StrictReduction.reduction in
private theorem linear_evaluation_of_models
    (g : SliceTensorGenerator.Coherence.{c, v, r} R V)
    (m : ReductionModel.{c, v, r} R)
    (mV : ReductionModel.{max c v, v, r} (R.over V))
    (S : AlgebraTowers.{c, v, r} R) (n : ℕᵒᵖ)
    (ρ : DerivedComparison.{c, v, r} R V m mV S)
    (hρ : DerivedNormalized.{c, v, r} R V m mV S (g.ordinary S) ρ)
    (e : ScalarModel.{c, v, r} R (S.obj n))
    (eV : ScalarModel.{max c v, v, r} (R.over V)
      ((S ⋙ sliceAlgebras.{c, v, r} R V).obj n)) :
    Nonempty (LinearEvaluation.{c, v, r} R V m mV S n (g.ordinary S) ρ) := by
  classical
  let SV := S ⋙ sliceAlgebras.{c, v, r} R V
  let L : Modules.{max c v, v, r} (R.over V) ⥤ Modules.{c, v, r} R :=
    localizedSystemExtension.{c, v, r} R V
  let N : (ℕᵒᵖ ⥤ Modules.{max c v, v, r} (R.over V)) ⥤
      (ℕᵒᵖ ⥤ Modules.{c, v, r} R) := towerExtension.{c, v, r} R V
  let H := evaluation.{c, v, r} R n
  let H' := evaluation.{max c v, v, r} (R.over V) n
  let U := scalars.{c, v, r} R (S.obj n)
  let U' := scalars.{max c v, v, r} (R.over V) (SV.obj n)
  let M : Modules.{max c v, v, r} (SV.obj n).right ⥤
      Modules.{c, v, r} (S.obj n).right :=
    localizedSystemExtension.{c, v, r} (S.obj n).right V
  let : N.Additive := towerExtension_additive.{c, v, r} R V
  let : PreservesFiniteLimits N := towerExtension_limits.{c, v, r} R V
  let : PreservesFiniteColimits N := towerExtension_colimits.{c, v, r} R V
  let : L.Additive := localizedSystemExtensionAdditive.{c, v, r} R V
  let : PreservesFiniteLimits L := localizedSystemExtensionLimits.{c, v, r} R V
  let : PreservesFiniteColimits L := localizedSystemExtensionColimits.{c, v, r} R V
  let : M.Additive := localizedSystemExtensionAdditive.{c, v, r} (S.obj n).right V
  let : PreservesFiniteLimits M :=
    localizedSystemExtensionLimits.{c, v, r} (S.obj n).right V
  let : PreservesFiniteColimits M :=
    localizedSystemExtensionColimits.{c, v, r} (S.obj n).right V
  let : (reduction.{max c v, v, r} (R.over V) SV).Additive :=
    reduction_additive.{max c v, v, r} (R.over V) SV
  let : e.E.Additive := e.additive
  let : eV.E.Additive := eV.additive
  let p := ordinary_evaluation R S n (g.tensorLift (S.obj n)) e
  let q := ordinary_evaluation.{max c v, v, r} (R.over V) SV n
    (g.sliceTensorLift (S.obj n)) eV
  let σ := scalar_ordinary R V g (S.obj n) e eV
  let θ := g.restrictionComparison (S.obj n)
  let κ : N ⋙ H ≅ H' ⋙ L :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  obtain ⟨pd, hpd, _⟩ := evaluated_comparison (reduction.{c, v, r} R S) e.E H U
    (m.F.obj S) e.T (m.ε S) e.ε (Resolving.{c, v, r} R)
    (CategoryTheory.StrictReduction.resolves (R := R))
    (m.computes S) (fun P hP ↦ e.computes P hP.1) p
  obtain ⟨qd, hqd, _⟩ := evaluated_comparison
    (reduction.{max c v, v, r} (R.over V) SV) eV.E H' U'
    (mV.F.obj SV) eV.T (mV.ε SV) eV.ε (Resolving.{max c v, v, r} (R.over V))
    (CategoryTheory.StrictReduction.resolves (R := R.over V))
    (mV.computes SV) (fun P hP ↦ eV.computes P hP.1) q
  set_option backward.isDefEq.respectTransparency true in
  obtain ⟨β, hβ, _⟩ := exact_comparison
    (A := Modules.{max c v, v, r} (R.over V)) (B := Modules.{c, v, r} R)
    (C := Modules.{max c v, v, r} (SV.obj n).right)
    (D := Modules.{c, v, r} (S.obj n).right) L M e.E eV.E e.T eV.T e.ε eV.ε
    (Resolving.{max c v, v, r} (R.over V))
    (CategoryTheory.StrictReduction.resolves (R := R.over V))
    (fun P hP ↦ e.computes _ (extension_resolving.{c, v, r} R V P hP).1)
    (fun P hP ↦ eV.computes P hP.1) σ
  let base : EvaluationModel.{c, v, r} R m S n :=
    { scalar := e
      ordinary := p
      ordinary_normalized := ordinary_evaluation_normalized R S n
        (g.tensorLift (S.obj n)) (g.tensorLift_normalized (S.obj n)) e
      derived := pd
      normalized := hpd }
  let slice : EvaluationModel.{max c v, v, r} (R.over V) mV SV n :=
    { scalar := eV
      ordinary := q
      ordinary_normalized := ordinary_evaluation_normalized.{max c v, v, r}
        (R.over V) SV n (g.sliceTensorLift (S.obj n))
        (g.sliceTensorLift_normalized (S.obj n)) eV
      derived := qd
      normalized := hqd }
  set_option backward.isDefEq.respectTransparency true in
  refine ⟨{ base := base
            slice := slice
            restriction := θ
            restriction_normalized := ?_
            ordinary := σ
            ordinary_square := ?_
            derived := β
            normalized := ?_
            evaluated := ?_ }⟩
  · exact g.restriction_normalized (S.obj n)
  · intro X
    exact scalar_ordinary_square R V g S n e eV X
  · exact hβ
  · set_option backward.isDefEq.respectTransparency true in
    let α := Functor.whiskerRight ρ.hom H.mapDerivedCategory ≫
      Functor.whiskerLeft (mV.F.obj SV) (exactDerivedSquare N H H' L κ).hom ≫
      Functor.whiskerRight qd.hom L.mapDerivedCategory ≫
      Functor.whiskerLeft eV.T (exactDerivedSquare U' L M U θ).hom
    let γ := Functor.whiskerLeft L.mapDerivedCategory pd.hom ≫
      Functor.whiskerRight β.hom U.mapDerivedCategory
    let ff := cochainRepresentativeWhiskering (Resolving.{max c v, v, r} (R.over V))
      (CategoryTheory.StrictReduction.resolves (R := R.over V)) (D.{c, v, r} R)
    have he : α = γ := by
      apply ff.map_injective
      ext P
      have hpa := hpd ((L.mapHomologicalComplex (.up ℤ)).obj P.obj)
        (extension_resolving.{c, v, r} R V P.obj P.property)
      have hpb := hqd P.obj P.property
      have hpc := hβ P.obj P.property
      set_option backward.isDefEq.respectTransparency true in
      refine paste_at (A := Modules.{max c v, v, r} (R.over V))
        (B := Modules.{c, v, r} R)
        (C := ℕᵒᵖ ⥤ Modules.{max c v, v, r} (R.over V))
        (D := ℕᵒᵖ ⥤ Modules.{c, v, r} R)
        (E := Modules.{max c v, v, r} (SV.obj n).right)
        (F := Modules.{c, v, r} (S.obj n).right) L N H H' M U U'
        (reduction.{c, v, r} R S) (reduction.{max c v, v, r} (R.over V) SV)
        e.E eV.E (m.F.obj S) (mV.F.obj SV) e.T eV.T
        (m.ε S) (mV.ε SV) e.ε eV.ε (g.ordinary S) p q σ κ θ ρ pd qd β
        P.obj ?_ ?_ ?_ ?_ ?_ ?_
      · exact eV.computes P.obj P.property.1
      · exact hρ P.obj P.property
      · exact hpa
      · exact hpb
      · exact hpc
      · intro K
        calc
          _ = H.map ((g.ordinary S).hom.app K) ≫
              L.map (q.hom.app K) ≫ θ.hom.app (eV.E.obj K) :=
            insert_identity _ _ _
          _ = _ := scalar_ordinary_square R V g S n e eV K
    intro K
    set_option backward.isDefEq.respectTransparency true in
    dsimp only [DerivedEvaluationSquare, base, slice]
    set_option backward.isDefEq.respectTransparency false in
    exact NatTrans.congr_app he K


private theorem linear_evaluation
    (g : SliceTensorGenerator.Coherence.{c, v, r} R V)
    (m : ReductionModel.{c, v, r} R)
    (mV : ReductionModel.{max c v, v, r} (R.over V))
    (S : AlgebraTowers.{c, v, r} R) (n : ℕᵒᵖ)
    (ρ : DerivedComparison.{c, v, r} R V m mV S)
    (hρ : DerivedNormalized.{c, v, r} R V m mV S (g.ordinary S) ρ) :
    Nonempty (LinearEvaluation.{c, v, r} R V m mV S n (g.ordinary S) ρ) := by
  obtain ⟨e⟩ : Nonempty (ScalarModel.{c, v, r} R (S.obj n)) :=
    nonempty_derivedChangeOfRingsCochainModel (S.obj n).hom
  obtain ⟨eV⟩ : Nonempty (ScalarModel.{max c v, v, r} (R.over V)
      ((S ⋙ sliceAlgebras.{c, v, r} R V).obj n)) :=
    nonempty_derivedChangeOfRingsCochainModel
      ((S ⋙ sliceAlgebras.{c, v, r} R V).obj n).hom
  exact linear_evaluation_of_models R V g m mV S n ρ hρ e eV


attribute [local irreducible] CategoryTheory.StrictReduction.reduction in
private theorem comparison_descent
    (m : ReductionModel.{c, v, r} R)
    (mV : ReductionModel.{max c v, v, r} (R.over V))
    (S : AlgebraTowers.{c, v, r} R) (η : OrdinaryComparison.{c, v, r} R V S) :
    ∃! ρ : DerivedComparison.{c, v, r} R V m mV S,
      DerivedNormalized.{c, v, r} R V m mV S η ρ := by
  let : (reduction.{max c v, v, r} (R.over V)
      (S ⋙ sliceAlgebras.{c, v, r} R V)).Additive :=
    reduction_additive.{max c v, v, r} (R.over V)
      (S ⋙ sliceAlgebras.{c, v, r} R V)
  let L : Modules.{max c v, v, r} (R.over V) ⥤ Modules.{c, v, r} R :=
    localizedSystemExtension.{c, v, r} R V
  let N : (ℕᵒᵖ ⥤ Modules.{max c v, v, r} (R.over V)) ⥤
      (ℕᵒᵖ ⥤ Modules.{c, v, r} R) := towerExtension.{c, v, r} R V
  let E : Modules.{c, v, r} R ⥤ (ℕᵒᵖ ⥤ Modules.{c, v, r} R) :=
    reduction.{c, v, r} R S
  let F : Modules.{max c v, v, r} (R.over V) ⥤
      (ℕᵒᵖ ⥤ Modules.{max c v, v, r} (R.over V)) :=
    reduction.{max c v, v, r} (R.over V) (S ⋙ sliceAlgebras.{c, v, r} R V)
  let : L.Additive := localizedSystemExtensionAdditive.{c, v, r} R V
  let : PreservesFiniteLimits L := localizedSystemExtensionLimits.{c, v, r} R V
  let : PreservesFiniteColimits L := localizedSystemExtensionColimits.{c, v, r} R V
  let : N.Additive := inferInstance
  let : PreservesFiniteLimits N := inferInstance
  let : PreservesFiniteColimits N := inferInstance
  let : E.Additive := inferInstance
  let : F.Additive := inferInstance
  set_option backward.isDefEq.respectTransparency true in
  exact exact_comparison
    (A := Modules.{max c v, v, r} (R.over V)) (B := Modules.{c, v, r} R)
    (C := ℕᵒᵖ ⥤ Modules.{max c v, v, r} (R.over V))
    (D := ℕᵒᵖ ⥤ Modules.{c, v, r} R) L N E F
    (m.F.obj S) (mV.F.obj (S ⋙ sliceAlgebras.{c, v, r} R V))
    (m.ε S) (mV.ε (S ⋙ sliceAlgebras.{c, v, r} R V))
    (Resolving.{max c v, v, r} (R.over V))
    (CategoryTheory.StrictReduction.resolves (R := R.over V))
    (fun P hP ↦ m.computes S _ (extension_resolving.{c, v, r} R V P hP))
    (fun P hP ↦ mV.computes _ P hP) η


attribute [local irreducible] CategoryTheory.StrictReduction.reduction in
private theorem derived_coefficient_natural
    (g : SliceTensorGenerator.Coherence.{c, v, r} R V)
    (m : ReductionModel.{c, v, r} R)
    (mV : ReductionModel.{max c v, v, r} (R.over V))
    (ρ : ∀ S, DerivedComparison.{c, v, r} R V m mV S)
    (hρ : ∀ S, DerivedNormalized.{c, v, r} R V m mV S (g.ordinary S) (ρ S))
    (S T : AlgebraTowers.{c, v, r} R) (a : S ⟶ T)
    (K : D.{max c v, v, r} (R.over V)) :
    (m.F.map a).app ((localizedSystemExtension.{c, v, r} R V).mapDerivedCategory.obj K) ≫
        (ρ T).hom.app K =
      (ρ S).hom.app K ≫ (towerExtension.{c, v, r} R V).mapDerivedCategory.map
        ((mV.F.map (Functor.whiskerRight a (sliceAlgebras.{c, v, r} R V))).app K) := by
  let : (reduction.{max c v, v, r} (R.over V)
      (S ⋙ sliceAlgebras.{c, v, r} R V)).Additive :=
    reduction_additive.{max c v, v, r} (R.over V)
      (S ⋙ sliceAlgebras.{c, v, r} R V)
  let : (reduction.{max c v, v, r} (R.over V)
      (T ⋙ sliceAlgebras.{c, v, r} R V)).Additive :=
    reduction_additive.{max c v, v, r} (R.over V)
      (T ⋙ sliceAlgebras.{c, v, r} R V)
  let L : Modules.{max c v, v, r} (R.over V) ⥤ Modules.{c, v, r} R :=
    localizedSystemExtension.{c, v, r} R V
  let N : (ℕᵒᵖ ⥤ Modules.{max c v, v, r} (R.over V)) ⥤
      (ℕᵒᵖ ⥤ Modules.{c, v, r} R) := towerExtension.{c, v, r} R V
  let : L.Additive := localizedSystemExtensionAdditive.{c, v, r} R V
  let : PreservesFiniteLimits L := localizedSystemExtensionLimits.{c, v, r} R V
  let : PreservesFiniteColimits L := localizedSystemExtensionColimits.{c, v, r} R V
  let : N.Additive := inferInstance
  let : PreservesFiniteLimits N := inferInstance
  let : PreservesFiniteColimits N := inferInstance
  set_option backward.isDefEq.respectTransparency true in
  refine comparison_natural
    (A := Modules.{max c v, v, r} (R.over V)) (B := Modules.{c, v, r} R)
    (C := ℕᵒᵖ ⥤ Modules.{max c v, v, r} (R.over V))
    (D := ℕᵒᵖ ⥤ Modules.{c, v, r} R) L N
    (reduction.{c, v, r} R S) (reduction.{c, v, r} R T)
    (reduction.{max c v, v, r} (R.over V) (S ⋙ sliceAlgebras.{c, v, r} R V))
    (reduction.{max c v, v, r} (R.over V) (T ⋙ sliceAlgebras.{c, v, r} R V))
    (m.F.obj S) (m.F.obj T) (mV.F.obj _) (mV.F.obj _)
    (m.ε S) (m.ε T) (mV.ε _) (mV.ε _)
    (Resolving.{max c v, v, r} (R.over V))
    (CategoryTheory.StrictReduction.resolves (R := R.over V))
    (mV.computes _) (g.ordinary S) (g.ordinary T) (ρ S) (ρ T) (hρ S) (hρ T)
    (coefficient_map.{c, v, r} R S T a)
    (coefficient_map.{max c v, v, r} (R.over V) _ _
      (Functor.whiskerRight a (sliceAlgebras.{c, v, r} R V)))
    (m.F.map a) (mV.F.map (Functor.whiskerRight a (sliceAlgebras.{c, v, r} R V)))
    ?_ ?_ ?_ K
  · exact m.coefficient S T a
  · exact mV.coefficient _ _ _
  · exact g.coefficient_natural S T a



private theorem assemble_descent
    (m : ReductionModel.{c, v, r} R)
    (mV : ReductionModel.{max c v, v, r} (R.over V))
    (g : SliceTensorGenerator.Coherence.{c, v, r} R V) :
    Nonempty (Descent.{c, v, r} R V m mV) := by
  classical
  have comparisons (S : AlgebraTowers.{c, v, r} R) :
      ∃ ρ : DerivedComparison.{c, v, r} R V m mV S,
        DerivedNormalized.{c, v, r} R V m mV S (g.ordinary S) ρ ∧
          ∀ ρ', DerivedNormalized.{c, v, r} R V m mV S (g.ordinary S) ρ' → ρ' = ρ :=
    comparison_descent R V m mV S (g.ordinary S)
  choose ρ hρ hu using comparisons
  refine ⟨{ ordinary := g.ordinary
            ordinary_normalized := g.ordinary_normalized
            derived := ρ
            normalized := hρ
            unique := ?_
            ordinary_natural := ?_
            derived_natural := ?_
            linear := ?_ }⟩
  · intro S ρ' hρ'
    exact hu S ρ' hρ'
  · exact fun S T a M ↦ NatTrans.congr_app (g.coefficient_natural S T a) M
  · exact derived_coefficient_natural R V g m mV ρ hρ
  · intro S n
    exact Classical.choice (linear_evaluation R V g m mV S n (ρ S) (hρ S))


/-- Exact localized extension commutes canonically with derived strict-tower tensor,
with its strict inverse-projection normalization, tower-map naturality, uniqueness,
and coefficient-linear evaluation. All models and comparisons are conclusions.
There is no ring-map flatness, transition-surjectivity, boundedness or completion assumption.

Source: Stacks sites-modules.tex, Tag 0E8I, lemma-j-shriek-and-tensor;
sites-cohomology.tex, Tags 06YS, 06YU; categories.tex, Tags 04VG, 04VK
(blueprint: lem-sf-cbc-localized-strict-tensor-descent).

Proof:
1. The flat-term K-flat resolving class and reductionInverts construct universal
left-derived ordinary reductions. Their coefficient maps are the universal
leftDerivedNatTrans maps, so the computation counits are coefficient-natural.
2. Exact localized extension preserves resolving complexes. On these complexes,
conjugate the ordinary generator-coherence comparison by the computing counits.
Fully faithful restriction to resolving complexes descends this comparison and
its inverse, and proves uniqueness with the required normalization.
3. The two coefficient-naturality composites agree on resolving complexes by
counit naturality and ordinary generator coherence. Faithfulness proves equality.
4. Choose the universal scalar-extension models and transport the ordinary
scalar lifts through their prescribed object equalities. The same descent gives
the evaluation and coefficient-linear comparison isomorphisms.
5. Paste the four counit equations on each resolving complex with the canonical
exact-derived-square comparisons. Cancel the invertible scalar counit; the
remaining identity is the ordinary coherence square. Faithfulness extends the
evaluated equality to every derived object. All models are conclusions, and no
coefficient flatness, transition surjectivity, boundedness or completion is used. -/
theorem localized_strict_tensor_descent :
    ∃ (m : ReductionModel.{c, v, r} R)
      (mV : ReductionModel.{max c v, v, r} (R.over V)),
      Nonempty (Descent.{c, v, r} R V m mV) := by
  classical
  obtain ⟨m⟩ := reduction_models.{c, v, r} R
  obtain ⟨mV⟩ := reduction_models.{max c v, v, r} (R.over V)
  obtain ⟨g⟩ := SliceTensorGenerator.coherence_exists.{c, v, r} R V
  exact ⟨m, mV, assemble_descent R V m mV g⟩

end SheafOfModules.LocalizedStrictTensor
