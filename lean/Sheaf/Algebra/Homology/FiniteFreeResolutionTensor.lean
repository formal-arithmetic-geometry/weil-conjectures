/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Sheaf.Algebra.Homology.FiniteFreeMonoCokernelKFlat
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-! # Tensor from a specified finite free sheaf resolution

Source: Stacks, Tags 06YQ, 06YS, 06YP and 06YU; Modules on Sites, Section 03EK;
blueprint main-20261015, Local models in det-def-localizing-closure-ctf-equals-bc.
(blueprint: lem-sfb-ringed-finite-free-resolution-tensor).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal


universe u v r w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SheafOfModules.KFlatFixedTensor

namespace SheafOfModules.FiniteFreeResolution

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

private theorem coefficientSheafify : HasSheafify J AddCommGrpCat.{r} :=
  SheafOfModules.hasSheafify_coefficientUniverse (J := J)

private theorem coefficientLocalEquivalences : J.WEqualsLocallyBijective AddCommGrpCat.{r} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse (J := J)

private theorem coefficientCompose :
    J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) := by infer_instance

private theorem coefficientWeakSheafify : HasWeakSheafify J AddCommGrpCat.{r} := by
  infer_instance

private theorem coefficientMonoidal :
    (J.W.inverseImage (PresheafOfModules.toPresheaf.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj)).IsMonoidal :=
  SheafOfModules.cochainTensorLocalizationIsMonoidal R

attribute [local instance] coefficientSheafify coefficientLocalEquivalences
  coefficientCompose coefficientWeakSheafify coefficientMonoidal

/-- Finite powers are the existing categorical products, including the empty product.
Source: Stacks, Modules on Sites, Section 03EK
(blueprint: lem-sfb-ringed-finite-free-resolution-tensor). -/
abbrev power (F : Modules R) (n : ℕ) := ∏ᶜ (fun _ : Fin n ↦ F)

/-- The existing single complex in degree zero.
Source: Stacks, Homology, Definition 0115
(blueprint: lem-sfb-ringed-finite-free-resolution-tensor). -/
abbrev single (F : Modules R) :=
  (HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).obj F

/-- Coordinate contraction: project the free factor and use the ordinary right unitor.
It sends z tensor (b_j) to (b_j z); no choice of a tensor comparison is made.
Source: Stacks, Modules on Sites, Section 03EK
(blueprint: lem-sfb-ringed-finite-free-resolution-tensor). -/
def coordinateMap (N : Modules R) (n : ℕ) :
    N ⊗ power R (𝟙_ (Modules R)) n ⟶ power R N n :=
  Pi.lift (fun j ↦ (N ◁ Pi.π (fun _ : Fin n ↦ 𝟙_ (Modules R)) j) ≫ (ρ_ N).hom)

/-- The explicit finite-sum inverse to coordinate contraction.
It sends (z_j) to the sum of z_j tensor e_j.
Source: Stacks, Modules on Sites, Section 03EK
(blueprint: lem-sfb-ringed-finite-free-resolution-tensor). -/
def coordinateInverse (N : Modules R) (n : ℕ) :
    power R N n ⟶ N ⊗ power R (𝟙_ (Modules R)) n :=
  ∑ j : Fin n, Pi.π (fun _ : Fin n ↦ N) j ≫ (ρ_ N).inv ≫
    (N ◁ Pi.ι (fun _ : Fin n ↦ 𝟙_ (Modules R)) j)

private theorem pi_total (F : Modules R) (n : ℕ) :
    ∑ j : Fin n, Pi.π (fun _ : Fin n ↦ F) j ≫ Pi.ι (fun _ : Fin n ↦ F) j =
      𝟙 (power R F n) := by
  classical
  apply Pi.hom_ext
  intro k
  rw [Preadditive.sum_comp, Finset.sum_eq_single k]
  · simp only [Category.assoc, Pi.ι_π_eq_id, Category.comp_id, Category.id_comp]
  · intro j _ hj
    simp only [Category.assoc, Pi.ι_π_of_ne _ hj, comp_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

private def coordinateIso (N : Modules R) (n : ℕ) :
    N ⊗ power R (𝟙_ (Modules R)) n ≅ power R N n where
  hom := coordinateMap R N n
  inv := coordinateInverse R N n
  hom_inv_id := by
    classical
    simp only [coordinateMap, coordinateInverse, Preadditive.comp_sum,
      ← Category.assoc, Pi.lift_π]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    simp only [← whiskerLeft_comp, ← whiskerLeft_sum, pi_total, whiskerLeft_id]
  inv_hom_id := by
    classical
    apply Pi.hom_ext
    intro k
    simp only [coordinateInverse, coordinateMap, Preadditive.sum_comp,
      Category.assoc, Pi.lift_π]
    rw [Finset.sum_eq_single k]
    · simp only [← whiskerLeft_comp_assoc, Pi.ι_π_eq_id, whiskerLeft_id,
        Category.id_comp, Iso.inv_hom_id, Category.comp_id]
    · intro j hj hne
      simp only [← whiskerLeft_comp_assoc, Pi.ι_π_of_ne _ hne,
        MonoidalPreadditive.whiskerLeft_zero, zero_comp, comp_zero]
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

private theorem finiteFree_flat (F : Modules R) (n : ℕ)
    (e : F ≅ power R (𝟙_ (Modules R)) n) : IsFlatOnSite (J := J) (R := R) F := by
  have : HasFiniteBiproducts (Modules R) := Abelian.hasFiniteBiproducts
  let := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
  let eSum : F ≅ ∐ (fun _ : Fin n ↦ 𝟙_ (Modules R)) :=
    e ≪≫ (biproduct.isoProduct _).symm ≪≫ biproduct.isoCoproduct _
  have hunit : ObjectProperty.flat (𝟙_ (Modules R)) := ObjectProperty.prop_unit _
  have hf : ObjectProperty.flat F :=
    (ObjectProperty.flat.prop_iff_of_iso eSum).2
      (flat_finite_coproduct _ (fun _ ↦ hunit))
  exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R F).symm hf.2

private theorem single_flat (F : Modules R)
    (hF : IsFlatOnSite (J := J) (R := R) F) (i : ℤ) :
    IsFlatOnSite (J := J) (R := R) ((single R F).X i) := by
  have hcat := SheafOfModules.flat_to_cat R F hF
  have hs : ObjectProperty.flat ((single R F).X i) := by
    by_cases hi : i = 0
    · subst i
      exact (ObjectProperty.flat.prop_iff_of_iso
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 F)).2 hcat
    · exact ObjectProperty.flat_of_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 F i hi)
  exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R _).symm hs.2

private abbrev baseRing :=
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R

private abbrev Sections := RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)

private def scalar (F : Modules R) (s : Sections R) : F ⟶ F :=
  ⟨PresheafOfModules.sectionsSMul F.val s⟩

private theorem scalar_naturality {F G : Modules R} (f : F ⟶ G) (s : Sections R) :
    scalar R F s ≫ f = f ≫ scalar R G s := by
  exact SheafOfModules.hom_ext (PresheafOfModules.sectionsSMul_naturality f.val s).symm

private theorem sheafify_scalar
    (P : PresheafOfModules.{r} (baseRing R).obj) (s : Sections R) :
    (PresheafOfModules.sheafification (𝟙 (baseRing R).obj)).map
      (PresheafOfModules.sectionsSMul P s) =
    scalar R ((PresheafOfModules.sheafification (𝟙 (baseRing R).obj)).obj P) s := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (baseRing R).obj)
  apply (adj.homEquiv P _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact (adj.unit.naturality (PresheafOfModules.sectionsSMul P s)).symm.trans
    (PresheafOfModules.sectionsSMul_naturality (adj.unit.app P) s).symm

private theorem tensorSheafification_naturality (A : Modules R)
    {F G : Modules R} (f : F ⟶ G) :
    A ◁ f ≫ (tensorObjIsoSheafification A G).hom =
      (tensorObjIsoSheafification A F).hom ≫
        (PresheafOfModules.sheafification (𝟙 (baseRing R).obj)).map (A.val ◁ f.val) := by
  have h := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (baseRing R).obj)).counit.naturality f
  dsimp at h
  simp only [tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom, tensorIso_inv,
    Iso.app_inv, asIso_inv, Functor.Monoidal.μIso_hom, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural_right]
  simp only [← Category.assoc]
  congr 1
  rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  congr 1
  simp only [NatIso.isIso_inv_app, IsIso.eq_inv_comp]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

private theorem tensor_scalar (N F : Modules R) (s : Sections R) :
    N ◁ scalar R F s = scalar R (N ⊗ F) s := by
  let e := tensorObjIsoSheafification N F
  apply (cancel_mono e.hom).1
  change N ◁ scalar R F s ≫ (tensorObjIsoSheafification N F).hom = _
  rw [tensorSheafification_naturality]
  have hp : N.val ◁ (scalar R F s).val =
      PresheafOfModules.sectionsSMul (N.val ⊗ F.val) s := by
    ext U x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      change x ⊗ₜ[R.obj.obj U] (s.1 U • y) =
        (show R.obj.obj U from s.1 U) • (x ⊗ₜ[R.obj.obj U] y)
      dsimp [CommRingCat.forgetToRingCat_obj]
      exact TensorProduct.tmul_smul (R := R.obj.obj U) (R' := R.obj.obj U)
        (show R.obj.obj U from s.1 U) x y
  rw [hp, sheafify_scalar]
  exact (scalar_naturality R e.hom s).symm

set_option allowUnsafeReducibility true in
attribute [local semireducible] SheafOfModules.monoidalCategory

private theorem unit_action (N : Modules R)
    (f : 𝟙_ (Modules R) ⟶ 𝟙_ (Modules R)) (U : Cᵒᵖ) (z : N.val.obj U) :
    (((ρ_ N).inv ≫ (N ◁ f) ≫ (ρ_ N).hom).val.app U) z =
      (f.val.app U (1 : R.obj.obj U)) • z := by
  let s : Sections R := ⟨fun V ↦ f.val.app V (1 : R.obj.obj V), by
    intro V W g
    have h := PresheafOfModules.naturality_apply f.val g (1 : R.obj.obj V)
    change f.val.app W ((R.obj.map g).hom 1) =
      (R.obj.map g).hom (f.val.app V (1 : R.obj.obj V)) at h
    change (R.obj.map g).hom (f.val.app V (1 : R.obj.obj V)) =
      f.val.app W (1 : R.obj.obj W)
    rw [← h, map_one]⟩
  have hf : f = scalar R (𝟙_ (Modules R)) s := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let x' : R.obj.obj V := x
    have h := (f.val.app V).hom.map_smul x' (1 : R.obj.obj V)
    change (show R.obj.obj V from
      f.val.app V (show R.obj.obj V from x' * (1 : R.obj.obj V))) =
        (show R.obj.obj V from x' * (show R.obj.obj V from
          f.val.app V (1 : R.obj.obj V))) at h
    change (show R.obj.obj V from f.val.app V x') =
      (show R.obj.obj V from (show R.obj.obj V from f.val.app V (1 : R.obj.obj V)) * x')
    simpa only [mul_one, mul_comm] using h
  have h : (ρ_ N).inv ≫ (N ◁ f) ≫ (ρ_ N).hom = scalar R N s := by
    rw [hf, tensor_scalar, scalar_naturality, Iso.inv_hom_id_assoc]
  rw [h]
  rfl

private theorem tensor_matrix (N : Modules R) (m n : ℕ)
    (f : power R (𝟙_ (Modules R)) m ⟶ power R (𝟙_ (Modules R)) n)
    (U : Cᵒᵖ) (a : Fin n → Fin m → R.obj.obj U)
    (ha : ∀ (x : (power R (𝟙_ (Modules R)) m).val.obj U) (k : Fin n),
      (Pi.π (fun _ : Fin n ↦ 𝟙_ (Modules R)) k).val.app U (f.val.app U x) =
        ∑ j : Fin m, a k j •
          (Pi.π (fun _ : Fin m ↦ 𝟙_ (Modules R)) j).val.app U x)
    (z : (power R N m).val.obj U) (k : Fin n) :
    (Pi.π (fun _ : Fin n ↦ N) k).val.app U
      ((coordinateInverse R N m ≫ (N ◁ f) ≫ coordinateMap R N n).val.app U z) =
        ∑ j : Fin m, a k j • (Pi.π (fun _ : Fin m ↦ N) j).val.app U z := by
  classical
  let entry (j : Fin m) : 𝟙_ (Modules R) ⟶ 𝟙_ (Modules R) :=
    Pi.ι (fun _ : Fin m ↦ 𝟙_ (Modules R)) j ≫ f ≫
      Pi.π (fun _ : Fin n ↦ 𝟙_ (Modules R)) k
  have hentry (j : Fin m) : (entry j).val.app U (1 : R.obj.obj U) = a k j := by
    have h := ha ((Pi.ι (fun _ : Fin m ↦ 𝟙_ (Modules R)) j).val.app U (1 : R.obj.obj U)) k
    change (entry j).val.app U (1 : R.obj.obj U) = _ at h
    rw [h]
    have hc (l : Fin m) :
        (Pi.π (fun _ : Fin m ↦ 𝟙_ (Modules R)) l).val.app U
          ((Pi.ι (fun _ : Fin m ↦ 𝟙_ (Modules R)) j).val.app U (1 : R.obj.obj U)) =
            if j = l then (1 : R.obj.obj U) else 0 := by
      change ((Pi.ι (fun _ : Fin m ↦ 𝟙_ (Modules R)) j ≫
        Pi.π (fun _ : Fin m ↦ 𝟙_ (Modules R)) l).val.app U) (1 : R.obj.obj U) = _
      by_cases h : j = l
      · subst l
        simp only [Pi.ι_π_eq_id, id_val, PresheafOfModules.id_app, ModuleCat.id_apply,
          if_true]
      · rw [Pi.ι_π_of_ne _ h, if_neg h]
        rfl
    simp [hc, smul_eq_mul]
  have hm :
      (coordinateInverse R N m ≫ (N ◁ f) ≫ coordinateMap R N n) ≫
          Pi.π (fun _ : Fin n ↦ N) k =
        ∑ j : Fin m, Pi.π (fun _ : Fin m ↦ N) j ≫ (ρ_ N).inv ≫
          (N ◁ entry j) ≫ (ρ_ N).hom := by
    simp only [coordinateInverse, coordinateMap, Preadditive.sum_comp,
      Category.assoc, Pi.lift_π, ← whiskerLeft_comp_assoc, entry]
  change (((coordinateInverse R N m ≫ (N ◁ f) ≫ coordinateMap R N n) ≫
    Pi.π (fun _ : Fin n ↦ N) k).val.app U) z = _
  rw [hm]
  have hsum (t : Fin m → (power R N m ⟶ N)) :
      (∑ j : Fin m, t j).val.app U z = ∑ j : Fin m, (t j).val.app U z := by
    exact map_sum (AddMonoidHom.mk' (fun t : power R N m ⟶ N ↦ t.val.app U z)
      (by intros; rfl)) _ _
  rw [hsum]
  apply Finset.sum_congr rfl
  intro j hj
  change (((ρ_ N).inv ≫ (N ◁ entry j) ≫ (ρ_ N).hom).val.app U)
    ((Pi.π (fun _ : Fin m ↦ N) j).val.app U z) = _
  rw [unit_action, hentry]

attribute [local irreducible] SheafOfModules.monoidalCategory

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option allowUnsafeReducibility true in
attribute [local semireducible] ordinaryTensor
attribute [local instance 2000] tensorAdditive tensorObjAdditive tensorHasMapBifunctor

private theorem genericCollapseLeft
    {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D]
    (F : D ⥤ D ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    (N : D) (K : CochainComplex D ℤ) (i : ℤ) :
    CochainComplex.ιMapBifunctor
        ((HomologicalComplex.single D (.up ℤ) 0).obj N) K F 0 i i (zero_add i) ≫
      (CochainComplex.mapBifunctorSingle₁Iso F N K).hom.f i =
        (F.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).hom).app (K.X i) := by
  simp only [CochainComplex.mapBifunctorSingle₁Iso, HomologicalComplex.Hom.isoOfComponents,
    CochainComplex.mapBifunctorSingle₁XIso, ComplexShape.π_def,
    HomologicalComplex.singleObjXSelf, Iso.symm_mk, HomologicalComplex.ι_mapBifunctorDesc,
    and_self, ↓reduceDIte, eqToHom_refl, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

private noncomputable def genericTransportIso
    {D E : Type*} [Category* D] [Category* E] [Preadditive D] [Preadditive E]
    (F : D ⥤ E) [F.Additive] (K : CochainComplex D ℤ) (A : ℤ → E)
    (g : ∀ i : ℤ, F.obj (K.X i) ≅ A i)
    (sq : ∀ i : ℤ,
      ((g i).inv ≫ F.map (K.d i (i + 1)) ≫ (g (i + 1)).hom) ≫
        ((g (i + 1)).inv ≫ F.map (K.d (i + 1) (i + 1 + 1)) ≫
          (g (i + 1 + 1)).hom) = 0) :
    (F.mapHomologicalComplex (.up ℤ)).obj K ≅
      CochainComplex.of A
        (fun i ↦ (g i).inv ≫ F.map (K.d i (i + 1)) ≫ (g (i + 1)).hom) sq :=
  HomologicalComplex.Hom.isoOfComponents g (by
    intro i j hij
    obtain rfl : j = i + 1 := hij.symm
    change (g i).hom ≫ CochainComplex.of.d A
      (fun j ↦ (g j).inv ≫ F.map (K.d j (j + 1)) ≫ (g (j + 1)).hom) i (i + 1) =
        F.map (K.d i (i + 1)) ≫ (g (i + 1)).hom
    rw [CochainComplex.of_d]
    simp only [Iso.hom_inv_id_assoc])

private theorem genericSignedInterchange
    {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D]
    [MonoidalCategory D] [MonoidalPreadditive D] [BraidedCategory D]
    [∀ X Y : GradedObject ℤ D, X.HasTensor Y]
    [∀ X Y Z : GradedObject ℤ D, GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ X Y Z : GradedObject ℤ D, GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)] :
    ∃ sigma : ∀ P L : CochainComplex D ℤ,
        (((curriedTensor D).map₂CochainComplex).obj P).obj L ≅
          (((curriedTensor D).map₂CochainComplex).obj L).obj P,
      (∀ (P L : CochainComplex D ℤ) (p q : ℤ),
        CochainComplex.ιMapBifunctor P L (curriedTensor D) p q (p + q) rfl ≫
            (sigma P L).hom.f (p + q) =
          (p * q).negOnePow • ((β_ (P.X p) (L.X q)).hom ≫
            CochainComplex.ιMapBifunctor L P (curriedTensor D) q p (p + q)
              (add_comm q p))) ∧
      (∀ (P P' L L' : CochainComplex D ℤ) (f : P ⟶ P') (g : L ⟶ L'),
        HomologicalComplex.mapBifunctorMap f g (curriedTensor D) (ComplexShape.up ℤ) ≫
            (sigma P' L').hom =
          (sigma P L).hom ≫
            HomologicalComplex.mapBifunctorMap g f (curriedTensor D) (ComplexShape.up ℤ)) := by
  refine ⟨fun P L ↦ CochainComplex.Monoidal.braiding P L, ?_, ?_⟩
  · intro P L p q
    exact CochainComplex.Monoidal.ι_braiding_hom p q (p + q) rfl
  · intro P P' L L' f g
    change HomologicalComplex.tensorHom f g ≫ _ =
      _ ≫ HomologicalComplex.tensorHom g f
    exact BraidedCategory.braiding_naturality f g


/-- Signed interchange on arbitrary resolving complexes, before localization.
Source: Stacks, following Definition 06YU, and blueprint Local models
(blueprint: lem-sfb-ringed-finite-free-resolution-tensor).

Proof (step 4 of the node): on the (p,q) summand use (-1)^(pq) times sheaf
symmetry from lem-pc-sheaf-modules-tensor-closed. The two coefficients in the
chain equation are (-1)^(pq+q) and (-1)^(pq), using the differential of
 def-pc-tensor-complex-sheaves. Swapping twice gives (-1)^(2pq)=1. The summand
formulas commute with cochain maps and induce maps on the direct sums. This
applies in particular to the resolving representatives used by the derived tensor.
-/
theorem signedInterchange :
    ∃ sigma : ∀ P L : CochainComplex (Modules R) ℤ,
        ((totalTensor R).obj P).obj L ≅ ((totalTensor R).obj L).obj P,
      (∀ (P L : CochainComplex (Modules R) ℤ) (p q : ℤ),
        CochainComplex.ιMapBifunctor P L (ordinaryTensor R) p q (p + q) rfl ≫
            (sigma P L).hom.f (p + q) =
          (p * q).negOnePow • ((β_ (P.X p) (L.X q)).hom ≫
            CochainComplex.ιMapBifunctor L P (ordinaryTensor R) q p (p + q)
              (add_comm q p))) ∧
      (∀ (P P' L L' : CochainComplex (Modules R) ℤ) (f : P ⟶ P') (g : L ⟶ L'),
        HomologicalComplex.mapBifunctorMap f g (ordinaryTensor R) (ComplexShape.up ℤ) ≫
            (sigma P' L').hom =
          (sigma P L).hom ≫
            HomologicalComplex.mapBifunctorMap g f (ordinaryTensor R) (ComplexShape.up ℤ)) := by
  unfold totalTensor ordinaryTensor
  exact genericSignedInterchange (D := Modules R)

attribute [local instance 2000] tensorAdditive tensorObjAdditive tensorHasMapBifunctor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable [HasDerivedCategory.{w} (Modules R)]

set_option allowUnsafeReducibility true in
attribute [local irreducible] derivedTensor representativeIso

/-- The specified finite free resolution computes the ordinary unbounded derived tensor,
with its actual differential and the comparison induced by the given augmentation.
The coordinate equations specify both directions, and the summand equation specifies
signed interchange. The final sectionwise clause includes locally specified matrices,
since it is quantified over every site object U. The last two clauses record the
support of the two-term case and the degree-zero complex, with the same differential.

Source: Stacks, Tags 06YQ, 06YS, 06YP, 06YU and Modules on Sites, Section 03EK;
blueprint main-20261015, det-def-localizing-closure-ctf-equals-bc, Local models
(blueprint: lem-sfb-ringed-finite-free-resolution-tensor).

Proof plan:
1. The coordinateMap is induced by balanced tensor maps on sections, via
   def-weil-presheaf-modules-sheafification and def-pur-sheaf-tensor-product.
   Its inverse is coordinateInverse: the composites are the identity by expanding
   the finite sum in the standard basis, also for rank zero.
2. Finite powers preserve kernels and cokernels in the abelian module-sheaf category
   def-weil-sheaf-of-modules-category. Thus the coordinate comparison identifies
   tensoring with each K.X i with an exact functor, giving def-pc-flat-sheaf-modules.
3. Apply lem-weil-pbc-independent-bounded-flat-kflat at the supplied upper bound.
   Essential smallness is relative to the common coefficient universe; no points enter.
4. Sheaf tensor symmetry (lem-pc-sheaf-modules-tensor-closed), multiplied by
   (-1)^(pq) on the (p,q) summand of def-pc-tensor-complex-sheaves, is a cochain
   isomorphism: the two differential coefficients are (-1)^(pq+q) and (-1)^(pq).
   Its square is the identity, and its construction commutes with all cochain maps.
5. lem-weil-pbc-kflat-fixed-tensor-triangulated gives the natural comparison c,
   normalized by lem-weil-pbc-site-derived-tensor-descent on resolving complexes.
   Invert Q epsilon using def-weil-abstract-derived-category. Compose its tensor,
   c inverse, signed interchange, and the localized coordinate cochain isomorphism.
6. In Tot(N[0] tensor K) only (0,i) survives in degree i. Its differential is
   1 tensor d_K. Conjugating by gamma gives delta and delta squared is zero.
   Expand a section in its finite coordinates to obtain the stated matrix formula.
   This computation commutes with restriction and does not assume N flat.
7. Zero ranks give zero terms. For support in {-1,0} this is precisely the two-term
   complex; for support in {0} the identity in degree zero gives the single complex.
-/
theorem finiteFreeResolution_tensor
    (K : CochainComplex (Modules R) ℤ) (b : ℤ)
    (hbound : ∀ i : ℤ, b < i → IsZero (K.X i))
    (rank : ℤ → ℕ) (hrank : ∀ i : ℤ, b < i → rank i = 0)
    (theta : ∀ i : ℤ, K.X i ≅ power R (𝟙_ (Modules R)) (rank i)) :
    ∃ hflat : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (K.X i),
    ∃ hK : K.IsKFlatIndependentCoefficients,
    ∃ c : (totalTensor R).obj K ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ (derivedTensor R).obj (DerivedCategory.Q.obj K),
      (∀ (L : CochainComplex (Modules R) ℤ)
        (hL : L.IsKFlatIndependentCoefficients)
        (hLf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (L.X i)),
        c.app L = representativeIso R K L hK hL hflat hLf) ∧
      ∀ (M : Modules R) (epsilon : K ⟶ single R M) [QuasiIso epsilon] (N : Modules R),
      ∃ gamma : ∀ i : ℤ, N ⊗ K.X i ≅ power R N (rank i),
      ∃ delta : ∀ i : ℤ, power R N (rank i) ⟶ power R N (rank (i + 1)),
      ∃ sq : ∀ i : ℤ, delta i ≫ delta (i + 1) = 0,
      ∃ tau : ((totalTensor R).obj (single R N)).obj K ≅
          CochainComplex.of (fun i ↦ power R N (rank i)) delta sq,
      ∃ sigma : ((totalTensor R).obj K).obj (single R N) ≅
          ((totalTensor R).obj (single R N)).obj K,
      ∃ comparison : ((derivedTensor R).obj (DerivedCategory.Q.obj (single R M))).obj
          (DerivedCategory.Q.obj (single R N)) ≅
          DerivedCategory.Q.obj
            (CochainComplex.of (fun i ↦ power R N (rank i)) delta sq),
        (∀ i : ℤ,
          (gamma i).hom = (N ◁ (theta i).hom) ≫ coordinateMap R N (rank i) ∧
          (gamma i).inv = coordinateInverse R N (rank i) ≫ (N ◁ (theta i).inv)) ∧
        (∀ i : ℤ, delta i =
          (gamma i).inv ≫ (N ◁ K.d i (i + 1)) ≫ (gamma (i + 1)).hom) ∧
        (∀ i : ℤ,
          CochainComplex.ιMapBifunctor (single R N) K (ordinaryTensor R) 0 i i
              (zero_add i) ≫ tau.hom.f i =
            ((ordinaryTensor R).map
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).hom).app
                (K.X i) ≫ (gamma i).hom) ∧
        (∀ p q : ℤ,
          CochainComplex.ιMapBifunctor K (single R N) (ordinaryTensor R) p q (p + q)
              rfl ≫ sigma.hom.f (p + q) =
            (p * q).negOnePow • ((β_ (K.X p) ((single R N).X q)).hom ≫
              CochainComplex.ιMapBifunctor (single R N) K (ordinaryTensor R) q p (p + q)
                (add_comm q p))) ∧
        comparison =
          (((derivedTensor R).mapIso (asIso (DerivedCategory.Q.map epsilon))).app
            (DerivedCategory.Q.obj (single R N))).symm ≪≫
          (c.app (single R N)).symm ≪≫ DerivedCategory.Q.mapIso sigma ≪≫
          DerivedCategory.Q.mapIso tau ∧
        (∀ (i : ℤ) (U : Cᵒᵖ)
          (a : Fin (rank (i + 1)) → Fin (rank i) → R.obj.obj U),
          (∀ (x : (power R (𝟙_ (Modules R)) (rank i)).val.obj U)
              (k : Fin (rank (i + 1))),
            (Pi.π (fun _ : Fin (rank (i + 1)) ↦ 𝟙_ (Modules R)) k).val.app U
                (((theta i).inv ≫ K.d i (i + 1) ≫ (theta (i + 1)).hom).val.app U x) =
              ∑ j : Fin (rank i), a k j •
                (Pi.π (fun _ : Fin (rank i) ↦ 𝟙_ (Modules R)) j).val.app U x) →
          ∀ (z : (power R N (rank i)).val.obj U) (k : Fin (rank (i + 1))),
            (Pi.π (fun _ : Fin (rank (i + 1)) ↦ N) k).val.app U
                ((delta i).val.app U z) =
              ∑ j : Fin (rank i), a k j •
                (Pi.π (fun _ : Fin (rank i) ↦ N) j).val.app U z) ∧
        ((∀ i : ℤ, i ≠ -1 → i ≠ 0 → rank i = 0) →
          ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
            IsZero ((CochainComplex.of (fun j ↦ power R N (rank j)) delta sq).X i)) ∧
        ((∀ i : ℤ, i ≠ 0 → rank i = 0) →
          ∃ e : CochainComplex.of (fun i ↦ power R N (rank i)) delta sq ≅
              single R (power R N (rank 0)),
            e.hom.f 0 =
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
                (power R N (rank 0))).inv) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    classical
    have _ := hrank
    have hf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (K.X i) :=
      fun i ↦ finiteFree_flat R _ _ (theta i)
    have : K.IsStrictlyLE b := (K.isStrictlyLE_iff b).2 hbound
    have hk := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
      R K b hf
    obtain ⟨s, hs⟩ := kFlat_fixed_tensor_triangulated R
    obtain ⟨c, _, hc⟩ := (hs K hk hf).2.2.2.1
    refine ⟨hf, hk, c, hc, ?_⟩
    intro M epsilon hqi N
    let H := (ordinaryTensor R).obj N
    let gamma (i : ℤ) : N ⊗ K.X i ≅ power R N (rank i) :=
      H.mapIso (theta i) ≪≫ coordinateIso R N (rank i)
    let delta (i : ℤ) := (gamma i).inv ≫ (N ◁ K.d i (i + 1)) ≫ (gamma (i + 1)).hom
    have sq (i : ℤ) : delta i ≫ delta (i + 1) = 0 := by
      change ((gamma i).inv ≫ (N ◁ K.d i (i + 1)) ≫ (gamma (i + 1)).hom) ≫
        ((gamma (i + 1)).inv ≫ (N ◁ K.d (i + 1) (i + 1 + 1)) ≫
          (gamma (i + 1 + 1)).hom) = 0
      simp only [Category.assoc, Iso.hom_inv_id_assoc, ← whiskerLeft_comp_assoc,
        K.d_comp_d, MonoidalPreadditive.whiskerLeft_zero, zero_comp, comp_zero]
    let T := CochainComplex.of (fun i ↦ power R N (rank i)) delta sq
    let t : (H.mapHomologicalComplex (.up ℤ)).obj K ≅ T :=
      genericTransportIso H K (fun i ↦ power R N (rank i)) gamma sq
    let tau : ((totalTensor R).obj (single R N)).obj K ≅ T :=
      CochainComplex.mapBifunctorSingle₁Iso (ordinaryTensor R) N K ≪≫ t
    obtain ⟨sigmaAll, hsigma, _⟩ := signedInterchange R
    let sigma := sigmaAll K (single R N)
    let comparison :=
      (((derivedTensor R).mapIso (asIso (DerivedCategory.Q.map epsilon))).app
        (DerivedCategory.Q.obj (single R N))).symm ≪≫
      (c.app (single R N)).symm ≪≫ DerivedCategory.Q.mapIso sigma ≪≫
      DerivedCategory.Q.mapIso tau
    refine ⟨gamma, delta, sq, tau, sigma, comparison, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · intro i
      exact ⟨rfl, rfl⟩
    · intro i
      rfl
    · intro i
      change CochainComplex.ιMapBifunctor (single R N) K (ordinaryTensor R) 0 i i
        (zero_add i) ≫
          (CochainComplex.mapBifunctorSingle₁Iso (ordinaryTensor R) N K).hom.f i ≫
            (gamma i).hom = _
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun f ↦ f ≫ (gamma i).hom)
          (genericCollapseLeft (ordinaryTensor R) N K i))
    · exact hsigma K (single R N)
    · intro i U a ha z k
      have hd : delta i = coordinateInverse R N (rank i) ≫
          (N ◁ ((theta i).inv ≫ K.d i (i + 1) ≫ (theta (i + 1)).hom)) ≫
            coordinateMap R N (rank (i + 1)) := by
        change (coordinateInverse R N (rank i) ≫ (N ◁ (theta i).inv)) ≫
          (N ◁ K.d i (i + 1)) ≫
            ((N ◁ (theta (i + 1)).hom) ≫ coordinateMap R N (rank (i + 1))) = _
        simp only [Category.assoc, whiskerLeft_comp]
      rw [hd]
      exact tensor_matrix R N _ _ _ U a ha z k
    · intro hr i hi hi'
      change IsZero (power R N (rank i))
      rw [hr i hi hi']
      apply (IsZero.iff_id_eq_zero _).2
      apply Pi.hom_ext
      intro j
      exact Fin.elim0 j
    · intro hr
      have hz (i : ℤ) (hi : i ≠ 0) : IsZero (T.X i) := by
        change IsZero (power R N (rank i))
        rw [hr i hi]
        apply (IsZero.iff_id_eq_zero _).2
        apply Pi.hom_ext
        intro j
        exact Fin.elim0 j
      let e : T ≅ single R (power R N (rank 0)) :=
        HomologicalComplex.Hom.isoOfComponents (fun i ↦
          if hi : i = 0 then by
            subst i
            exact (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).symm
          else (hz i hi).iso (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ i hi))
          (by
            intro i j hij
            by_cases hi : i = 0
            · apply (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ j
                (by change i + 1 = j at hij; omega)).eq_of_tgt
            · apply (hz i hi).eq_of_src)
      refine ⟨e, ?_⟩
      rfl

/-- A specified short exact finite free presentation gives the augmentation of its
actual two-term complex, represented by the standard cone of f[0]. The equality
on the cone inclusion says that its degree-zero component is the specified g.
Source: Stacks, Homology, Definition 0115; blueprint Local models
(blueprint: lem-sfb-ringed-finite-free-resolution-tensor).

Proof (step 7 of the node): f followed by g is zero by exactness, hence g[0]
extends to the cone augmentation with zero shifted-source component. Its cohomology
is ker f in degree -1, coker f in degree 0, and zero elsewhere. Short exactness
makes the former zero and identifies the latter with M by g. Thus the augmentation
is a quasi-isomorphism by def-pc-quasi-iso-modules, and finiteFreeResolution_tensor
applies with the specified f and identity coordinates, including rank zero.
-/
theorem shortExact_finiteFree_augmentation
    (m n : ℕ) (M : Modules R)
    (f : power R (𝟙_ (Modules R)) m ⟶ power R (𝟙_ (Modules R)) n)
    (g : power R (𝟙_ (Modules R)) n ⟶ M) (hfg : f ≫ g = 0)
    (h : (ShortComplex.mk f g hfg).ShortExact) :
    ∃ epsilon : CochainComplex.mappingCone
        ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map f) ⟶
          single R M,
      CochainComplex.mappingCone.inr
          ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map f) ≫
            epsilon =
        (HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map g ∧
      QuasiIso epsilon ∧
      ∀ N : Modules R,
        Nonempty
          (((derivedTensor R).obj (DerivedCategory.Q.obj (single R M))).obj
              (DerivedCategory.Q.obj (single R N)) ≅
            DerivedCategory.Q.obj (CochainComplex.mappingCone
              ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map
                (coordinateInverse R N m ≫ (N ◁ f) ≫ coordinateMap R N n)))) := by
  classical
  have : HasFiniteBiproducts (Modules R) := Abelian.hasFiniteBiproducts
  let S := ShortComplex.mk f g hfg
  have : Mono S.f := h.mono_f
  let eUnit : 𝟙_ (Modules R) ≅ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) := by
    with_unfolding_all exact Iso.refl _
  let eSum (k : ℕ) : power R (𝟙_ (Modules R)) k ≅ ∐ (fun _ : Fin k ↦
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) :=
    (Pi.mapIso (fun _ ↦ eUnit)) ≪≫
      (biproduct.isoProduct _).symm ≪≫ biproduct.isoCoproduct _
  obtain ⟨hqi, hf, _, _, hk, _, _, _, hinr, _⟩ :=
    CochainComplex.finite_free_mono_cokernel_kflat R S h.gIsCokernel m n
      (eSum m) (eSum n)
  refine ⟨CochainComplex.monoCokernelAugmentation S, hinr, hqi, fun N ↦ ?_⟩
  have : QuasiIso (CochainComplex.monoCokernelAugmentation S) := hqi
  let K := CochainComplex.monoCokernelComplex f
  obtain ⟨s, hs⟩ := kFlat_fixed_tensor_triangulated R
  obtain ⟨c, _, _⟩ := (hs K hk hf).2.2.2.1
  let H := (ordinaryTensor R).obj N
  let singleF := HomologicalComplex.single (Modules R) (.up ℤ) 0
  let d := coordinateInverse R N m ≫ (N ◁ f) ≫ coordinateMap R N n
  let tm := (HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).app
      (power R (𝟙_ (Modules R)) m) ≪≫ singleF.mapIso (coordinateIso R N m)
  let tn := (HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).app
      (power R (𝟙_ (Modules R)) n) ≪≫ singleF.mapIso (coordinateIso R N n)
  let a : Arrow.mk ((H.mapHomologicalComplex (.up ℤ)).map (singleF.map f)) ≅
      Arrow.mk (singleF.map d) := Arrow.isoMk tm tn (by
    change ((HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).hom.app _ ≫
      singleF.map (coordinateMap R N m)) ≫ singleF.map d = _
    rw [Category.assoc, ← singleF.map_comp]
    have he : coordinateMap R N m ≫ d = H.map f ≫ coordinateMap R N n := by
      dsimp [d, H]
      have hi : coordinateMap R N m ≫ coordinateInverse R N m = 𝟙 _ :=
        (coordinateIso R N m).hom_inv_id
      rw [← Category.assoc, ← Category.assoc, hi]
      simp only [Category.id_comp]
      rfl
    rw [he, singleF.map_comp, ← Category.assoc]
    exact congrArg (fun t ↦ t ≫ singleF.map (coordinateMap R N n))
      ((HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).hom.naturality f).symm)
  obtain ⟨sigmaAll, _, _⟩ := signedInterchange R
  let t : ((totalTensor R).obj K).obj (single R N) ≅
      CochainComplex.mappingCone (singleF.map d) :=
    sigmaAll K (single R N) ≪≫
      CochainComplex.mapBifunctorSingle₁Iso (ordinaryTensor R) N K ≪≫
      CochainComplex.mappingCone.mapHomologicalComplexIso (singleF.map f) H ≪≫
      HomologicalComplex.homotopyCofiber.mapArrowIso _ _
        (fun j ↦ ⟨j - 1, by change j - 1 + 1 = j; omega⟩) a
  exact ⟨(((derivedTensor R).mapIso
      (asIso (DerivedCategory.Q.map (CochainComplex.monoCokernelAugmentation S)))).app
        (DerivedCategory.Q.obj (single R N))).symm ≪≫
    (c.app (single R N)).symm ≪≫ DerivedCategory.Q.mapIso t⟩

/-- A specified finite free isomorphism gives its specified degree-zero augmentation.
Source: Stacks, Homology, Definition 0115; blueprint Local models
(blueprint: lem-sfb-ringed-finite-free-resolution-tensor).

Proof (step 7 of the node): applying the single-complex functor to the supplied
isomorphism gives a cochain isomorphism and hence a quasi-isomorphism. The general
formula then has support {0}, and is N^r[0], including r=0.
-/
theorem finiteFree_iso_augmentation (n : ℕ) (M : Modules R)
    (e : power R (𝟙_ (Modules R)) n ≅ M) :
    QuasiIso ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).map e.hom) ∧
      ∀ N : Modules R,
        Nonempty
          (((derivedTensor R).obj (DerivedCategory.Q.obj (single R M))).obj
              (DerivedCategory.Q.obj (single R N)) ≅
            DerivedCategory.Q.obj (single R (power R N n))) := by
  have hqi : QuasiIso
      ((HomologicalComplex.single (Modules R) (.up ℤ) 0).map e.hom) := by
    infer_instance
  refine ⟨hqi, fun N ↦ ?_⟩
  let P : CochainComplex (Modules R) ℤ := single R (power R (𝟙_ (Modules R)) n)
  have hf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i) :=
    single_flat R _ (finiteFree_flat R _ n (Iso.refl _))
  have hk : P.IsKFlatIndependentCoefficients :=
    SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R P 0 hf
  obtain ⟨s, hs⟩ := kFlat_fixed_tensor_triangulated R
  obtain ⟨c, _, _⟩ := (hs P hk hf).2.2.2.1
  let se := (HomologicalComplex.single (Modules R) (.up ℤ) 0).mapIso e
  obtain ⟨sigmaAll, _, _⟩ := signedInterchange R
  let t : ((totalTensor R).obj P).obj (single R N) ≅ single R (power R N n) :=
    sigmaAll P (single R N) ≪≫
      CochainComplex.mapBifunctorSingle₁Iso (ordinaryTensor R) N P ≪≫
      (HomologicalComplex.singleMapHomologicalComplex ((ordinaryTensor R).obj N)
        (.up ℤ) 0).app _ ≪≫
      (HomologicalComplex.single (Modules R) (.up ℤ) 0).mapIso (coordinateIso R N n)
  exact ⟨(((derivedTensor R).mapIso (DerivedCategory.Q.mapIso se)).app
      (DerivedCategory.Q.obj (single R N))).symm ≪≫
    (c.app (single R N)).symm ≪≫ DerivedCategory.Q.mapIso t⟩

end SheafOfModules.FiniteFreeResolution
