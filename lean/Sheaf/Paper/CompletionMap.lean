/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.AdicDerivedInverseLimit
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

/-!
# The completion map in the explicit shifted-cone model

Source: Weil conjectures blueprint, proper base change, order 1258
(blueprint: def-weil-pbc-completion-map). The strict reductions use one fixed K-flat
model. The target is `Cone(1-s)[-1]`; its lift has zero homotopy component.
-/

@[expose] public section

universe t

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
variable (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
variable (M : AdicKFlatModel X Λ K)

/-- The strict reduction complex at positive level n+1, with Λ scalars retained.
Source: blueprint order 1258, strict tower (blueprint: def-weil-pbc-completion-map). -/
noncomputable abbrev adicReductionComplex (n : ℕ) :=
  adicRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
    (adicChange X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) M.complex)

/-- The strict quotient transition on the fixed model.
Source: blueprint order 1258, strict tower (blueprint: def-weil-pbc-completion-map). -/
noncomputable def adicReductionComplexStep (n : ℕ) :
    adicReductionComplex X d M (n + 1) ⟶ adicReductionComplex X d M n :=
  adicTransitionComplex X d.ideal M.complex
    ⟨(n + 1) + 1, Nat.succ_pos (n + 1)⟩ ⟨n + 1, Nat.succ_pos n⟩
    (Nat.le_succ (n + 1))

set_option backward.isDefEq.respectTransparency false in
/-- The quotient augmentation is uniquely determined by m ↦ 1 tensor m on local sections.
Source: blueprint order 1258, formula a_n (blueprint: def-weil-pbc-completion-map).
Proof: the unit of extension/restriction of scalars has this formula. Its compatibility
with restrictions and differentials follows from naturality of the tensor unit; these
sectionwise formulas also give uniqueness. -/
theorem adicReductionAugmentation_exists (n : ℕ) :
    ∃! f : M.complex ⟶ adicReductionComplex X d M n,
      ∀ (p : ℤ) (U : X.ProEtᵒᵖ) (m : (M.complex.X p).val.obj U),
        (f.f p).val.app U m =
          adicTensorSection X (Ideal.Quotient.mk (d.ideal ^ (n + 1))) _ U 1 m := by
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{t + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{t, 0} X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} X
  let φ := Ideal.Quotient.mk (d.ideal ^ (n + 1))
  let α := adicConstantMap X φ
  let η (p : ℤ) := (PresheafOfModules.sheafificationAdjunction.{t + 1}
    (𝟙 (adicModuleRing X (Λ ⧸ d.ideal ^ (n + 1))).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} α (M.complex.X p))
  let a (p : ℤ) : M.complex.X p ⟶ (adicReductionComplex X d M n).X p :=
    { val :=
      { app := fun U ↦
          (ModuleCat.extendRestrictScalarsAdj.{t + 1, t + 1, t + 1} (α.hom.app U).hom).unit.app
            ((M.complex.X p).val.obj U) ≫
          (ModuleCat.restrictScalars (α.hom.app U).hom).map ((η p).app U)
        naturality := by
          intro U V i
          ext m
          have h := PresheafOfModules.naturality_apply (η p) i
            ((1 : (adicConstantRing X (Λ ⧸ d.ideal ^ (n + 1))).obj.obj U)
              ⊗ₜ[(adicConstantRing X Λ).obj.obj U, (α.hom.app U).hom] m)
          change (η p).app V
            (SheafOfModules.changeOfRingsMap α (M.complex.X p) i _) = _ at h
          change (η p).app V _ = _
          rw [show SheafOfModules.changeOfRingsMap α (M.complex.X p) i _ = _ from
            Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap
              α (M.complex.X p) i) 1 m, map_one] at h
          exact h }
    }
  have ha (p : ℤ) (U : X.ProEtᵒᵖ) (m : (M.complex.X p).val.obj U) :
      (a p).val.app U m = adicTensorSection X φ _ U 1 m := rfl
  let f : M.complex ⟶ adicReductionComplex X d M n :=
    { f := a
      comm' := by
        intro i j hij
        ext U m
        let b : SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1}
            α (M.complex.X i) ⟶
            SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} α (M.complex.X j) :=
          { app := fun U ↦ (ModuleCat.extendScalars (α.hom.app U).hom).map
              ((M.complex.d i j).val.app U)
            naturality := SheafOfModules.changeOfRingsHom_naturality α _ (M.complex.d i j) }
        have hn := congrArg (fun q ↦ q.app U
          ((1 : (adicConstantRing X (Λ ⧸ d.ideal ^ (n + 1))).obj.obj U)
            ⊗ₜ[(adicConstantRing X Λ).obj.obj U, (α.hom.app U).hom] m))
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 (adicModuleRing X (Λ ⧸ d.ideal ^ (n + 1))).obj)).unit.naturality b)
        change (η j).app U (b.app U _) = _ at hn
        erw [ModuleCat.ExtendScalars.map_tmul] at hn
        exact hn.symm }
  refine ⟨f, ?_, ?_⟩
  · exact ha
  · intro g hg
    apply HomologicalComplex.hom_ext
    intro p
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext m
    exact (hg p U m).trans (ha p U m).symm

/-- The actual quotient chain map, selected by its unique local formula.
Source: blueprint order 1258, a_n (blueprint: def-weil-pbc-completion-map). -/
noncomputable def adicReductionAugmentation (n : ℕ) :
    M.complex ⟶ adicReductionComplex X d M n :=
  Classical.choose (adicReductionAugmentation_exists X d M n)

/-- Quotient augmentations commute strictly with the quotient transitions.
Source: blueprint order 1258 (blueprint: def-weil-pbc-completion-map).
Proof: the transition sends 1 tensor m to 1 tensor m, since the quotient ring map
preserves one. The local formulas for the augmentations then identify the chain maps. -/
theorem adicReductionAugmentation_step (n : ℕ) :
    adicReductionAugmentation X d M (n + 1) ≫ adicReductionComplexStep X d M n =
      adicReductionAugmentation X d M n := by
  apply (Classical.choose_spec (adicReductionAugmentation_exists X d M n)).2
  intro p U m
  change ((adicReductionComplexStep X d M n).f p).val.app U
    (((adicReductionAugmentation X d M (n + 1)).f p).val.app U m) = _
  change ((adicReductionComplexStep X d M n).f p).val.app U
    (((Classical.choose (adicReductionAugmentation_exists X d M (n + 1))).f p).val.app U m) = _
  erw [(Classical.choose_spec (adicReductionAugmentation_exists X d M (n + 1))).1]
  change ((adicTransitionComplex X d.ideal M.complex _ _ _).f p).val.app U _ = _
  erw [(Classical.choose_spec (adicTransitionComplex_exists X d.ideal M.complex
    ⟨(n + 1) + 1, Nat.succ_pos (n + 1)⟩ ⟨n + 1, Nat.succ_pos n⟩
    (Nat.le_succ (n + 1)))).1]
  congr 1
  exact map_one ((adicConstantMap X
    (adicQuotientMap d.ideal (n + 1 + 1) (n + 1) (Nat.le_succ (n + 1)))).hom.app U).hom

/-- Finite biproducts used in the cone, with their usual product construction.
Source: blueprint order 1258, cone terms (blueprint: def-weil-pbc-completion-map). -/
noncomputable instance adicCompletionFiniteBiproducts :
    HasFiniteBiproducts (SheafOfModules.{t + 1} (adicModuleRing X Λ)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The termwise product complex B.
Source: blueprint order 1258 (blueprint: def-weil-pbc-completion-map). -/
noncomputable abbrev adicReductionProduct := ∏ᶜ (adicReductionComplex X d M)

/-- The product shift, whose n-th coordinate is the next projection then transition.
Source: blueprint order 1258 (blueprint: def-weil-pbc-completion-map). -/
noncomputable def adicReductionProductShift :
    adicReductionProduct X d M ⟶ adicReductionProduct X d M :=
  towerProductShift (adicReductionComplexStep X d M)

/-- The compatible augmentation a : F → B.
Source: blueprint order 1258 (blueprint: def-weil-pbc-completion-map). -/
noncomputable def adicReductionProductAugmentation : M.complex ⟶ adicReductionProduct X d M :=
  Pi.lift (adicReductionAugmentation X d M)

/-- The explicit shifted cone; mappingCocone is definitionally Cone(1-s)[-1].
Its terms are B^(j-1) ⊕ B^j, with differential (-d y -(1-s)x, d x), after
exchanging the two summands of Mathlib's cone convention.
Source: blueprint order 1258 (blueprint: def-weil-pbc-completion-map). -/
noncomputable def adicCompletionComplex :=
  CochainComplex.mappingCocone (𝟙 _ - adicReductionProductShift X d M)

/-- The zero homotopy is the required cocycle relation for the explicit cone lift.
Source: blueprint order 1258, (1-s)a=0 (blueprint: def-weil-pbc-completion-map).
Proof: project to each factor. Strict compatibility of the augmentations gives a-sa=0;
the differential of the zero cochain is zero. Product extensionality gives the relation. -/
theorem adicCompletionLift_relation :
    CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain M.complex (adicReductionProduct X d M) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (adicReductionProductAugmentation X d M ≫
          (𝟙 _ - adicReductionProductShift X d M)) = 0 := by
  have h : adicReductionProductAugmentation X d M ≫
      (𝟙 _ - adicReductionProductShift X d M) = 0 := by
    apply Pi.hom_ext
    intro n
    simp [adicReductionProductAugmentation, adicReductionProductShift,
      towerProductShift, Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc,
      adicReductionAugmentation_step]
  simp [h]

/-- The chain map j=(0,a), with the zero component specified, rather than an arbitrary lift.
Source: blueprint order 1258 (blueprint: def-weil-pbc-completion-map). -/
noncomputable def adicCompletionChainMap : M.complex ⟶ adicCompletionComplex X d M :=
  CochainComplex.mappingCocone.lift _ (adicReductionProductAugmentation X d M) 0
    (adicCompletionLift_relation X d M)

/-- The derived completion target is the localization of the displayed cone complex.
Source: blueprint order 1258 (blueprint: def-weil-pbc-completion-map). -/
noncomputable def adicCompletionObject : proEtaleDerivedCategory X Λ :=
  (adicLocalization X Λ).obj (adicCompletionComplex X d M)

/-- Completion is Q(j) after the inverse of the chosen K-flat realization e.
Source: blueprint order 1258, comp_K (blueprint: def-weil-pbc-completion-map). -/
noncomputable def adicCompletionMap (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) : K ⟶ adicCompletionObject X d M :=
  M.realization.inv ≫ (adicLocalization X Λ).map (adicCompletionChainMap X d M)

/-- Projection from the shifted cone onto the product of reductions.
Source: blueprint order 1258 (blueprint: def-weil-pbc-completion-map). -/
noncomputable def adicCompletionProjection :
    adicCompletionComplex X d M ⟶ adicReductionProduct X d M :=
  CochainComplex.mappingCocone.fst _

/-- The cone lift projects to precisely each quotient arrow.
Source: blueprint order 1258 (blueprint: def-weil-pbc-completion-map).
Proof: mappingCocone.lift_fst identifies the product projection of the lift with a;
then Pi.lift_π identifies its n-th component with a_n. Apply Q and compose with e⁻¹. -/
theorem adicCompletionMap_projection (n : ℕ) :
    adicCompletionMap X d M ≫ (adicLocalization X Λ).map
        (adicCompletionProjection X d M ≫ Pi.π (adicReductionComplex X d M) n) =
      M.realization.inv ≫ (adicLocalization X Λ).map
        (adicReductionAugmentation X d M n) := by
  unfold adicCompletionMap
  rw [Category.assoc, ← Functor.map_comp]
  congr 2
  simp [adicCompletionChainMap, adicCompletionProjection,
    adicReductionProductAugmentation]

-- Translate the stated epi-product property into the exactness class used by the derived API.
private theorem adicCompletion_countableAB4Star :
    CountableAB4Star (SheafOfModules.{t + 1} (adicModuleRing X Λ)) := by
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{t + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{t, 0} X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} X
  have : HasCountableProducts (SheafOfModules.{t + 1} (adicModuleRing X Λ)) :=
    (ProEt.countableProducts_exact.{t, t, 0} X (adicConstantRing X Λ)).1
  have : (lim (J := Discrete ℕ)
      (C := SheafOfModules.{t + 1} (adicModuleRing X Λ))).PreservesEpimorphisms :=
    { preserves := by
        intro F G f hf
        have h := (ProEt.countableProducts_exact.{t, t, 0} X (adicConstantRing X Λ)).2.2
          ℕ (fun n ↦ F.obj ⟨n⟩) (fun n ↦ G.obj ⟨n⟩)
          (fun n ↦ f.app ⟨n⟩) (fun n ↦ inferInstance)
        have he : lim.map f = (Pi.isoLimit _).inv ≫
            Limits.Pi.map (fun n ↦ f.app ⟨n⟩) ≫ (Pi.isoLimit _).hom := by
          apply limit.hom_ext
          intro ⟨n⟩
          simp
        rw [he]
        infer_instance }
  have := hasExactLimitsOfShape_of_preservesEpi
    (SheafOfModules.{t + 1} (adicModuleRing X Λ)) (Discrete ℕ)
  exact CountableAB4Star.of_hasExactLimitsOfShape_nat _

/-- The derived product exists for this countable reduction sequence.
Source: blueprint order 1258 (blueprint: def-weil-pbc-completion-map).
Proof: countableProducts_exact gives exact countable products of the module sheaves.
Apply derivedCategory_countableProducts_core with the standard localization to obtain
countable derived products, in particular the product of the specified reductions. -/
theorem adicReductionSequence_hasProduct : HasProduct (adicReductionSequence X d M) := by
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{t + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{t, 0} X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} X
  have : HasCountableProducts (SheafOfModules.{t + 1} (adicModuleRing X Λ)) :=
    (ProEt.countableProducts_exact.{t, t, 0} X (adicConstantRing X Λ)).1
  let := HasDerivedCategory.standard (SheafOfModules.{t + 1} (adicModuleRing X Λ))
  have := adicCompletion_countableAB4Star X (Λ := Λ)
  let := (derivedCategory_countableProducts_core.{0, t + 2, t + 1, t + 2}
    (SheafOfModules.{t + 1} (adicModuleRing X Λ))).choose
  exact inferInstance

/-- Canonical comparison from the localized termwise product to the derived product.
Source: blueprint order 1258 (blueprint: def-weil-pbc-completion-map). -/
noncomputable def adicCompletionProductComparison [HasProduct (adicReductionSequence X d M)] :
    (adicLocalization X Λ).obj (adicReductionProduct X d M) ⟶
      ∏ᶜ (adicReductionSequence X d M) :=
  Pi.lift (fun n ↦ (adicLocalization X Λ).map (Pi.π (adicReductionComplex X d M) n))

/-- The comparison is invertible: Q(B) is the derived product, with its given projections.
Source: blueprint order 1258 (blueprint: def-weil-pbc-completion-map).
Proof: exact countable products are supplied by countableProducts_exact. The limiting-cone
clause of derivedCategory_countableProducts_core says the localized termwise product cone
is limiting. The unique comparison between it and the chosen product cone is invertible. -/
theorem adicCompletionProductComparison_isIso [HasProduct (adicReductionSequence X d M)] :
    IsIso (adicCompletionProductComparison X d M) := by
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{t + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{t, 0} X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} X
  let := HasDerivedCategory.standard (SheafOfModules.{t + 1} (adicModuleRing X Λ))
  have := adicCompletion_countableAB4Star X (Λ := Λ)
  have h := (derivedCategory_countableProducts_core.{0, t + 2, t + 1, t + 2}
    (SheafOfModules.{t + 1} (adicModuleRing X Λ))).choose_spec.1
    ℕ (adicReductionComplex X d M)
  apply (Fan.nonempty_isLimit_iff_isIso_piLift (f := adicReductionSequence X d M)
    (Fan.mk _ (fun n ↦ (adicLocalization X Λ).map
      (Pi.π (adicReductionComplex X d M) n)))).mp
  let h' := (IsLimit.postcomposeHomEquiv
    (Discrete.compNatIsoDiscrete (adicReductionComplex X d M) DerivedCategory.Q) _).symm h.some
  refine ⟨IsLimit.ofIsoLimit h' (Fan.ext (Iso.refl _) ?_)⟩
  intro n
  change DerivedCategory.Q.map
    (limit.π (Discrete.functor (adicReductionComplex X d M)) (Discrete.mk n)) ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The canonical product comparison as an isomorphism.
Source: blueprint order 1258 (blueprint: def-weil-pbc-completion-map). -/
noncomputable def adicCompletionProductIso [HasProduct (adicReductionSequence X d M)] :
    (adicLocalization X Λ).obj (adicReductionProduct X d M) ≅
      ∏ᶜ (adicReductionSequence X d M) :=
  letI := adicCompletionProductComparison_isIso X d M
  asIso (adicCompletionProductComparison X d M)

/-- The named localization is the standard derived localization and commutes with shifts.
Source: blueprint order 1258, Q and shift convention
(blueprint: def-weil-pbc-completion-map). -/
noncomputable instance adicCompletionLocalizationCommShift :
    (adicLocalization X Λ).CommShift ℤ :=
  inferInstanceAs ((@DerivedCategory.Q
    (SheafOfModules.{t + 1} (adicModuleRing X Λ)) _ _
      (HasDerivedCategory.standard _)).CommShift ℤ)

/-- The boundary is the cone-triangle boundary, transported by the product comparison.
Source: blueprint order 1258, chosen cone triple
(blueprint: def-weil-pbc-completion-map). -/
noncomputable def adicCompletionBoundary [HasProduct (adicReductionSequence X d M)] :
    ∏ᶜ (adicReductionSequence X d M) ⟶ (adicCompletionObject X d M)⟦(1 : ℤ)⟧ :=
  (adicCompletionProductIso X d M).inv ≫
    ((adicLocalization X Λ).mapTriangle.obj
      (CochainComplex.mappingCocone.triangle (𝟙 _ - adicReductionProductShift X d M))).mor₃

/-- This particular cone, projection and boundary form the adic derived-limit triangle.
Source: blueprint order 1258 (blueprint: def-weil-pbc-completion-map).
Proof: the mapping-cocone triangle is distinguished after localization. The product
comparison intertwines the middle arrow with 1 minus the derived tower shift, by checking
all projections. Transport the localized triangle through this comparison, using its
inverse for the boundary. Distinguished triangles are invariant under isomorphism. -/
theorem adicCompletion_distinguished [HasProduct (adicReductionSequence X d M)] :
    IsDerivedLimitTriangle (adicReductionStep X d M) (adicCompletionObject X d M)
      ((adicLocalization X Λ).map (adicCompletionProjection X d M) ≫
        (adicCompletionProductIso X d M).hom) (adicCompletionBoundary X d M) := by
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{t + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{t, 0} X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} X
  have : (adicLocalization X Λ).Additive :=
    inferInstanceAs ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).Additive)
  let Q := adicLocalization X Λ
  let e := adicCompletionProductIso X d M
  have he (n : ℕ) : e.hom ≫ Pi.π (adicReductionSequence X d M) n =
      Q.map (Pi.π (adicReductionComplex X d M) n) := by
    exact Pi.lift_π _ _
  have ht (n : ℕ) : adicReductionStep X d M n =
      Q.map (adicReductionComplexStep X d M n) := rfl
  have hmid : Q.map (𝟙 _ - adicReductionProductShift X d M) ≫ e.hom =
      e.hom ≫ towerTransitionEndomorphism (adicReductionStep X d M) := by
    apply Pi.hom_ext
    intro n
    calc
      (Q.map (𝟙 _ - adicReductionProductShift X d M) ≫ e.hom) ≫
          Pi.π (adicReductionSequence X d M) n =
        Q.map ((𝟙 _ - adicReductionProductShift X d M) ≫
          Pi.π (adicReductionComplex X d M) n) := by
        rw [Category.assoc, he, Functor.map_comp]
      _ = Q.map (Pi.π (adicReductionComplex X d M) n) -
          Q.map (Pi.π (adicReductionComplex X d M) (n + 1)) ≫
            Q.map (adicReductionComplexStep X d M n) := by
        simp only [adicReductionProductShift, towerProductShift, Preadditive.sub_comp,
          Category.id_comp, Pi.lift_π, Functor.map_sub, Functor.map_comp]
      _ = (e.hom ≫ towerTransitionEndomorphism (adicReductionStep X d M)) ≫
          Pi.π (adicReductionSequence X d M) n := by
        rw [Category.assoc, (towerTransitionEndomorphism_eq_iff
          (adicReductionStep X d M) _).mp rfl n]
        rw [Preadditive.comp_sub, ← Category.assoc, he, he, ht]
  let T : Pretriangulated.Triangle (proEtaleDerivedCategory X Λ) := Q.mapTriangle.obj
    (CochainComplex.mappingCocone.triangle (𝟙 _ - adicReductionProductShift X d M))
  let T' : Pretriangulated.Triangle (proEtaleDerivedCategory X Λ) :=
    Pretriangulated.Triangle.mk
      (Q.map (adicCompletionProjection X d M) ≫ e.hom)
      (towerTransitionEndomorphism (adicReductionStep X d M)) (adicCompletionBoundary X d M)
  have hT : T ∈ distTriang _ :=
    @DerivedCategory.mappingCocone_triangle_distinguished _ _ _
      (HasDerivedCategory.standard _) _ _ (𝟙 _ - adicReductionProductShift X d M)
  have hE : T ≅ T' := Pretriangulated.Triangle.isoMk T T' (Iso.refl _) e e
    (by
      change (Q.map (adicCompletionProjection X d M) ≫ e.hom) =
        𝟙 _ ≫ (Q.map (adicCompletionProjection X d M) ≫ e.hom)
      exact (Category.id_comp _).symm) hmid
    (by
      change T.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map (𝟙 _) =
        e.hom ≫ (e.inv ≫ T.mor₃)
      rw [(shiftFunctor (proEtaleDerivedCategory X Λ) (1 : ℤ)).map_id T.obj₁,
        Category.comp_id]
      exact (Iso.hom_inv_id_assoc e T.mor₃).symm)
  exact Pretriangulated.isomorphic_distinguished T hT T' hE.symm

/-- The specific adic derived-limit triple furnished by the cone model.
Source: blueprint order 1258 (blueprint: def-weil-pbc-completion-map). -/
noncomputable def adicCompletionLimit [HasProduct (adicReductionSequence X d M)] :
    AdicDerivedInverseLimit X d M where
  obj := adicCompletionObject X d M
  p := (adicLocalization X Λ).map (adicCompletionProjection X d M) ≫
    (adicCompletionProductIso X d M).hom
  δ := adicCompletionBoundary X d M
  distinguished := adicCompletion_distinguished X d M

variable {L : proEtaleDerivedCategory X Λ} (N : AdicKFlatModel X Λ L)

-- Shift the strict mapping-cone map and characterize it by both cocone coordinates.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mappingCoconeMap_exists
    {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
    {A B A' B' : CochainComplex C ℤ} (φ : A ⟶ B) (ψ : A' ⟶ B')
    (a : A ⟶ A') (b : B ⟶ B') (h : φ ≫ b = a ≫ ψ) :
    ∃! f : CochainComplex.mappingCocone φ ⟶ CochainComplex.mappingCocone ψ,
      f ≫ CochainComplex.mappingCocone.fst ψ = CochainComplex.mappingCocone.fst φ ≫ a ∧
      ∀ p : ℤ, f.f p ≫ (CochainComplex.mappingCocone.snd ψ).v p (p + -1) rfl =
        (CochainComplex.mappingCocone.snd φ).v p (p + -1) rfl ≫ b.f (p + -1) := by
  let c := CochainComplex.mappingCone.map φ ψ a b h
  let f : CochainComplex.mappingCocone φ ⟶ CochainComplex.mappingCocone ψ :=
    (shiftFunctor _ (-1 : ℤ)).map c
  have hc₁ (p : ℤ) : c.f (p + -1) ≫
      (CochainComplex.mappingCone.fst ψ).1.v (p + -1) p (by omega) =
      (CochainComplex.mappingCone.fst φ).1.v (p + -1) p (by omega) ≫ a.f p := by
    simp [c, CochainComplex.mappingCone.ext_from_iff φ p (p + -1) (by omega),
      CochainComplex.mappingCone.map]
  have hc₂ (p : ℤ) : c.f (p + -1) ≫
      (CochainComplex.mappingCone.snd ψ).v (p + -1) (p + -1) (add_zero _) =
      (CochainComplex.mappingCone.snd φ).v (p + -1) (p + -1) (add_zero _) ≫
        b.f (p + -1) := by
    simp [c, CochainComplex.mappingCone.ext_from_iff φ p (p + -1) (by omega),
      CochainComplex.mappingCone.map]
  have hf₁ : f ≫ CochainComplex.mappingCocone.fst ψ =
      CochainComplex.mappingCocone.fst φ ≫ a := by
    apply HomologicalComplex.hom_ext
    intro p
    simpa [f, CochainComplex.mappingCocone.fst,
      CochainComplex.HomComplex.Cochain.leftShift_v
        (CochainComplex.mappingCone.fst ψ).1 (-1) 0 (by omega) p p
        (add_zero p) (p + -1) (by omega),
      CochainComplex.HomComplex.Cochain.leftShift_v
        (CochainComplex.mappingCone.fst φ).1 (-1) 0 (by omega) p p
        (add_zero p) (p + -1) (by omega)] using hc₁ p
  have hf₂ (p : ℤ) : f.f p ≫ (CochainComplex.mappingCocone.snd ψ).v p (p + -1) rfl =
      (CochainComplex.mappingCocone.snd φ).v p (p + -1) rfl ≫ b.f (p + -1) := by
    simpa [f, CochainComplex.mappingCocone.snd,
      CochainComplex.HomComplex.Cochain.leftShift_v
        (CochainComplex.mappingCone.snd ψ) (-1) (-1) (by omega)
        p (p + -1) rfl (p + -1) (by omega),
      CochainComplex.HomComplex.Cochain.leftShift_v
        (CochainComplex.mappingCone.snd φ) (-1) (-1) (by omega)
        p (p + -1) rfl (p + -1) (by omega),
      Int.negOnePow_even 2 ⟨1, rfl⟩] using hc₂ p
  refine ⟨f, ⟨hf₁, hf₂⟩, ?_⟩
  intro f' hf'
  apply HomologicalComplex.hom_ext
  intro p
  have h₁ : f'.f p ≫ (CochainComplex.mappingCocone.fst ψ).f p =
      f.f p ≫ (CochainComplex.mappingCocone.fst ψ).f p :=
    congrArg (fun q ↦ q.f p) (hf'.1.trans hf₁.symm)
  have h₂ := (hf'.2 p).trans (hf₂ p).symm
  have hi := CochainComplex.mappingCocone.id_X ψ p (p + -1) rfl
  calc
    f'.f p = f'.f p ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = f'.f p ≫
        ((CochainComplex.mappingCocone.fst ψ).f p ≫
          (CochainComplex.mappingCocone.inl ψ).v p p (add_zero p) +
        (CochainComplex.mappingCocone.snd ψ).v p (p + -1) rfl ≫
          (CochainComplex.mappingCocone.inr ψ).1.v (p + -1) p (by omega)) := by rw [hi]
    _ = f.f p ≫
        ((CochainComplex.mappingCocone.fst ψ).f p ≫
          (CochainComplex.mappingCocone.inl ψ).v p p (add_zero p) +
        (CochainComplex.mappingCocone.snd ψ).v p (p + -1) rfl ≫
          (CochainComplex.mappingCocone.inr ψ).1.v (p + -1) p (by omega)) := by
      simp only [Preadditive.comp_add, ← Category.assoc]
      rw [h₁, h₂]
    _ = f.f p := by rw [hi, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- A strict tower map induces the uniquely specified map with the product map in both
cone coordinates. The first equation gives the x coordinate; the second gives y.
Source: blueprint order 1258, final sentence (blueprint: def-weil-pbc-completion-map).
Proof: compatibility with the transitions makes the product map commute with 1-s.
Apply this map to both coordinates in each degree. The cone differential formula then
proves the chain-map condition. Its two projections determine each component uniquely. -/
theorem adicCompletionTowerMap_exists
    (τ : ∀ n : ℕ, adicReductionComplex X d M n ⟶ adicReductionComplex X d N n)
    (hτ : ∀ n : ℕ, τ (n + 1) ≫ adicReductionComplexStep X d N n =
      adicReductionComplexStep X d M n ≫ τ n) :
    ∃! f : adicCompletionComplex X d M ⟶ adicCompletionComplex X d N,
      f ≫ adicCompletionProjection X d N =
          adicCompletionProjection X d M ≫ Limits.Pi.map τ ∧
      ∀ p : ℤ, f.f p ≫
          (CochainComplex.mappingCocone.snd
            (𝟙 _ - adicReductionProductShift X d N)).v p (p + -1) rfl =
        (CochainComplex.mappingCocone.snd
          (𝟙 _ - adicReductionProductShift X d M)).v p (p + -1) rfl ≫
            (Limits.Pi.map τ).f (p + -1) := by
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{t + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{t, 0} X
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} X
  exact mappingCoconeMap_exists _ _ (Limits.Pi.map τ) (Limits.Pi.map τ)
    (towerTransitionEndomorphism_natural_backward
      (adicReductionComplexStep X d M) (adicReductionComplexStep X d N) τ hτ).symm

/-- The action of a strict map of reduction towers on the explicit completion model.
Its data are fixed by the two coordinate formulas, not by an arbitrary triangle lift.
Source: blueprint order 1258, final sentence (blueprint: def-weil-pbc-completion-map). -/
noncomputable def adicCompletionTowerMap
    (τ : ∀ n : ℕ, adicReductionComplex X d M n ⟶ adicReductionComplex X d N n)
    (hτ : ∀ n : ℕ, τ (n + 1) ≫ adicReductionComplexStep X d N n =
      adicReductionComplexStep X d M n ≫ τ n) :
    adicCompletionComplex X d M ⟶ adicCompletionComplex X d N :=
  Classical.choose (adicCompletionTowerMap_exists X d M N τ hτ)

end AlgebraicGeometry.Scheme
