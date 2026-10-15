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
import Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts
import Sheaf.Algebra.Homology.KFlatResolutionGeneral

/-!
# The completion map in the explicit shifted-cone model

Source: Weil conjectures blueprint, proper base change, order 1258
(blueprint: def-weil-pbc-completion-map). The strict reductions use one fixed K-flat
model. The target is `Cone(1-s)[-1]`; its lift has zero homotopy component.
-/

@[expose] public section

universe t

open CategoryTheory CategoryTheory.Limits

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- The derived product exists for this countable reduction sequence.
Source: blueprint order 1258 (blueprint: def-weil-pbc-completion-map).
Proof: countableProducts_exact gives exact countable products of the module sheaves.
Apply derivedCategory_countableProducts_core with the standard localization to obtain
countable derived products, in particular the product of the specified reductions. -/
theorem adicReductionSequence_hasProduct : HasProduct (adicReductionSequence X d M) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
