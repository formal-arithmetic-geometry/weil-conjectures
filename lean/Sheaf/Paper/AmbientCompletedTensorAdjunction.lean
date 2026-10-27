/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q59 and C6
-/
module

public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.RoosIntrinsicCompletenessEquivalence
public import Mathlib.Algebra.Homology.Functor
import all Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.Paper.SfDerivedCompleteLegacyComparison
import Mathlib.Data.Nat.Prime.Infinite
import Sheaf.Paper.PrincipalKoszulStrictReplacement
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Paper.IntegralCompletionUnitInverted
import Sheaf.Paper.NormalizedFiniteTensorComparison
import Sheaf.Paper.QuotientTotalTensorTowerComparison
import all Sheaf.Paper.IntegralTensorTransitionCompatibility

/-! # Quotient-completed tensor and maps into locally complete targets

Source: Stacks Project, proetale.tex, Tag 099M and the preceding completed-coefficient
comparison; algebraization.tex, Tags 0999, 099B and 0A0E
(blueprint: lem-sf-ambient-completed-tensor-adjunction).

The strict tower lives in the derived category of the abelian category of towers.
The finite-level formula fixes the comparison, including its quotient transitions.
Index n denotes exponent n+1. No boundedness or finite Tor amplitude is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u t
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open CategoryTheory.ConstantCompletion
attribute [local irreducible] CategoryTheory.ConstantCompletion.completed
  CategoryTheory.ConstantCompletion.quotientPresentation HasDerivedCategory.standard
  SheafOfModules.monoidalCategory CategoryTheory.ConstantCompletion.rlim

namespace CategoryTheory.AmbientCompletedTensor

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type u) [CommRing A] (I : Ideal A)

/-- The standard derived localization of module sheaves on this small site.
Source: Stacks 05RU (blueprint: lem-sf-ambient-completed-tensor-adjunction). -/
instance moduleDerived (O : Sheaf J CommRingCat.{u}) :
    HasDerivedCategory.{u + 1} (Mod O) := HasDerivedCategory.standard _

/-- The two separately reduced complexes, tensored over their actual quotient ring
and then restricted to the completed coefficients. Source: Stacks 099M, 07A4
(blueprint: lem-sf-ambient-completed-tensor-adjunction). -/
def finiteTensor (n : ℕ) : Cx (completed J A I) × Cx (completed J A I) ⥤
    Cx (completed J A I) :=
  ((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).prod
      ((change (projection J A I n)).mapHomologicalComplex (.up ℤ)) ⋙
    coefficientTotalTensor.{u, u, u} J (finite J A I n) ⋙
      (res (projection J A I n)).mapHomologicalComplex (.up ℤ)

/-- The actual sheafified pure tensor in the (p,q) summand of the finite total tensor.
Source: Stacks 03EK, 06YM (blueprint: lem-sf-ambient-completed-tensor-adjunction). -/
def finiteGenerator (n : ℕ) (P Q : Cx (completed J A I))
    (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
    (a b : (finite J A I n).obj.obj U)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    (((finiteTensor J A I n).obj (P, Q)).X k).val.obj U :=
  coefficientTensorGenerator.{u, u, u} J (finite J A I n)
    (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).obj P)
    (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).obj Q)
    p q k h U (tensorSection (projection J A I n) (P.X p) U a x)
      (tensorSection (projection J A I n) (Q.X q) U b y)

private instance reduction_additive (n : ℕ) : (reduction J A I true n).Additive := by
  dsimp only [reduction]
  infer_instance

private theorem reductionStep_tensorSection (n : ℕ)
    (M : ConstantCompletion.Mod (completed J A I))
    (U : Cᵒᵖ) (s : (finite J A I (n + 1)).obj.obj U) (x : M.val.obj U) :
    ((reductionStep J A I true n).app M).val.app U
        (tensorSection (projection J A I (n + 1)) M U s x) =
      tensorSection (projection J A I n) M U ((transition J A I n).hom.app U s) x :=
  (reductionStep_existsUnique J A I true n).exists.choose_spec M U s x

private theorem finiteTensorComparison_exists (n : ℕ) :
    ∃ e : coefficientTotalTensor.{u, u, u} J (completed J A I) ⋙
        (reduction J A I true n).mapHomologicalComplex (.up ℤ) ≅ finiteTensor J A I n,
      ∀ (P Q : Cx (completed J A I)) (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
        (a b : (finite J A I n).obj.obj U)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((e.hom.app (P, Q)).f k).val.app U
          (tensorSection (projection J A I n)
            (((coefficientTotalTensor.{u, u, u} J (completed J A I)).obj (P, Q)).X k)
            U (a * b) (coefficientTensorGenerator.{u, u, u} J (completed J A I)
              P Q p q k h U x y)) =
          finiteGenerator J A I n P Q p q k h U a b x y := by
  exact normalizedFiniteTensorComparison J A I n

/-- The unique strict quotient transition sends both scalar factors to their quotients.
Source: Stacks 099M, 07A4 (blueprint: lem-sf-ambient-completed-tensor-adjunction).
Proof: the sectionwise balanced map sends (a tensor x) tensor (b tensor y) to
(q(a) tensor x) tensor (q(b) tensor y). Balancing, restriction and each differential
commute with this map. Sheafify and take the direct-sum totalization. Pure tensors
locally generate the sheafified summands, proving uniqueness and naturality. -/
theorem finiteTensorStep_existsUnique (n : ℕ) :
    ∃! t : finiteTensor J A I (n + 1) ⟶ finiteTensor J A I n,
      ∀ (P Q : Cx (completed J A I)) (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
        (a b : (finite J A I (n + 1)).obj.obj U)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((t.app (P, Q)).f k).val.app U
            (finiteGenerator J A I (n + 1) P Q p q k h U a b x y) =
          finiteGenerator J A I n P Q p q k h U
            ((transition J A I n).hom.app U a) ((transition J A I n).hom.app U b) x y := by
  classical
  obtain ⟨e₀, he₀⟩ := finiteTensorComparison_exists J A I n
  obtain ⟨e₁, he₁⟩ := finiteTensorComparison_exists J A I (n + 1)
  let d := Functor.whiskerLeft
    (coefficientTotalTensor.{u, u, u} J (completed J A I))
    (NatTrans.mapHomologicalComplex (reductionStep J A I true n) (.up ℤ))
  let t : finiteTensor J A I (n + 1) ⟶ finiteTensor J A I n :=
    e₁.inv ≫ d ≫ e₀.hom
  have ht (P Q : Cx (completed J A I)) (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
      (a b : (finite J A I (n + 1)).obj.obj U)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
      ((t.app (P, Q)).f k).val.app U
          (finiteGenerator J A I (n + 1) P Q p q k h U a b x y) =
        finiteGenerator J A I n P Q p q k h U
          ((transition J A I n).hom.app U a) ((transition J A I n).hom.app U b) x y := by
    let H := (coefficientTotalTensor.{u, u, u} J (completed J A I)).obj (P, Q)
    let z := tensorSection (projection J A I (n + 1)) (H.X k) U (a * b)
      (coefficientTensorGenerator.{u, u, u} J (completed J A I) P Q p q k h U x y)
    have hi : ((e₁.inv.app (P, Q)).f k).val.app U
        (finiteGenerator J A I (n + 1) P Q p q k h U a b x y) = z := by
      rw [← he₁ P Q p q k h U a b x y]
      exact congrArg (fun f ↦ (f.f k).val.app U z) (e₁.app (P, Q)).hom_inv_id
    change ((e₀.hom.app (P, Q)).f k).val.app U
      (((reductionStep J A I true n).app (H.X k)).val.app U
        (((e₁.inv.app (P, Q)).f k).val.app U _)) = _
    rw [hi]
    change ((e₀.hom.app (P, Q)).f k).val.app U
      (((reductionStep J A I true n).app (H.X k)).val.app U
        (tensorSection (projection J A I (n + 1)) (H.X k) U (a * b) _)) = _
    rw [reductionStep_tensorSection J A I, map_mul]
    exact he₀ P Q p q k h U _ _ x y
  refine ⟨t, ht, ?_⟩
  intro t' ht'
  apply NatTrans.ext
  funext Z
  rcases Z with ⟨P, Q⟩
  apply (cancel_epi (e₁.hom.app (P, Q))).mp
  apply HomologicalComplex.hom_ext
  intro k
  let F := change (projection J A I (n + 1))
  let : PreservesColimitsOfSize.{0, 0} F :=
    WeilConjectures.extension_preserves_small_colimits.{u, u, u} (projection J A I (n + 1)) F
      (fun _ ↦ rfl)
      (fun _ ↦ by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl)
  apply WeilConjectures.total_extension_hom_ext.{u, u, u}
    (projection J A I (n + 1)) F (fun _ ↦ rfl)
      (fun _ ↦ by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl) P Q k
  intro p q h U c x y
  have he := he₁ P Q p q k h U c 1 x y
  rw [mul_one] at he
  change ((t'.app (P, Q)).f k).val.app U
      (((e₁.hom.app (P, Q)).f k).val.app U
        (tensorSection (projection J A I (n + 1))
          (((coefficientTotalTensor.{u, u, u} J (completed J A I)).obj (P, Q)).X k)
          U c (coefficientTensorGenerator.{u, u, u} J (completed J A I)
            P Q p q k h U x y))) =
    ((t.app (P, Q)).f k).val.app U
      (((e₁.hom.app (P, Q)).f k).val.app U
        (tensorSection (projection J A I (n + 1))
          (((coefficientTotalTensor.{u, u, u} J (completed J A I)).obj (P, Q)).X k)
          U c (coefficientTensorGenerator.{u, u, u} J (completed J A I)
            P Q p q k h U x y)))
  rw [he, ht', ht]

/-- The specified quotient transition; its data are determined by the section formula.
Source: Stacks 099M (blueprint: lem-sf-ambient-completed-tensor-adjunction). -/
def finiteTensorStep (n : ℕ) : finiteTensor J A I (n + 1) ⟶ finiteTensor J A I n :=
  (finiteTensorStep_existsUnique J A I n).exists.choose

/-- The strict inverse sequence of the separately reduced tensors.
Source: Stacks 099M (blueprint: lem-sf-ambient-completed-tensor-adjunction). -/
def finiteTensorTower : Cx (completed J A I) × Cx (completed J A I) ⥤
    ℕᵒᵖ ⥤ Cx (completed J A I) :=
  (Functor.ofOpSequence (finiteTensorStep J A I)).flip

/-- Good representatives impose no restriction on derived inputs: each unbounded
complex has a flat-term K-flat resolution. Source: Stacks 06YS
(blueprint: lem-sf-ambient-completed-tensor-adjunction). -/
def Good : ObjectProperty (Cx (completed J A I)) :=
  fun P ↦ CochainComplex.IsKFlatIndependentCoefficients (R := completed J A I) P ∧
    ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u} (J := J) (R := completed J A I) (P.X i)

/-- The localization of good representatives into the existing ambient derived category.
Source: Stacks 06YS (blueprint: lem-sf-ambient-completed-tensor-adjunction). -/
def goodLocalization : (Good J A I).FullSubcategory ⥤ D (completed J A I) :=
  (Good J A I).ι ⋙ Q (completed J A I)

private theorem totalTensor_good (P Q : (Good J A I).FullSubcategory) :
    let H := (coefficientTotalTensor.{u, u, u} J (completed J A I)).obj (P.obj, Q.obj)
    H.IsAcyclicTensorKFlat ∧ ∀ i : ℤ, SheafOfModules.IsFlat (H.X i) := by
  let R := completed J A I
  let := SheafOfModules.monoidalCategory R
  have ht := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model R
    P.obj Q.obj P.property.1 Q.property.1 P.property.2 Q.property.2
  refine ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mp ht.1, ?_⟩
  intro i
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R _) (ht.2.1 i)

private theorem mapped_identity_postcomp
    {D E : Type*} [Category D] [Category E] (F : D ⥤ E)
    {X : E} {Y : D} (f : X ⟶ F.obj Y) :
    f ≫ F.map (𝟙 Y) = f := by rw [F.map_id, Category.comp_id]

private theorem mapped_iso_comparison
    {D E H : Type*} [Category D] [Category E] [Category H]
    (F : D ⥤ E) (Q : H ⥤ E) {X Y : D} (e : X ≅ Y) {W : H} (V : H) (b : W ≅ V)
    (f : F.obj X ⟶ Q.obj W) [IsIso f] :
    𝟙 _ ≫ (F.mapIso e.symm ≪≫ asIso f ≪≫ Q.mapIso b).hom =
      F.map e.inv ≫ f ≫ Q.map b.hom := by
  simp only [Category.id_comp, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    asIso_hom]

private theorem inverse_unit_equation
    {D : Type*} [Category D] {X Y Z : D} (e : Y ≅ Z)
    (f : X ⟶ Y) (g : X ⟶ Z) (h : f ≫ e.hom = g) : g ≫ e.inv = f := by
  rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]

attribute [local irreducible] CoefficientClosedStructure.tensor coefficientTotalTensor

/-- The derived strict tensor tower is canonically the reduction tower of ordinary tensor;
its total derived limit is Koszul completion with the same unit, and precomposition
with that unit is bijective for every locally complete target.

Source: Stacks 099M, 099B, 0A0E
(blueprint: lem-sf-ambient-completed-tensor-adjunction).
Proof:
1. Set the derived tensor tower to ordinary tensor followed by the existing
   normalized quotient presentation. On good representatives the total tensor is
   K-flat and flat termwise, so its quotient comparison is invertible. Compose
   this comparison with the supplied tensor-model isomorphism.
2. Apply the strict balanced comparison of quotient total tensor towers. Its
   formula sends c tensor (x tensor y) to (1 tensor x) tensor (c tensor y), and
   provides exactly the required chain-level generator normalization.
3. Whisker the existing quotient completion unit by the ordinary tensor functor.
   Its comparison with Koszul completion preserves the actual units. Inverting
   that comparison and using its hom-inverse equation gives the Koszul unit.
4. The existing normalized Koszul/quotient reflector gives the Hom bijection
   into every locally complete target. No boundedness or finite Tor condition
   on the two inputs is introduced; zero and unit ideals are included. -/
theorem ambientCompletedTensorAdjunction [IsNoetherianRing A]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = I)
    (S : CoefficientClosedStructure
      (@derivedInternalHomOfUniverses.{u, u, u, u + 1} C _ J _ _ (completed J A I)
        (HasDerivedCategory.standard _)))
    (models : @CoefficientTensorModels.{u, u, u, u + 1} C _ J _ _ (completed J A I)
      (HasDerivedCategory.standard _) S) :
    ∃ (T : D (completed J A I) × D (completed J A I) ⥤ TD (completed J A I))
      (β : S.tensor ⋙ (quotientPresentation J A I true).tower ≅ T)
      (ν : S.tensor ⟶ T ⋙ rlim (completed J A I)),
      (∀ (P Q : (Good J A I).FullSubcategory),
        ∃ (V : CochainComplex (ℕᵒᵖ ⥤ Mod (completed J A I)) ℤ)
          (κ : V.asFunctor ≅ (finiteTensorTower J A I).obj (P.obj, Q.obj))
          (e : T.obj ((goodLocalization J A I).obj P,
            (goodLocalization J A I).obj Q) ≅ (TQ (completed J A I)).obj V)
          (b : reductionComplex J A I true
            ((coefficientTotalTensor.{u, u, u} J (completed J A I)).obj (P.obj, Q.obj)) ≅ V),
          β.hom.app ((goodLocalization J A I).obj P, (goodLocalization J A I).obj Q) ≫
              e.hom =
            (quotientPresentation J A I true).tower.map
                (models.iso J (completed J A I) S P.obj Q.obj
                  P.property.1 Q.property.1).inv ≫
              (quotientPresentation J A I true).comparison.app
                ((coefficientTotalTensor.{u, u, u} J (completed J A I)).obj (P.obj, Q.obj)) ≫
              (TQ (completed J A I)).map b.hom ∧
          ∀ (n : ℕ) (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
            (c : (finite J A I n).obj.obj U)
            (x : (P.obj.X p).val.obj U) (y : (Q.obj.X q).val.obj U),
            ((κ.hom.app (op n)).f k).val.app U
                (((b.hom.f k).app (op n)).val.app U
                  (tensorSection (projection J A I n)
                    (((coefficientTotalTensor.{u, u, u} J (completed J A I)).obj
                      (P.obj, Q.obj)).X k) U c
                    (coefficientTensorGenerator.{u, u, u} J (completed J A I)
                      P.obj Q.obj p q k h U x y))) =
              finiteGenerator J A I n P.obj Q.obj p q k h U 1 c x y) ∧
      (∀ M : D (completed J A I) × D (completed J A I),
        (completionUnit J A I true).app (S.tensor.obj M) ≫
          (rlim (completed J A I)).map (β.hom.app M) = ν.app M) ∧
      (∃ (K : KoszulPresentation J A I true r a)
        (γ : T ⋙ rlim (completed J A I) ≅ S.tensor ⋙ koszulCompletion J A I K),
        ∀ M : D (completed J A I) × D (completed J A I),
          ν.app M ≫ γ.hom.app M = koszulUnit J A I K (S.tensor.obj M)) ∧
      (∀ (M : D (completed J A I) × D (completed J A I)) (L : D (completed J A I)),
        IsComplete (projection J A I 0) L →
          Function.Bijective (fun f : (T ⋙ rlim (completed J A I)).obj M ⟶ L ↦
            ν.app M ≫ f)) := by
  classical
  let : HasDerivedCategory (ConstantCompletion.Mod (completed J A I)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (ℕᵒᵖ ⥤ ConstantCompletion.Mod (completed J A I)) :=
    HasDerivedCategory.standard _
  let T : D (completed J A I) × D (completed J A I) ⥤ TD (completed J A I) :=
    S.tensor ⋙ (quotientPresentation J A I true).tower
  let β : S.tensor ⋙ (quotientPresentation J A I true).tower ≅ T := Iso.refl _
  let ν : S.tensor ⟶ T ⋙ rlim (completed J A I) :=
    Functor.whiskerLeft S.tensor (completionUnit J A I true)
  let reflector := koszul_quotient_reflector J A I true r a ha
  let K := reflector.choose
  let θ := reflector.choose_spec.1.choose
  have hθ := reflector.choose_spec.1.choose_spec
  have hbij := reflector.choose_spec.2.2.1
  refine ⟨T, β, ν, ?_, ?_, ?_, ?_⟩
  · intro P Q
    let H := (coefficientTotalTensor.{u, u, u} J (completed J A I)).obj (P.obj, Q.obj)
    obtain ⟨hk, hf⟩ := totalTensor_good J A I P Q
    have hc : IsIso ((quotientPresentation J A I true).comparison.app H) :=
      (quotientPresentation J A I true).laws.2.1 H hk hf
    let comparison := quotientTotalTensorTowerComparison J A I
      (finiteTensorStep J A I)
      (fun n ↦ (finiteTensorStep_existsUnique J A I n).exists.choose_spec) P.obj Q.obj
    let V := comparison.choose
    let b := comparison.choose_spec.choose
    let κ := comparison.choose_spec.choose_spec.choose
    have hκ := comparison.choose_spec.choose_spec.choose_spec
    let e : T.obj ((goodLocalization J A I).obj P,
        (goodLocalization J A I).obj Q) ≅ (TQ (completed J A I)).obj V :=
      (quotientPresentation J A I true).tower.mapIso
        (models.iso J (completed J A I) S P.obj Q.obj
          P.property.1 Q.property.1).symm ≪≫
        asIso ((quotientPresentation J A I true).comparison.app H) ≪≫
          (TQ (completed J A I)).mapIso b
    refine ⟨V, κ, e, b, ?_, ?_⟩
    · exact mapped_iso_comparison (quotientPresentation J A I true).tower
        (TQ (completed J A I))
        (models.iso J (completed J A I) S P.obj Q.obj
          P.property.1 Q.property.1) V b
        ((quotientPresentation J A I true).comparison.app H)
    · exact hκ
  · intro M
    change (completionUnit J A I true).app (S.tensor.obj M) ≫
      (rlim (completed J A I)).map (𝟙 _) =
      (completionUnit J A I true).app (S.tensor.obj M)
    exact mapped_identity_postcomp (rlim (completed J A I)) _
  · refine ⟨K, Functor.isoWhiskerLeft S.tensor θ.symm, ?_⟩
    intro M
    change (completionUnit J A I true).app (S.tensor.obj M) ≫
      θ.inv.app (S.tensor.obj M) = _
    exact inverse_unit_equation (θ.app (S.tensor.obj M)) _ _ (hθ _)
  · intro M L hL
    exact hbij (S.tensor.obj M) L hL

end CategoryTheory.AmbientCompletedTensor

namespace WeilConjectures

private theorem completionUnit_hom_bijective
    {D : Type*} [Category D] (F : D ⥤ D) (η : 𝟭 D ⟶ F)
    (hη : ∀ M, IsIso (F.map (η.app M))) (M L : D) [IsIso (η.app L)] :
    Function.Bijective (fun f : F.obj M ⟶ L ↦ η.app M ≫ f) := by
  constructor
  · intro f g hfg
    have := hη M
    have hmap : F.map f = F.map g := by
      apply (cancel_epi (F.map (η.app M))).mp
      simpa only [← F.map_comp] using congrArg F.map hfg
    apply (cancel_mono (η.app L)).mp
    have hf := η.naturality f
    have hg := η.naturality g
    simp only [Functor.id_map] at hf hg
    rw [hf, hg, hmap]
  · intro f
    refine ⟨F.map f ≫ inv (η.app L), ?_⟩
    have hn := η.naturality f
    dsimp only [Functor.id_map, Functor.id_obj] at hn
    dsimp only
    rw [← Category.assoc, ← hn, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective in
/-- For local-field integral coefficients the published completed tensor unit induces
the asserted bijection into complete targets.
The local vanishing condition is spelled out on every slice and every section of tB.

Source: Stacks 099M, 099B, 0A0E; Bhatt--Scholze, Definition 3.4.10
(blueprint: lem-sf-ambient-completed-tensor-adjunction).
Proof: choose a good representative of the target using the existing localization.
The principal uniformizer datum and the Roos/intrinsic equivalence turn the given
local vanishing into invertibility of its actual completion unit. Completion
inverts its own unit by integralCompletion_unit_inverted. For any functor F with
unit eta having this property, precomposition with eta_M into a target K whose
unit is invertible is bijective. A preimage of f is F(f) followed by eta_K inverse,
by naturality. For injectivity apply F, cancel F(eta_M), use naturality, and cancel
eta_K. Apply this argument to M equal to the ordinary tensor. The published
completedTensor is its quotient completion by definition. -/
theorem integralAmbientCompletedTensorAdjunction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{t}) :
    ∀ (P L K : IntegralOnSlice.D.{t, u} l E X none),
      (∀ (U : X.ProEt)
        (s : ((IntegralOnSlice.ring.{t, u} l E X (some U)).obj ⋙
            forget CommRingCat.{max u (t + 1)}).sections),
        (∃ Z : Sieve U, Z ∈ AlgebraicGeometry.Scheme.ProEt.topology X U ∧
          ∀ (V : X.ProEt) (f : V ⟶ U), Z f →
            ∃ c : (completedIntegralCoefficientSheafUnrestricted.{t, u} l E X).obj.obj (op V),
              s.val (op (Over.mk f)) = integralCompletionScalarValue.{t, u} l E X (op V) * c) →
        IsZero (integralCompletionLocalTest.{t, u} l E X K U s)) →
      Function.Bijective (fun f :
        (IntegralOnSlice.completedTensor.{t, u} l E X none).obj (P, L) ⟶ K ↦
        (IntegralOnSlice.completionUnit.{t, u} l E X none).app
          ((@RingedSiteDualityModel.closed.{t + 1, t, u, (max u (t + 1)) + 1}
            _ _ _ (IntegralOnSlice.abSheafify.{t, u} X none)
            (IntegralOnSlice.abLocallyBijective.{t, u} X none) _ _
            (IntegralOnSlice.duality.{t, u} l E X none)).tensor.obj (P, L)) ≫ f) := by
  intro P L K hK
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  have hpl : p ≠ l := by omega
  let q := IntegralOnSlice.qGood.{t, u} l E X none
  let : q.IsLocalization ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage
      (IntegralOnSlice.Good l E X none).ι) := IntegralOnSlice.goodLocalization.{t, u} l E X none
  let := Localization.essSurj q
    ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage
      (IntegralOnSlice.Good l E X none).ι)
  let Q := q.objPreimage K
  let e : DerivedCategory.Q.obj Q.obj ≅ K := q.objObjPreimageIso K
  obtain ⟨d, hd, _⟩ := PrincipalKoszulStrictReplacement.coefficient_datum.{u} l E
  have hunit : IsIso ((IntegralOnSlice.completionUnit l E X none).app K) :=
    ((roosIntrinsicCompletenessEquivalence.{t, u} p l hpl E X d hd K Q e).out 1 4).mp hK
  exact completionUnit_hom_bijective (IntegralOnSlice.completion l E X none)
    (IntegralOnSlice.completionUnit l E X none)
    (IntegralOnSlice.integralCompletion_unit_inverted l E X) _ K


/-- Keep the concrete finite-field structure out of the completeness proof's reductions. -/
@[irreducible] private def auxiliaryFiniteFieldDatum (p : ℕ) (hp : p.Prime) :
    FiniteFieldDatum.{0} := by
  let : Fact p.Prime := ⟨hp⟩
  exact
    { p := p
      a := 1
      q := p
      prime := hp
      exponent_pos := by decide
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }

private theorem auxiliaryFiniteFieldDatum_p (p : ℕ) (hp : p.Prime) :
    (auxiliaryFiniteFieldDatum p hp).p = p := by
  unfold auxiliaryFiniteFieldDatum
  rfl

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  IntegralOnSlice.abSheafify IntegralOnSlice.abLocallyBijective in
/-- Every object of the recorded integral bounded constructible category is locally
uniformizer-complete on every slice. The uniform reduction amplitude is used only
by the existing category predicate and places no bound on tensor inputs.
Source: Stacks 0999, 0A0E; Bhatt--Scholze, Definition 3.5.2
(blueprint: lem-sf-ambient-completed-tensor-adjunction).
Proof: the predicate supplies the Roos-triangle completeness condition. Its actual
quotient transitions and legs agree with the unrestricted reduction tower, since both
are fixed by the sectionwise quotient tensor and x mapped to 1 tensor x units.
The uniformizer datum hypotheses follow from lem-a1-principal-koszul-strict-replacement.
Apply (i) implies (ii) of lem-pur-roos-intrinsic-completeness-equivalence, choosing the
auxiliary prime 3 for l=2 and 2 otherwise. The vanishing is for all local sections
of the ideal sheaf, expressed by local divisibility, not just its global generator. -/
theorem integralConstructible_locallyComplete
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{u}) :
    ∀ K : IntegralOnSlice.D.{u, u} l E X none,
      sfIntegralConstructible.{u} l E X K →
        ∀ (U : X.ProEt)
          (s : ((IntegralOnSlice.ring.{u, u} l E X (some U)).obj ⋙
            forget CommRingCat.{u + 1}).sections),
          (∃ Z : Sieve U, Z ∈ AlgebraicGeometry.Scheme.ProEt.topology X U ∧
            ∀ (V : X.ProEt) (f : V ⟶ U), Z f →
              ∃ c : (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X).obj.obj (op V),
                s.val (op (Over.mk f)) = integralCompletionScalarValue.{u, u} l E X (op V) * c) →
          IsZero (integralCompletionLocalTest.{u, u} l E X K U s) := by
  intro K hK
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  have hpl : p ≠ l := by omega
  let D := auxiliaryFiniteFieldDatum p hprime
  have hl : l ≠ D.p := by
    change l ≠ (auxiliaryFiniteFieldDatum p hprime).p
    rw [auxiliaryFiniteFieldDatum_p]
    omega
  have hc : IntegralOnSlice.IsComplete l E X none K :=
    ⟨D, hl, (sfDerivedComplete_iff_legacy.{u, 0} l E X D hl K).mp hK.1⟩
  let q := IntegralOnSlice.qGood.{u, u} l E X none
  let : q.IsLocalization ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage
      (IntegralOnSlice.Good l E X none).ι) := IntegralOnSlice.goodLocalization.{u, u} l E X none
  let := Localization.essSurj q
    ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage
      (IntegralOnSlice.Good l E X none).ι)
  let P := q.objPreimage K
  let e : DerivedCategory.Q.obj P.obj ≅ K := q.objObjPreimageIso K
  obtain ⟨d, hd, _⟩ := PrincipalKoszulStrictReplacement.coefficient_datum.{u} l E
  exact ((roosIntrinsicCompletenessEquivalence.{u, u} p l hpl E X d hd K P e).out 0 1).mp hc

end WeilConjectures
