/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.SequentialDerivedInverseLimit
public import Sheaf.Paper.SequentialDerivedInverseLimitCompleted
public import Sheaf.Paper.StrictPerfectPackageOnSite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Sheaf.Algebra.Homology.DerivedTensor
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.Algebra.Homology.Monoidal.Dual
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Finite-projective tensor and countable derived products

Source: blueprint, proper base change, finite-reduction-reconstruction proof,
final sentence on tensor and the two Roos products
(blueprint: lem-weil-pbc-finite-projective-tensor-products).

A bounded finite-free retract complex P represents E. Tensor in the first variable
with P in the second already preserves quasi-isomorphisms, so localization gives
precisely C ↦ C tensor-derived E, without resolving C or choosing representatives
of derived objects. The localization comparison fixes this functor on every complex.
The product comparison is Mathlib's canonical map induced by the projections.

## Main definitions

* `finiteProjectiveTensorComplexRight`: total tensor with the chosen representative.
* `finiteProjectiveTensorRight`: its canonical localization lift.
* `finiteProjectiveTensorRightComparison`: the comparison on all complexes.
* `finiteProjectiveTensorRightMap`: the unique roof-normalized coefficient action.

## Main statements

* `finiteProjectiveTensorComplexRight_inverts`: bounded finite-free retracts are K-flat.
* `finiteProjectiveTensorRightMap_exists`: existence and uniqueness of the coefficient action.
* `finiteProjectiveTensorProducts`: preservation of products and naturality.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
variable (d : ProEtaleAdicCoefficientDatum A)

/-- Total tensor with P, followed by the standard localization in D(Mod(A_T)).
Source: blueprint, finite-reduction-reconstruction proof, tensor/Roos sentence
(blueprint: lem-weil-pbc-finite-projective-tensor-products). -/
def finiteProjectiveTensorComplexRight (P : CochainComplex (adicDatumModules T d) ℤ) :
    CochainComplex (adicDatumModules T d) ℤ ⥤ adicDatumDerived T d :=
  (completedConstantTensor T (adicDatumRing T d)).flip.obj P ⋙ completedConstantQ _

private theorem finite_unit_dualizable
    {M : Type*} [Category M] [Abelian M] [MonoidalCategory M]
    [MonoidalPreadditive M] [HasFiniteBiproducts M] (n : ℕ) :
    IsDualizable (∏ᶜ (fun _ : Fin n ↦ MonoidalCategoryStruct.tensorUnit M)) := by
  classical
  let : HasBinaryBiproducts M := HasBinaryBiproducts.of_hasBinaryProducts
  induction n with
  | zero =>
    apply IsZero.isDualizable
    apply (IsZero.iff_id_eq_zero _).2
    apply Pi.hom_ext
    intro i
    exact Fin.elim0 i
  | succ n ih =>
    let e : (MonoidalCategoryStruct.tensorUnit M ⊞
        ∏ᶜ fun _ : Fin n ↦ MonoidalCategoryStruct.tensorUnit M) ≅
        (∏ᶜ fun _ : Fin (n + 1) ↦ MonoidalCategoryStruct.tensorUnit M) :=
      { hom := Pi.lift (Fin.cases biprod.fst (fun i ↦ biprod.snd ≫ Pi.π _ i))
        inv := biprod.lift (Pi.π _ 0) (Pi.lift (fun i ↦ Pi.π _ i.succ))
        hom_inv_id := by
          apply biprod.hom_ext
          · simp
          · apply Pi.hom_ext
            intro i
            simp
        inv_hom_id := by
          apply Pi.hom_ext
          intro i
          refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp }
    exact (isDualizable_unit.biprod ih).of_iso e

private theorem tensor_right_quasiIso_adic
    {E E' P : CochainComplex (adicDatumModules T d) ℤ} (f : E ⟶ E')
    (hf : QuasiIso f) (hP : P.IsAcyclicTensorKFlat) :
    letI := SheafOfModules.monoidalCategory (adicDatumRing T d)
    QuasiIso (HomologicalComplex.mapBifunctorMap f (𝟙 P) (MonoidalCategory.curriedTensor _)
      (.up ℤ)) := by
  let := SheafOfModules.monoidalCategory (adicDatumRing T d)
  let := SheafOfModules.tensorPreadditive.{t + 1, t, t + 1} (adicDatumRing T d)
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic f).1 hf
  have ht := hP (CochainComplex.mappingCone f) hc
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht i).of_iso
    (CochainComplex.mapBifunctorMappingCone₁Iso f P (MonoidalCategory.curriedTensor _))

private theorem finiteProjective_isKFlat
    (P : CochainComplex (adicDatumModules T d) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P.X j))
    (p : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget T).obj (adicDatumRing T d)) P) :
    CochainComplex.IsKFlatIndependentCoefficients (R := adicDatumRing T d) P := by
  classical
  let := SheafOfModules.monoidalCategory (adicDatumRing T d)
  let := SheafOfModules.symmetricCategory (adicDatumRing T d)
  let := SheafOfModules.tensorPreadditive.{t + 1, t, t + 1} (adicDatumRing T d)
  obtain ⟨a, b, hbound⟩ := hb
  have hdual (n : ℤ) : IsDualizable (P.X n) := by
    apply IsDualizable.of_retract ⟨p.i n, p.p n, p.splitting n⟩
    exact finite_unit_dualizable (p.N n)
  have hflat (n : ℤ) :
      SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
        (J := ProEt.topology T) (R := adicDatumRing T d) (P.X n) := by
    obtain ⟨_⟩ := hdual n
    have := (tensorLeftAdjunction (P.X n) (P.X n)ᘁ).rightAdjoint_preservesLimits
    have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients
      (adicDatumRing T d) (P.X n)
    have hl : exactFunctor _ _ (MonoidalCategory.tensorLeft (P.X n)) :=
      (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩
    have hr := (exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight (P.X n)) hl
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (adicDatumRing T d) (P.X n)).symm hr
  have : P.IsStrictlyLE b :=
    (P.isStrictlyLE_iff b).2 (fun n hn ↦ hbound n (Or.inr hn))
  exact SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    (adicDatumRing T d) P b hflat

/-- Bounded finite-free retract terms make tensor with P preserve quasi-isomorphisms.
Source: blueprint, finite-reduction-reconstruction proof, tensor/Roos sentence
(blueprint: lem-weil-pbc-finite-projective-tensor-products).
Proof: finite powers of the unit are dualizable by induction using binary
biproducts, and dualizability passes to retracts. The tensor adjunction and tensor
colimit preservation give exactness of tensor by each term. The independent-universe
bounded-above flat criterion makes P K-flat. Tensor commutes with mapping cones, so
the acyclic-cone criterion proves preservation of quasi-isomorphisms. Localization
then inverts their images. -/
theorem finiteProjectiveTensorComplexRight_inverts
    (P : CochainComplex (adicDatumModules T d) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P.X j))
    (p : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget T).obj (adicDatumRing T d)) P) :
    (HomologicalComplex.quasiIso (adicDatumModules T d) (ComplexShape.up ℤ)).IsInvertedBy
      (finiteProjectiveTensorComplexRight T d P) := by
  let := SheafOfModules.monoidalCategory (adicDatumRing T d)
  have hK : P.IsAcyclicTensorKFlat :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).1
      (finiteProjective_isKFlat T d P hb p)
  intro X Y f hf
  have : QuasiIso f := hf
  have htensor := tensor_right_quasiIso_adic T d f hf hK
  have : QuasiIso
      (((completedConstantTensor T (adicDatumRing T d)).flip.obj P).map f) := htensor
  have hq : IsIso ((completedConstantQ _).map
      (((completedConstantTensor T (adicDatumRing T d)).flip.obj P).map f)) := by
    exact inferInstance
  exact hq

/-- The canonical derived functor C ↦ C tensor-derived E, for E represented by P.
The value is defined by localization, with its universal representative comparison;
no arbitrary endofunctor or isomorphism is chosen.
Source: blueprint, finite-reduction-reconstruction proof, tensor/Roos sentence
(blueprint: lem-weil-pbc-finite-projective-tensor-products). -/
def finiteProjectiveTensorRight (P : CochainComplex (adicDatumModules T d) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P.X j))
    (p : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget T).obj (adicDatumRing T d)) P) :
    adicDatumDerived T d ⥤ adicDatumDerived T d :=
  Localization.lift (finiteProjectiveTensorComplexRight T d P)
    (finiteProjectiveTensorComplexRight_inverts T d P hb p) (completedConstantQ _)

/-- On every complex, this is exactly total tensor with the chosen bounded representative.
It identifies the functor with derived tensor by E = Q(P), naturally in the input.
Source: blueprint, finite-reduction-reconstruction proof, tensor/Roos sentence
(blueprint: lem-weil-pbc-finite-projective-tensor-products). -/
def finiteProjectiveTensorRightComparison (P : CochainComplex (adicDatumModules T d) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P.X j))
    (p : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget T).obj (adicDatumRing T d)) P) :
    completedConstantQ _ ⋙ finiteProjectiveTensorRight T d P hb p ≅
      finiteProjectiveTensorComplexRight T d P :=
  Localization.fac (finiteProjectiveTensorComplexRight T d P)
    (finiteProjectiveTensorComplexRight_inverts T d P hb p) (completedConstantQ _)

/-- A derived coefficient map induces a unique tensor transformation, fixed on every
K-flat test complex and every roof representing that coefficient map.
Source: blueprint, finite-reduction-reconstruction proof, functoriality in step 4
(blueprint: lem-weil-pbc-finite-projective-tensor-products).
Proof: use the normalized one-K-flat comparison of
lem-sf-ringed-derived-closed-symmetric-monoidal. Since P and P' are K-flat,
this compares their tensor functors on every complex with the recorded derived
bifunctor. Full faithfulness of precomposition with localization lifts these
comparisons to the derived category. Conjugating tensor with e gives the required
natural transformation. For a K-flat test C, naturality of the comparison on
C tensor S, C tensor P, and C tensor P' gives the prescribed formula for every roof.
For uniqueness, choose one roof representing e. Its denominator tensored with any
K-flat C becomes invertible, so the formula determines the component at Q(C).
Resolve an arbitrary test complex by a K-flat complex using lem-pc-kflat-resolution;
naturality and invertibility of its augmentation determine the remaining components.
Localization's transformation extensionality gives equality. -/
theorem finiteProjectiveTensorRightMap_exists
    (P P' : CochainComplex (adicDatumModules T d) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P.X j))
    (hb' : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P'.X j))
    (p : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget T).obj (adicDatumRing T d)) P)
    (p' : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget T).obj (adicDatumRing T d)) P')
    (e : (completedConstantQ _).obj P ⟶ (completedConstantQ _).obj P') :
    ∃! η : finiteProjectiveTensorRight T d P hb p ⟶
        finiteProjectiveTensorRight T d P' hb' p',
      ∀ (C : CochainComplex (adicDatumModules T d) ℤ),
        CochainComplex.IsAcyclicTensorKFlat (R := adicDatumRing T d) C →
        ∀ (S : CochainComplex (adicDatumModules T d) ℤ) (s : S ⟶ P) [QuasiIso s]
          (g : S ⟶ P'),
          e = inv ((completedConstantQ _).map s) ≫ (completedConstantQ _).map g →
          (completedConstantQ _).map
              (((completedConstantTensor T (adicDatumRing T d)).obj C).map s) ≫
            (finiteProjectiveTensorRightComparison T d P hb p).inv.app C ≫
              η.app ((completedConstantQ _).obj C) =
          (completedConstantQ _).map
              (((completedConstantTensor T (adicDatumRing T d)).obj C).map g) ≫
            (finiteProjectiveTensorRightComparison T d P' hb' p').inv.app C := by
  classical
  let := HasDerivedCategory.standard (adicDatumModules T d)
  obtain ⟨S, M, β, ⟨coh⟩⟩ :=
    CategoryTheory.ringedDerived_closed_symmetric_monoidal.{t + 1, t, t + 1, t + 2}
      (ProEt.topology T) (adicDatumRing T d)
  let Q := completedConstantQ (adicDatumModules T d)
  let τ (X Y : CochainComplex (adicDatumModules T d) ℤ)
      (h : CochainComplex.IsKFlatIndependentCoefficients (R := adicDatumRing T d) X ∨
        CochainComplex.IsKFlatIndependentCoefficients (R := adicDatumRing T d) Y) :
      Q.obj (((completedConstantTensor T (adicDatumRing T d)).obj X).obj Y) ≅
        S.tensor.obj (Q.obj X, Q.obj Y) := coh.tensorIso X Y h
  let F := finiteProjectiveTensorRight T d P hb p
  let F' := finiteProjectiveTensorRight T d P' hb' p'
  let H (V : adicDatumDerived T d) := Prod.sectL (adicDatumDerived T d) V ⋙ S.tensor
  have hP := finiteProjective_isKFlat T d P hb p
  have hP' := finiteProjective_isKFlat T d P' hb' p'
  let c (K : CochainComplex (adicDatumModules T d) ℤ)
      (hK : CochainComplex.IsKFlatIndependentCoefficients (R := adicDatumRing T d) K) :
      finiteProjectiveTensorComplexRight T d K ≅ Q ⋙ H (Q.obj K) :=
    NatIso.ofComponents (fun C ↦ τ C K (Or.inr hK)) (by
      intro C C' f
      have hn := coh.tensorIso_naturality C K C' K (Or.inr hK) (Or.inr hK) f (𝟙 K)
      change Q.map
          (((completedConstantTensor T (adicDatumRing T d)).map f).app K ≫
            ((completedConstantTensor T (adicDatumRing T d)).obj C').map (𝟙 K)) ≫
              (τ C' K (Or.inr hK)).hom =
        (τ C K (Or.inr hK)).hom ≫ S.tensor.map (Q.map f, Q.map (𝟙 K)) at hn
      simpa [finiteProjectiveTensorComplexRight, Q, H] using hn)
  let ff := Localization.fullyFaithfulWhiskeringLeft Q
    (HomologicalComplex.quasiIso (adicDatumModules T d) (.up ℤ)) (adicDatumDerived T d)
  let α : F ≅ H (Q.obj P) := ff.preimageIso
    (finiteProjectiveTensorRightComparison T d P hb p ≪≫ c P hP)
  let α' : F' ≅ H (Q.obj P') := ff.preimageIso
    (finiteProjectiveTensorRightComparison T d P' hb' p' ≪≫ c P' hP')
  let μ : H (Q.obj P) ⟶ H (Q.obj P') :=
    { app := fun X ↦ S.tensor.map (𝟙 X, e)
      naturality := by
        intro X Y f
        dsimp [H]
        rw [← S.tensor.map_comp, ← S.tensor.map_comp]
        simp }
  let η : F ⟶ F' := α.hom ≫ μ ≫ α'.inv
  have hα (C : CochainComplex (adicDatumModules T d) ℤ) :
      α.hom.app (Q.obj C) =
        (finiteProjectiveTensorRightComparison T d P hb p).hom.app C ≫
          (τ C P (Or.inr hP)).hom := by
    exact congr_app (ff.map_preimage _) C
  have hα' (C : CochainComplex (adicDatumModules T d) ℤ) :
      α'.hom.app (Q.obj C) =
        (finiteProjectiveTensorRightComparison T d P' hb' p').hom.app C ≫
          (τ C P' (Or.inr hP')).hom := by
    exact congr_app (ff.map_preimage _) C
  have hη (C : CochainComplex (adicDatumModules T d) ℤ)
      (hC : CochainComplex.IsAcyclicTensorKFlat (R := adicDatumRing T d) C)
      (V : CochainComplex (adicDatumModules T d) ℤ) (s : V ⟶ P) [QuasiIso s]
      (g : V ⟶ P') (he : e = inv (Q.map s) ≫ Q.map g) :
      Q.map (((completedConstantTensor T (adicDatumRing T d)).obj C).map s) ≫
          (finiteProjectiveTensorRightComparison T d P hb p).inv.app C ≫
            η.app (Q.obj C) =
        Q.map (((completedConstantTensor T (adicDatumRing T d)).obj C).map g) ≫
          (finiteProjectiveTensorRightComparison T d P' hb' p').inv.app C := by
    have hC' := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat C).2 hC
    have hs := coh.tensorIso_naturality C V C P (Or.inl hC') (Or.inr hP) (𝟙 C) s
    have hg := coh.tensorIso_naturality C V C P' (Or.inl hC') (Or.inr hP') (𝟙 C) g
    have hs' :
        Q.map (((completedConstantTensor T (adicDatumRing T d)).obj C).map s) ≫
            (τ C P (Or.inr hP)).hom =
          (τ C V (Or.inl hC')).hom ≫
            S.tensor.map (𝟙 (Q.obj C), Q.map s) := by
      simpa [WeilConjectures.coefficientTotalTensor, completedConstantTensor, Q, τ] using hs
    have hg' :
        Q.map (((completedConstantTensor T (adicDatumRing T d)).obj C).map g) ≫
            (τ C P' (Or.inr hP')).hom =
          (τ C V (Or.inl hC')).hom ≫
            S.tensor.map (𝟙 (Q.obj C), Q.map g) := by
      simpa [WeilConjectures.coefficientTotalTensor, completedConstantTensor, Q, τ] using hg
    apply (cancel_mono (α'.hom.app (Q.obj C))).1
    dsimp only [η, μ, NatTrans.comp_app]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [hα, hα']
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← Category.assoc, hs', Category.assoc, ← S.tensor.map_comp, hg']
    congr 2
    ext <;> simp [he]
  refine ⟨η, hη, ?_⟩
  intro θ hθ
  apply Localization.natTrans_ext Q
    (HomologicalComplex.quasiIso (adicDatumModules T d) (.up ℤ))
  intro C
  obtain ⟨K, s, hK, _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := adicDatumRing T d) C
  have : QuasiIso s := hs
  have hK' := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat K).1 hK
  obtain ⟨V, v, hv, g, he⟩ := DerivedCategory.right_fac e
  have : QuasiIso v := (DerivedCategory.isIso_Q_map_iff_quasiIso _ v).1 hv
  have hθK := hθ K hK' V v g he
  have hηK := hη K hK' V v g he
  have hvK : IsIso
      (Q.map (((completedConstantTensor T (adicDatumRing T d)).obj K).map v)) := by
    have hn := coh.tensorIso_naturality K V K P (Or.inl hK) (Or.inr hP) (𝟙 K) v
    have hh : Q.map (((completedConstantTensor T (adicDatumRing T d)).obj K).map v) =
        (τ K V (Or.inl hK)).hom ≫ S.tensor.map (𝟙 (Q.obj K), Q.map v) ≫
          (τ K P (Or.inr hP)).inv := by
      have hn' :
          Q.map (((completedConstantTensor T (adicDatumRing T d)).obj K).map v) ≫
              (τ K P (Or.inr hP)).hom =
            (τ K V (Or.inl hK)).hom ≫
              S.tensor.map (𝟙 (Q.obj K), Q.map v) := by
        simpa [WeilConjectures.coefficientTotalTensor, completedConstantTensor, Q, τ] using hn
      apply (cancel_mono (τ K P (Or.inr hP)).hom).1
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hn'
    have : IsIso (S.tensor.map
        (X := (Q.obj K, Q.obj V)) (Y := (Q.obj K, Q.obj P))
        (𝟙 (Q.obj K), Q.map v)) :=
      inferInstanceAs (IsIso
        ((Prod.sectR (Q.obj K) (adicDatumDerived T d) ⋙ S.tensor).map (Q.map v)))
    rw [hh]
    infer_instance
  have hK_eq : θ.app (Q.obj K) = η.app (Q.obj K) := by
    apply (cancel_epi (Q.map
      (((completedConstantTensor T (adicDatumRing T d)).obj K).map v) ≫
        (finiteProjectiveTensorRightComparison T d P hb p).inv.app K)).1
    simpa only [Category.assoc] using hθK.trans hηK.symm
  apply (cancel_epi (F.map (Q.map s))).1
  rw [θ.naturality, η.naturality, hK_eq]

/-- Tensoring an arbitrary derived coefficient map, defined by its unique roof formula.
Source: blueprint, finite-reduction-reconstruction proof, functoriality in step 4
(blueprint: lem-weil-pbc-finite-projective-tensor-products). -/
def finiteProjectiveTensorRightMap
    (P P' : CochainComplex (adicDatumModules T d) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P.X j))
    (hb' : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P'.X j))
    (p : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget T).obj (adicDatumRing T d)) P)
    (p' : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget T).obj (adicDatumRing T d)) P')
    (e : (completedConstantQ _).obj P ⟶ (completedConstantQ _).obj P') :
    finiteProjectiveTensorRight T d P hb p ⟶ finiteProjectiveTensorRight T d P' hb' p' :=
  (finiteProjectiveTensorRightMap_exists T d P P' hb hb' p p' e).exists.choose

private theorem preserves_products_of_essSurj
    {C₀ : Type*} [Category* C₀] {D₀ : Type*} [Category* D₀]
    {B₀ : Type*} [Category* B₀] (J : Type*) [HasProductsOfShape J C₀]
    (Q : C₀ ⥤ D₀) [Q.EssSurj] (H : D₀ ⥤ B₀)
    (hQ : ∀ K : J → C₀,
      Nonempty (IsLimit (Q.mapCone (limit.cone (Discrete.functor K)))))
    [PreservesLimitsOfShape (Discrete J) (Q ⋙ H)] :
    PreservesLimitsOfShape (Discrete J) H := by
  classical
  have h (E : J → D₀) : PreservesLimit (Discrete.functor E) H := by
    let K := fun j ↦ Q.objPreimage (E j)
    let e : Discrete.functor K ⋙ Q ≅ Discrete.functor E :=
      Discrete.natIso (fun j ↦ Q.objObjPreimageIso (E j.as))
    have : PreservesLimit (Discrete.functor K ⋙ Q) H :=
      preservesLimit_of_preserves_limit_cone (hQ K).some
        (isLimitOfPreserves (Q ⋙ H) (limit.isLimit (Discrete.functor K)))
    exact preservesLimit_of_iso_diagram H e
  let := h
  exact preservesLimitsOfShape_of_discrete H

private theorem finiteProjectiveTensorRight_preservesProducts
    (P : CochainComplex (adicDatumModules T d) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P.X j))
    (p : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget T).obj (adicDatumRing T d)) P) :
    PreservesLimitsOfShape (Discrete ℕ) (finiteProjectiveTensorRight T d P hb p) := by
  classical
  let := SheafOfModules.monoidalCategory (adicDatumRing T d)
  let := SheafOfModules.symmetricCategory (adicDatumRing T d)
  let := SheafOfModules.tensorPreadditive.{t + 1, t, t + 1} (adicDatumRing T d)
  have (M : adicDatumModules T d) :
      PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft M) := by
    have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients
      (adicDatumRing T d) M
    exact preservesColimitsOfSize_shrink _
  have (M : adicDatumModules T d) :
      PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have hbcopy := hb
  obtain ⟨a, b, hab⟩ := hbcopy
  have : P.IsStrictlyGE a :=
    (P.isStrictlyGE_iff a).2 (fun n hn ↦ hab n (Or.inl hn))
  have : P.IsStrictlyLE b :=
    (P.isStrictlyLE_iff b).2 (fun n hn ↦ hab n (Or.inr hn))
  have hdual (n : ℤ) : IsDualizable (P.X n) := by
    apply IsDualizable.of_retract ⟨p.i n, p.p n, p.splitting n⟩
    exact finite_unit_dualizable (p.N n)
  obtain ⟨_⟩ := CochainComplex.isDualizable_of_isStrictlyGE_of_isStrictlyLE a b hdual
  let := BraidedCategory.exactPairing_swap P Pᘁ
  have := (tensorRightAdjunction Pᘁ P).rightAdjoint_preservesLimits
  let Q := completedConstantQ (adicDatumModules T d)
  let := HasDerivedCategory.standard (adicDatumModules T d)
  let := adicDatumCountableAB4Star T d
  have hQ (K : ℕ → CochainComplex (adicDatumModules T d) ℤ) :
      Nonempty (IsLimit (Q.mapCone (limit.cone (Discrete.functor K)))) :=
    (derivedCategory_countableProducts_core.{0, t + 2, t + 1, t + 2}
      (adicDatumModules T d)).choose_spec.1 ℕ K
  have : PreservesLimitsOfShape (Discrete ℕ) Q := by
    have (K : ℕ → CochainComplex (adicDatumModules T d) ℤ) :
        PreservesLimit (Discrete.functor K) Q :=
      preservesLimit_of_preserves_limit_cone (limit.isLimit _) (hQ K).some
    exact preservesLimitsOfShape_of_discrete Q
  have : PreservesLimitsOfShape (Discrete ℕ) (finiteProjectiveTensorComplexRight T d P) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ)
      (MonoidalCategory.tensorRight P ⋙ Q))
  have : PreservesLimitsOfShape (Discrete ℕ)
      (Q ⋙ finiteProjectiveTensorRight T d P hb p) :=
    preservesLimitsOfShape_of_natIso
      (finiteProjectiveTensorRightComparison T d P hb p).symm
  exact preserves_products_of_essSurj ℕ Q _ hQ

/-- Tensor by a globally strict-perfect coefficient complex preserves countable products.
The comparison is induced by the actual derived-product projections. The second clause
records naturality for every derived coefficient map e : E → E', using the unique
roof-normalized tensor transformation, and every componentwise map f of families.
Thus the assertion is independent of the bounded representative and is functorial
in E and in the family.

Source: blueprint, finite-reduction-reconstruction proof, final tensor/Roos sentence
(blueprint: lem-weil-pbc-finite-projective-tensor-products).
Proof:
1. Finite powers of the unit are dualizable, and dualizability passes to the given
retracts. The bounded-complex dual construction therefore makes P dualizable.
2. The tensor adjunction shows that total tensor with P preserves products of
complexes. This packages the finite free, retract and bounded totalization argument,
including the signed differential, into the source library's dual-complex theorem.
3. Exact countable products identify localization of the product cone of complexes
with the derived product. Transfer preservation through the localization comparison;
essential surjectivity of localization supplies representatives of every family.
4. The resulting isomorphism is the canonical piComparison. Compose both naturality
routes with each product projection. Functoriality, naturality of the coefficient
transformation, and product extensionality give the displayed equality. -/
theorem finiteProjectiveTensorProducts
    (P : CochainComplex (adicDatumModules T d) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P.X j))
    (p : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((adicLisseForget T).obj (adicDatumRing T d)) P)
    (C : ℕ → adicDatumDerived T d) :
    IsIso (piComparison (finiteProjectiveTensorRight T d P hb p) C) ∧
    ∀ (P' : CochainComplex (adicDatumModules T d) ℤ)
      (hb' : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (P'.X j))
      (p' : SheafOfModules.StrictPerfectCoefficientPackageOnSite
        ((adicLisseForget T).obj (adicDatumRing T d)) P')
      (e : (completedConstantQ _).obj P ⟶ (completedConstantQ _).obj P')
      (C' : ℕ → adicDatumDerived T d) (f : ∀ n : ℕ, C n ⟶ C' n),
      (finiteProjectiveTensorRight T d P hb p).map (Limits.Pi.map f) ≫
          (finiteProjectiveTensorRightMap T d P P' hb hb' p p' e).app (∏ᶜ C') ≫
          piComparison (finiteProjectiveTensorRight T d P' hb' p') C' =
        piComparison (finiteProjectiveTensorRight T d P hb p) C ≫
          Limits.Pi.map (fun n ↦ (finiteProjectiveTensorRight T d P hb p).map (f n) ≫
            (finiteProjectiveTensorRightMap T d P P' hb hb' p p' e).app (C' n)) := by
  have := finiteProjectiveTensorRight_preservesProducts T d P hb p
  constructor
  · infer_instance
  · intro P' hb' p' e C' f
    apply Pi.hom_ext
    intro n
    simp
    simp [← Functor.map_comp]

end AlgebraicGeometry.Scheme
