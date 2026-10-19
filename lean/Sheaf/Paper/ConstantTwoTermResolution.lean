/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.CategoryTheory.ConstantCoefficientScalarExtension
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.Algebra.Homology.Double
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # The constant prime-power resolution on a small site

Source: Stacks Project, Modules on Sites, Tags 03EI and 03EP; Cohomology on Sites,
Tag 06YQ; main-20261015 blueprint, lem-pur-finite-kummer-level.proof.md
(blueprint: lem-pur-constant-two-term-resolution).
The coefficient sheaves are discrete constant sheaves, formed by module sheafification.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 1024

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory


namespace SheafOfModules.ConstantPrimePower

variable {S : Type u} [SmallCategory S] (J : GrothendieckTopology S)
  (l : ℕ) [Fact l.Prime]

/-- A universe lift of the ordinary coefficient ring. Source: Stacks, Tag 03EI,
constant-coefficient application (blueprint: lem-pur-constant-two-term-resolution). -/
abbrev Coeff := ULift.{u} (PadicInt l)

/-- Modules over the discrete constant coefficient ring. Source: Stacks, Tag 03EI
(blueprint: lem-pur-constant-two-term-resolution). -/
abbrev Modules := ringedSiteModules.{u} (constantCoefficientRing J (Coeff.{u} l))

/-- The constant coefficient module, obtained by the recorded constant module functor.
Source: Stacks, Tag 03EI (blueprint: lem-pur-constant-two-term-resolution). -/
abbrev freeModule : Modules J l :=
  (constantCoefficientModule J (Coeff.{u} l)).obj
    (ModuleCat.of (Coeff.{u} l) (Coeff.{u} l))

/-- The ordinary reduction homomorphism, lifted without changing its elements.
Source: Mathlib `PadicInt.toZModPow`; Stacks, Tag 03EI
(blueprint: lem-pur-constant-two-term-resolution). -/
def reductionRingHom (n : ℕ) : Coeff.{u} l →+* ULift.{u} (ZMod (l ^ n)) :=
  (PadicInt.toZModPow n).ulift

/-- The ordinary finite quotient as a module over the lifted coefficient ring.
Source: Stacks, Tag 03EI (blueprint: lem-pur-constant-two-term-resolution). -/
abbrev quotientModule (n : ℕ) : ModuleCat.{u} (Coeff.{u} l) :=
  (ModuleCat.restrictScalars (reductionRingHom.{u} l n)).obj
    (ModuleCat.of (ULift.{u} (ZMod (l ^ n))) (ULift.{u} (ZMod (l ^ n))))

/-- The ordinary quotient map as a linear map into its restricted-scalars module.
Source: Stacks, Tag 03EI (blueprint: lem-pur-constant-two-term-resolution). -/
def reductionLinear (n : ℕ) :
    ModuleCat.of (Coeff.{u} l) (Coeff.{u} l) ⟶ quotientModule.{u} l n :=
  ModuleCat.ofHom (X := ModuleCat.of (Coeff.{u} l) (Coeff.{u} l))
    (Y := quotientModule.{u} l n)
    { toFun := reductionRingHom l n
      map_add' := (reductionRingHom l n).map_add
      map_smul' := (reductionRingHom l n).map_mul }

/-- The constant finite quotient with its canonical constant-ring action.
Source: Stacks, Tag 03EI (blueprint: lem-pur-constant-two-term-resolution). -/
abbrev quotientSheaf (n : ℕ) : Modules J l :=
  (constantCoefficientModule J (Coeff.{u} l)).obj (quotientModule l n)

/-- Sheafification of the coefficient quotient map, retaining its specified normalization.
Source: Stacks, Tag 03EI (blueprint: lem-pur-constant-two-term-resolution). -/
abbrev quotientMap (n : ℕ) : freeModule J l ⟶ quotientSheaf J l n :=
  (constantCoefficientModule J (Coeff.{u} l)).map (reductionLinear l n)

/-- The image of a constant coefficient in the constant free module sheaf.
Source: Stacks, Tag 03EI (blueprint: lem-pur-constant-two-term-resolution). -/
def constantSection (U : Sᵒᵖ) (a : Coeff.{u} l) : (freeModule J l).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction.{u}
    (R := constantCoefficientRing J (Coeff.{u} l)) (J := J)
    (constantCoefficientUnit J (Coeff.{u} l))).unit.app
      ((strictPerfectConstantPresheaf (C := S) (Coeff.{u} l)).obj
        (ModuleCat.of (Coeff.{u} l) (Coeff.{u} l)))).app U) a

/-- The single complex in degree zero, using Mathlib's cochain convention.
Source: Stacks, Tag 0115 (blueprint: lem-pur-constant-two-term-resolution). -/
abbrev single (L : Modules J l) : CochainComplex (Modules J l) ℤ :=
  (CochainComplex.singleFunctor (Modules J l) 0).obj L

/-- The total tensor with a degree-zero left factor; this is the recorded signed total tensor.
Source: Stacks, Tag 06YN (blueprint: lem-pur-constant-two-term-resolution). -/
def total (L : Modules J l) (K : CochainComplex (Modules J l) ℤ) :
    CochainComplex (Modules J l) ℤ :=
  letI := monoidalCategory ((constantSheaf J CommRingCat.{u}).obj
    (CommRingCat.of (Coeff.{u} l)))
  CochainComplex.mapBifunctor (single J l L) K (curriedTensor _)

/-- Inclusion of the `(0,0)` summand, expressed using the explicit sheaf tensor product.
Source: Stacks, Tag 06YN and Section 03EK
(blueprint: lem-pur-constant-two-term-resolution). -/
def zeroSummand (L : Modules J l) (K : CochainComplex (Modules J l) ℤ) :
    (siteSheafTensorRight (K.X 0)).obj ((single J l L).X 0) ⟶ (total J l L K).X 0 :=
  letI := monoidalCategory ((constantSheaf J CommRingCat.{u}).obj
    (CommRingCat.of (Coeff.{u} l)))
  (siteSheafTensorRightIso _ (K.X 0)).hom.app _ ≫
    HomologicalComplex.ιMapBifunctor (single J l L) K (curriedTensor _) (.up ℤ)
      0 0 0 (zero_add 0)

private theorem constant_preservesFiniteLimits (B : Type u) [CommRing B] :
    PreservesFiniteLimits (constantCoefficientModule J B) := by
  have : PreservesFiniteLimits (strictPerfectConstantPresheaf (C := S) B) := by
    constructor
    intro D _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun _ ↦ hc)⟩
  dsimp [constantCoefficientModule]
  infer_instance

private theorem constant_preservesFiniteColimits (B : Type u) [CommRing B] :
    PreservesFiniteColimits (constantCoefficientModule J B) := by
  have : PreservesFiniteColimits (strictPerfectConstantPresheaf (C := S) B) := by
    constructor
    intro D _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun _ ↦ hc)⟩
  dsimp [constantCoefficientModule]
  infer_instance

private theorem free_unit :
    ∃ e : freeModule J l ≅ unit (constantCoefficientRing J (Coeff.{u} l)),
      ∀ (U : Sᵒᵖ) (a : Coeff.{u} l),
        e.hom.val.app U (constantSection J l U a) =
          (constantCoefficientUnit J (Coeff.{u} l)).app U a := by
  let B := Coeff.{u} l
  let R := constantCoefficientRing J B
  let α := constantCoefficientUnit J B
  let P := (strictPerfectConstantPresheaf (C := S) B).obj (ModuleCat.of B B)
  let b : P ⟶ (PresheafOfModules.restrictScalars α).obj (unit R).val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := P.obj U)
        (Y := ((PresheafOfModules.restrictScalars α).obj (unit R).val).obj U)
        { toFun := α.app U
          map_add' := (α.app U).hom.map_add
          map_smul' := by
            intro r x
            exact (α.app U).hom.map_mul r x }
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact congrArg (fun g ↦ g x) (α.naturality f) }
  let E := PresheafOfModules.sheafificationHomEquiv.{u} α (P := P) (F := unit R)
  let m : (PresheafOfModules.sheafification.{u} α).obj P ⟶ unit R := E.symm b
  have hm : E m = b := E.apply_symm_apply b
  let F := PresheafOfModules.toPresheaf ((Functor.const Sᵒᵖ).obj (RingCat.of B))
  have heq : CategoryTheory.toSheafify J P.presheaf ≫
      ((SheafOfModules.toSheaf R).map m).hom = F.map b := by
    exact (PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def α m).symm.trans
      (F.congr_map hm)
  have hbI : Presheaf.IsLocallyInjective J (F.map b) := by
    constructor
    intro U x y hxy
    exact Presheaf.equalizerSieve_mem J α x y hxy
  have hbS : Presheaf.IsLocallySurjective J (F.map b) := by
    constructor
    intro U x
    exact Presheaf.imageSieve_mem J α x
  have hmI : Sheaf.IsLocallyInjective ((SheafOfModules.toSheaf R).map m) := by
    rw [← Sheaf.isLocallyInjective_sheafToPresheaf_map_iff,
      ← Presheaf.comp_isLocallyInjective_iff J (CategoryTheory.toSheafify J P.presheaf)]
    exact heq.symm ▸ hbI
  have hmS : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map m) := by
    rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff,
      ← Presheaf.comp_isLocallySurjective_iff J (CategoryTheory.toSheafify J P.presheaf)]
    exact heq.symm ▸ hbS
  have : IsIso ((SheafOfModules.toSheaf R).map m) :=
    (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨hmI, hmS⟩
  have : IsIso m := isIso_of_reflects_iso m (SheafOfModules.toSheaf R)
  refine ⟨asIso m, ?_⟩
  intro U a
  exact congrArg (fun z ↦ z.app U a) heq

private theorem flat_of_iso {M N : Modules J l} (e : M ≅ N)
    (hN : IsFlatOnSite (J := J)
      (R := (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of (Coeff.{u} l))) N) :
    IsFlatOnSite (J := J)
      (R := (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of (Coeff.{u} l))) M := by
  let R := (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of (Coeff.{u} l))
  let := monoidalCategory R
  apply (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R M).symm
  apply (exactFunctor _ _).prop_of_iso ((curriedTensor _).flip.mapIso e).symm
  exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R N) hN

private theorem flat_of_isZero (M : Modules J l) (hM : IsZero M) :
    IsFlatOnSite (J := J)
      (R := (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of (Coeff.{u} l))) M := by
  let R := (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of (Coeff.{u} l))
  let := monoidalCategory R
  apply (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R M).symm
  have hz : IsZero (tensorRight M) := by
    rw [Functor.isZero_iff]
    intro N
    exact (tensorLeft N).map_isZero hM
  exact ⟨⟨fun _ _ _ ↦ (tensorRight M).preservesLimitsOfShape_of_isZero hz _⟩,
    ⟨fun _ _ _ ↦ (tensorRight M).preservesColimitsOfShape_of_isZero hz _⟩⟩

private abbrev ring : Sheaf J CommRingCat.{u} :=
  (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of (Coeff.{u} l))

set_option backward.isDefEq.respectTransparency false in
private def presheafTensorIso (M N : Modules J l) :
    (M.val ⊗ N.val : PresheafOfModules.{u} (constantCoefficientRing J (Coeff l)).obj) ≅
      siteTensorPresheaf M.val N.val :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
    intro U V f
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    rfl)

private def tensorIso (M N : Modules J l) :
    (siteSheafTensorRight N).obj M ≅
      letI := monoidalCategory (ring J l)
      M ⊗ N := by
  let := monoidalCategory (ring J l)
  let a := PresheafOfModules.sheafification.{u}
    (R := constantCoefficientRing J (Coeff l)) (𝟙 _)
  exact (a.mapIso (presheafTensorIso J l M N)).symm ≪≫
    (tensorObjIsoSheafification M N).symm

set_option backward.isDefEq.respectTransparency false in
private theorem presentation_eq (M N : Modules J l) :
    letI := monoidalCategory (ring J l)
    (tensorRightPresentation (ring J l) N).hom.app M =
      (tensorObjIsoSheafification M N).hom := by
  let := monoidalCategory (ring J l)
  change _ = (_ ⊗ₘ _) ≫ _
  rw [tensorHom_def']
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem tensorIso_eq (M N : Modules J l) :
    letI := monoidalCategory (ring J l)
    (tensorIso J l M N).hom = (siteSheafTensorRightIso (ring J l) N).hom.app M := by
  let := monoidalCategory (ring J l)
  let a := PresheafOfModules.sheafification.{u}
    (R := constantCoefficientRing J (Coeff l)) (𝟙 _)
  have he : (tensorRightPresentation (ring J l) N).app M =
      tensorObjIsoSheafification M N := Iso.ext (presentation_eq J l M N)
  change a.map (presheafTensorIso J l M N).inv ≫
    (tensorObjIsoSheafification M N).inv =
      a.map ((siteTensorRightIso (ring J l) N.val).hom.app M.val) ≫
        ((tensorRightPresentation (ring J l) N).app M).inv
  rw [he]
  rfl


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem tensorIso_naturality (M : Modules J l) {N N' : Modules J l}
    (g : N ⟶ N') :
    letI := monoidalCategory (ring J l)
    siteSheafTensorSecondMap M g ≫ (tensorIso J l M N').hom =
      (tensorIso J l M N).hom ≫ M ◁ g := by
  let := monoidalCategory (ring J l)
  let a := PresheafOfModules.sheafification.{u}
    (R := constantCoefficientRing J (Coeff l)) (𝟙 _)
  apply (cancel_mono (tensorObjIsoSheafification M N').hom).1
  simp only [Category.assoc, tensorIso, Iso.trans_hom, Iso.symm_hom,
    Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id,
    whiskerLeft_tensorObjIsoSheafification_hom]
  change a.map (siteTensorSecondMap M.val g.val) ≫
    a.map (presheafTensorIso J l M N').inv =
      a.map (presheafTensorIso J l M N).inv ≫ a.map (M.val ◁ g.val)
  rw [← a.map_comp, ← a.map_comp]
  apply a.congr_map
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem tensorSecond_tmul (M : Modules J l) {N N' : Modules J l}
    (g : N ⟶ N') (U : Sᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (siteSheafTensorSecondMap M g).val.app U (siteSheafTensorTmul M N U x y) =
      siteSheafTensorTmul M N' U x (g.val.app U y) := by
  have h := (PresheafOfModules.sheafificationAdjunction.{u}
    (R := constantCoefficientRing J (Coeff l)) (𝟙 _)).unit.naturality
      (siteTensorSecondMap M.val g.val)
  exact (congrArg (fun z ↦ z.app U (x ⊗ₜ[(ring J l).obj.obj U] y)) h).symm

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_unit (M : Modules J l) :
    ∃ e : (siteSheafTensorRight (unit (constantCoefficientRing J (Coeff l)))).obj M ≅ M,
      ∀ (U : Sᵒᵖ) (x : M.val.obj U)
        (r : (constantCoefficientRing J (Coeff l)).obj.obj U),
        e.hom.val.app U (siteSheafTensorTmul M _ U x r) = r • x := by
  let R := constantCoefficientRing J (Coeff l)
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (R := R) (𝟙 _)
  let ep : siteTensorPresheaf M.val (unit R).val ≅ M.val :=
    (presheafTensorIso J l M (unit R)).symm ≪≫ (ρ_ M.val)
  let e := (PresheafOfModules.sheafification.{u} (R := R) (𝟙 _)).mapIso ep ≪≫
    (asIso adj.counit).app M
  refine ⟨e, ?_⟩
  intro U x r
  have h : adj.homEquiv _ M e.hom = ep.hom :=
    (adj.homEquiv _ M).apply_symm_apply ep.hom
  exact congrArg (fun z ↦ z.app U (x ⊗ₜ[(ring J l).obj.obj U] r)) h

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_free (M : Modules J l) :
    letI := monoidalCategory (ring J l)
    ∃ e : M ⊗ freeModule J l ≅ M,
      ∀ (U : Sᵒᵖ) (x : M.val.obj U) (a : Coeff.{u} l),
        ((tensorIso J l M (freeModule J l)) ≪≫ e).hom.val.app U
          (siteSheafTensorTmul M _ U x (constantSection J l U a)) =
            (constantCoefficientUnit J (Coeff l)).app U a • x := by
  let := monoidalCategory (ring J l)
  obtain ⟨ef, hef⟩ := free_unit J l
  obtain ⟨eu, heu⟩ := tensor_unit J l M
  let e : M ⊗ freeModule J l ≅ M :=
    (tensorLeft M).mapIso ef ≪≫ (tensorIso J l M _).symm ≪≫ eu
  refine ⟨e, ?_⟩
  intro U x a
  have he : ((tensorIso J l M _) ≪≫ e).hom =
      siteSheafTensorSecondMap M ef.hom ≫ eu.hom := by
    dsimp [e]
    rw [← Category.assoc, ← tensorIso_naturality J l M ef.hom]
    simp
  rw [he]
  change eu.hom.val.app U
    ((siteSheafTensorSecondMap M ef.hom).val.app U _) = _
  rw [tensorSecond_tmul J l, hef]
  exact heu U x _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Two-term constant resolution and its tensor augmentation.
Source: Stacks, Tags 03EI, 03EP, 06YQ; main-20261015 blueprint,
lem-pur-finite-kummer-level.proof.md (blueprint: lem-pur-constant-two-term-resolution).

Proof:
1. The kernel formula for `PadicInt.toZModPow`, injectivity of multiplication in the
   coefficient domain, and surjectivity of the reduction give the ordinary short exact
   sequence. The constant-module functor preserves finite limits and colimits, so its
   image is the specified short exact sequence of constant module sheaves.
2. Construct the free-module identification with the tensor unit from the sheafification
   adjunction and the locally bijective ring unit. Tensor unitors make it flat, and zero
   is flat as well. The two-term complex is bounded above, hence independently K-flat by
   `lem-weil-pbc-independent-bounded-flat-kflat`.
3. Its only possible cohomology sheaves are the kernel in degree -1 and cokernel in degree 0.
   The quotient augmentation induces the cokernel identification, hence is a quasi-isomorphism.
4. By `lem-weil-pbc-independent-sheaf-tensor-colimits`, tensor preserves the quotient cokernel.
   The unitor takes `id tensor l^n` to multiplication by `l^n` on L. The induced quotient
   isomorphism sends `x tensor a-bar` to `a[x]`; its inverse sends `[x]` to `x tensor 1`.
   This identification requires no injectivity on L.
5. The total tensor has just the two terms L, with differential multiplication by `l^n`
   and positive sign. Under the assumed injectivity its degree -1 cohomology vanishes,
   and the normalized augmentation induces the quotient isomorphism on degree 0.
   The summand equation fixes the canonical augmentation, rather than an arbitrary map. -/
theorem constant_two_term_resolution (n : ℕ) (hn : 1 ≤ n) :
    ∃ (K : CochainComplex (Modules J l) ℤ)
      (em : K.X (-1) ≅ freeModule J l) (e0 : K.X 0 ≅ freeModule J l),
      (∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (K.X i)) ∧
      K.d (-1) 0 = em.hom ≫ ((l ^ n) • 𝟙 (freeModule J l)) ≫ e0.inv ∧
      (∀ i : ℤ, IsFlatOnSite
        (J := J)
        (R := (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of (Coeff.{u} l)))
        (K.X i)) ∧
      CochainComplex.IsKFlatIndependentCoefficients K ∧
      (∃ ε : K ⟶ single J l (quotientSheaf J l n),
        ε.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).hom =
          e0.hom ≫ quotientMap J l n ∧ QuasiIso ε) ∧
      (∀ L : Modules J l,
        ∃ φ : (siteSheafTensorRight (quotientSheaf J l n)).obj L ≅
            cokernel ((l ^ n) • 𝟙 L),
          (∀ (U : Sᵒᵖ) (x : L.val.obj U) (a : Coeff.{u} l),
            φ.hom.val.app U (siteSheafTensorTmul L (quotientSheaf J l n) U x
              ((quotientMap J l n).val.app U
                (constantSection J l U a))) =
              (cokernel.π ((l ^ n) • 𝟙 L)).val.app U
                (((constantCoefficientUnit J (Coeff.{u} l)).app U a) • x)) ∧
          (Mono ((l ^ n) • 𝟙 L) →
            ∃ α : total J l L K ⟶
                single J l ((siteSheafTensorRight (quotientSheaf J l n)).obj L),
              zeroSummand J l L K ≫ α.f 0 ≫
                  (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).hom =
                (siteSheafTensorRight (K.X 0)).map
                    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).hom ≫
                  siteSheafTensorSecondMap L (e0.hom ≫ quotientMap J l n) ∧
              QuasiIso α)) := by
  classical
  have _ := hn
  let f : freeModule J l ⟶ freeModule J l := (l ^ n) • 𝟙 _
  let q := quotientMap J l n
  have hp : Mono f ∧ ∃ hw : f ≫ q = 0,
      (ShortComplex.mk f q hw).Exact ∧ Epi q := by
    let A := Coeff.{u} l
    let f₀ : ModuleCat.of A A ⟶ ModuleCat.of A A := (l ^ n) • 𝟙 _
    let q₀ := reductionLinear.{u} l n
    have hmul (x : A) : f₀ x = (l : A) ^ n * x := by
      apply ULift.ext
      change (l ^ n) • x.down = (l : PadicInt l) ^ n * x.down
      simp [nsmul_eq_mul]
    have hker (x : A) : q₀ x = 0 ↔
        x.down ∈ Ideal.span ({(l : PadicInt l) ^ n} : Set (PadicInt l)) := by
      change ULift.up (PadicInt.toZModPow n x.down) = (0 : ULift (ZMod (l ^ n))) ↔ _
      rw [ULift.ext_iff]
      change PadicInt.toZModPow n x.down = 0 ↔ _
      rw [← PadicInt.ker_toZModPow]
      rfl
    have hw₀ : f₀ ≫ q₀ = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply (hker (f₀ x)).2
      rw [hmul]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
    have hex₀ : (ShortComplex.mk f₀ q₀ hw₀).Exact := by
      rw [ShortComplex.moduleCat_exact_iff]
      intro x hx
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp ((hker x).mp hx)
      refine ⟨ULift.up y, ?_⟩
      rw [hmul]
      exact ULift.ext _ _ hy.symm
    have hm₀ : Mono f₀ := by
      rw [ModuleCat.mono_iff_injective]
      have ht : (l : PadicInt l) ^ n ≠ 0 := pow_ne_zero n (by
        exact_mod_cast (Fact.out : l.Prime).ne_zero)
      intro x y hxy
      apply ULift.ext
      apply mul_left_cancel₀ ht
      have hd : ((l : A) ^ n * x).down = ((l : A) ^ n * y).down :=
        congrArg (fun z : A ↦ z.down) (by simpa only [hmul] using hxy)
      exact hd
    have hq₀ : Epi q₀ := by
      rw [ModuleCat.epi_iff_surjective]
      intro x
      obtain ⟨y, hy⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow n) x.down
      exact ⟨ULift.up y, ULift.ext _ _ hy⟩
    let F := constantCoefficientModule J A
    have : PreservesFiniteLimits F := constant_preservesFiniteLimits J A
    have : PreservesFiniteColimits F := constant_preservesFiniteColimits J A
    have := preservesBinaryBiproducts_of_preservesBinaryProducts F
    have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
    have heq : F.map f₀ = f := by simp [f₀, f, F, A]
    have hs₀ : (ShortComplex.mk f₀ q₀ hw₀).ShortExact := ⟨hex₀⟩
    have hs := hs₀.map_of_exact F
    have hm : Mono f := by
      rw [← heq]
      infer_instance
    have hw : f ≫ q = 0 := by
      rw [← heq]
      exact (ShortComplex.mk f₀ q₀ hw₀).map F |>.zero
    refine ⟨hm, hw, ?_, ?_⟩
    · have hsx := hs.exact
      change (ShortComplex.mk (F.map f₀) (F.map q₀) _).Exact at hsx
      simpa only [heq] using hsx
    · exact hs.epi_g
  have : Mono f := hp.1
  obtain ⟨hw, hex, hq⟩ := hp.2
  have : Epi q := hq
  have hf : IsFlatOnSite (J := J)
      (R := (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of (Coeff.{u} l)))
      (freeModule J l) := by
    let R := (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of (Coeff.{u} l))
    let := monoidalCategory R
    obtain ⟨e, _⟩ := free_unit J l
    have hu : IsFlatOnSite (J := J) (R := R) (unit (constantCoefficientRing J (Coeff l))) := by
      apply (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R _).symm
      apply (exactFunctor _ _).prop_of_iso (rightUnitorNatIso (Modules J l)).symm
      change PreservesFiniteLimits (𝟭 (Modules J l)) ∧
        PreservesFiniteColimits (𝟭 (Modules J l))
      exact ⟨inferInstance, inferInstance⟩
    exact flat_of_iso J l e hu
  have hrel : (ComplexShape.up ℤ).Rel (-1) 0 := by simp
  let K : CochainComplex (Modules J l) ℤ := HomologicalComplex.double f hrel
  let em := HomologicalComplex.doubleXIso₀ f hrel
  let e0 := HomologicalComplex.doubleXIso₁ f hrel (by omega)
  have hz (i : ℤ) (hm : i ≠ -1) (h0 : i ≠ 0) : IsZero (K.X i) :=
    HomologicalComplex.isZero_double_X f hrel i hm h0
  have hle : K.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact hz i (by omega) (by omega)
  have hflat (i : ℤ) : IsFlatOnSite (J := J)
      (R := (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of (Coeff.{u} l)))
      (K.X i) := by
    by_cases hm : i = -1
    · subst i
      exact flat_of_iso J l em hf
    · by_cases h0 : i = 0
      · subst i
        exact flat_of_iso J l e0 hf
      · exact flat_of_isZero J l (K.X i) (hz i hm h0)
  have hk : CochainComplex.IsKFlatIndependentCoefficients K := by
    have := hle
    exact SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite _ K 0 hflat
  let T := single J l (quotientSheaf J l n)
  let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0 (quotientSheaf J l n)
  have hT (i : ℤ) (hi : i ≠ 0) : IsZero (T.X i) :=
    HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ i hi
  let ε : K ⟶ T := HomologicalComplex.mkHomFromDouble hrel (by omega) 0 (q ≫ e.inv)
    (by change 0 ≫ T.d (-1) 0 = f ≫ q ≫ e.inv
        rw [zero_comp, ← Category.assoc, hw, zero_comp])
    (by intro i hi; exact (hT i (by simp only [ComplexShape.up_Rel] at hi; omega)).eq_of_tgt _ _)
  have hε0 : ε.f 0 ≫ e.hom = e0.hom ≫ q := by
    simp [ε, e0]
  have hεi (i : ℤ) (hi : i ≠ 0) : ε.f i = 0 := (hT i hi).eq_of_tgt _ _
  have hmono : Mono (K.d (-1) 0) := by
    dsimp [K]
    rw [HomologicalComplex.double_d f hrel (by omega)]
    infer_instance
  have hε : QuasiIso ε := by
    rw [quasiIso_iff]
    intro i
    by_cases hi : i = 0
    · subst i
      rw [quasiIsoAt_iff' ε (-1) 0 1 (by simp) (by simp)]
      apply (ShortComplex.quasiIso_iff_of_zeros' _
        ((hz 1 (by omega) (by omega)).eq_of_tgt _ _)
        ((hT (-1) (by omega)).eq_of_src _ _)
        ((hT 1 (by omega)).eq_of_tgt _ _)).2
      have heq : K.d (-1) 0 ≫ ε.f 0 = 0 := by
        rw [← ε.comm]
        simp [hεi (-1) (by omega)]
      let A := ShortComplex.mk (K.d (-1) 0) (ε.f 0) heq
      let B := ShortComplex.mk f q hw
      let iso : A ≅ B := ShortComplex.isoMk em e0 e
        (by dsimp [A, B, K, em, e0]
            rw [HomologicalComplex.double_d f hrel (by omega)]
            simp)
        hε0.symm
      have hs : A.Exact := (ShortComplex.exact_iff_of_iso iso).2 hex
      have : Epi (ε.f 0) := by
        have : Epi (ε.f 0 ≫ e.hom) := by rw [hε0]; infer_instance
        exact (epi_comp_iff_of_isIso (ε.f 0) e.hom).1 inferInstance
      exact ⟨hs, show Epi (ε.f 0) from inferInstance⟩
    · have hTex : T.ExactAt i := HomologicalComplex.ExactAt.of_isZero (hT i hi)
      rw [quasiIsoAt_iff_exactAt' ε i hTex]
      by_cases hm : i = -1
      · subst i
        rw [HomologicalComplex.exactAt_iff' K (-2) (-1) 0 (by simp) (by simp)]
        apply (ShortComplex.exact_iff_mono _ ((hz (-2) (by omega) (by omega)).eq_of_src _ _)).2
        exact hmono
      · exact HomologicalComplex.ExactAt.of_isZero (hz i hm hi)
  refine ⟨K, em, e0, hz, HomologicalComplex.double_d f hrel (by omega), hflat, hk,
    ⟨ε, hε0, hε⟩, ?_⟩
  intro L
  let R := (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of (Coeff.{u} l))
  let := monoidalCategory R
  let F := tensorLeft L
  have : PreservesColimitsOfSize.{u, u} F :=
    tensorLeft_preservesColimits_independentCoefficients R L
  have : F.Additive := tensorLeft_additive_independent R L
  obtain ⟨ef, hef⟩ := tensor_free J l L
  let t : L ⟶ L := (l ^ n) • 𝟙 L
  have hd : F.map f ≫ ef.hom = ef.hom ≫ t := by
    simp only [F, f, t, CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id,
      Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.comp_id, Category.id_comp]
  let hc := hex.gIsCokernel
  let hcF := CokernelCofork.mapIsColimit _ hc F
  let ec : F.obj (quotientSheaf J l n) ≅ cokernel (F.map f) :=
    CokernelCofork.mapIsoOfIsColimit
      (cc' := CokernelCofork.ofπ (cokernel.π (F.map f)) (cokernel.condition _))
      hcF (cokernelIsCokernel (F.map f))
      (Iso.refl (Arrow.mk (F.map f)))
  have hec : F.map q ≫ ec.hom = cokernel.π (F.map f) := by
    exact CokernelCofork.π_mapOfIsColimit hcF _ (𝟙 (Arrow.mk (F.map f)))
  let ect := cokernel.mapIso (F.map f) t ef ef hd
  let φ := tensorIso J l L (quotientSheaf J l n) ≪≫ ec ≪≫ ect
  have hφ : siteSheafTensorSecondMap L q ≫ φ.hom =
      ((tensorIso J l L (freeModule J l)) ≪≫ ef).hom ≫ cokernel.π t := by
    dsimp [φ]
    rw [← Category.assoc, tensorIso_naturality J l L q]
    change (tensorIso J l L (freeModule J l)).hom ≫
      F.map q ≫ ec.hom ≫ ect.hom = _
    rw [reassoc_of% hec]
    simp only [ect, cokernel.mapIso, cokernel.map, cokernel.π_desc, Category.assoc]
  refine ⟨φ, ?_, ?_⟩
  · intro U x a
    have h := congrArg (fun z ↦ z.val.app U
      (siteSheafTensorTmul L (freeModule J l) U x (constantSection J l U a))) hφ
    change φ.hom.val.app U ((siteSheafTensorSecondMap L q).val.app U _) = _ at h
    rw [tensorSecond_tmul J l] at h
    change φ.hom.val.app U (siteSheafTensorTmul L _ U x (q.val.app U
      (constantSection J l U a))) = (cokernel.π t).val.app U
        (((tensorIso J l L (freeModule J l)) ≪≫ ef).hom.val.app U
          (siteSheafTensorTmul L _ U x (constantSection J l U a))) at h
    rw [hef] at h
    exact h
  · intro hLt
    have : Mono t := hLt
    let D := (F.mapHomologicalComplex (.up ℤ)).obj K
    let T' := single J l (F.obj (quotientSheaf J l n))
    let es := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app
      (quotientSheaf J l n)
    let β : D ⟶ T' := (F.mapHomologicalComplex (.up ℤ)).map ε ≫ es.hom
    let em' : D.X (-1) ≅ L := F.mapIso em ≪≫ ef
    let e0' : D.X 0 ≅ L := F.mapIso e0 ≪≫ ef
    have hD (i : ℤ) (hm : i ≠ -1) (h0 : i ≠ 0) : IsZero (D.X i) :=
      F.map_isZero (hz i hm h0)
    have hT' (i : ℤ) (hi : i ≠ 0) : IsZero (T'.X i) :=
      HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ i hi
    let eq0 := HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (F.obj (quotientSheaf J l n))
    have hβ0 : β.f 0 ≫ eq0.hom = F.map (e0.hom ≫ q) := by
      change F.map (ε.f 0) ≫ es.hom.f 0 ≫ eq0.hom = _
      dsimp only [es, Iso.app_hom]
      rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
      simp only [Category.assoc]
      exact (F.map_comp (ε.f 0) e.hom).symm.trans (F.congr_map hε0)
    have hDf : D.d (-1) 0 ≫ (F.mapIso e0).hom =
        (F.mapIso em).hom ≫ F.map f := by
      change F.map (K.d (-1) 0) ≫ F.map e0.hom = F.map em.hom ≫ F.map f
      rw [← F.map_comp, ← F.map_comp]
      apply F.congr_map
      dsimp [K, em, e0]
      rw [HomologicalComplex.double_d f hrel (by omega)]
      simp
    have hDm : Mono (D.d (-1) 0) := by
      have ht : D.d (-1) 0 ≫ e0'.hom = em'.hom ≫ t := by
        dsimp [e0', em']
        calc
          (D.d (-1) 0 ≫ F.map e0.hom) ≫ ef.hom =
              (F.map em.hom ≫ F.map f) ≫ ef.hom :=
            congrArg (fun z ↦ z ≫ ef.hom) hDf
          _ = (F.map em.hom ≫ ef.hom) ≫ t := by
            rw [Category.assoc, hd, ← Category.assoc]
      have : Mono (D.d (-1) 0 ≫ e0'.hom) := by rw [ht]; infer_instance
      exact mono_of_mono (D.d (-1) 0) e0'.hom
    have hβ : QuasiIso β := by
      rw [quasiIso_iff]
      intro i
      by_cases hi : i = 0
      · subst i
        rw [quasiIsoAt_iff' β (-1) 0 1 (by simp) (by simp)]
        apply (ShortComplex.quasiIso_iff_of_zeros' _
          ((hD 1 (by omega) (by omega)).eq_of_tgt _ _)
          ((hT' (-1) (by omega)).eq_of_src _ _)
          ((hT' 1 (by omega)).eq_of_tgt _ _)).2
        have hzero : D.d (-1) 0 ≫ β.f 0 = 0 := by
          rw [← β.comm]
          rw [(hT' (-1) (by omega)).eq_of_tgt (β.f (-1)) 0, zero_comp]
        let A := ShortComplex.mk (D.d (-1) 0) (β.f 0) hzero
        let B := (ShortComplex.mk f q hw).map F
        let eAB : A ≅ B := ShortComplex.isoMk (F.mapIso em) (F.mapIso e0) eq0
          hDf.symm (by rw [hβ0, F.map_comp]; rfl)
        have hBF : B.Exact := hex.map_of_epi_of_preservesCokernel F inferInstance inferInstance
        have hA : A.Exact := (ShortComplex.exact_iff_of_iso eAB).2 hBF
        have : Epi (β.f 0) := by
          have : Epi (β.f 0 ≫ eq0.hom) := by rw [hβ0, F.map_comp]; infer_instance
          exact (epi_comp_iff_of_isIso (β.f 0) eq0.hom).1 inferInstance
        exact ⟨hA, show Epi (β.f 0) from inferInstance⟩
      · rw [quasiIsoAt_iff_exactAt' β i (HomologicalComplex.ExactAt.of_isZero (hT' i hi))]
        by_cases hm : i = -1
        · subst i
          rw [HomologicalComplex.exactAt_iff' D (-2) (-1) 0 (by simp) (by simp)]
          apply (ShortComplex.exact_iff_mono _
            ((hD (-2) (by omega) (by omega)).eq_of_src _ _)).2
          exact hDm
        · exact HomologicalComplex.ExactAt.of_isZero (hD i hm hi)
    let eD := CochainComplex.mapBifunctorSingle₁Iso (curriedTensor _) L K
    let eQ := (CochainComplex.singleFunctor (Modules J l) 0).mapIso
      (tensorIso J l L (quotientSheaf J l n)).symm
    let α := eD.hom ≫ β ≫ eQ.hom
    refine ⟨α, ?_, ?_⟩
    · have hι : HomologicalComplex.ιMapBifunctor (single J l L) K
          (curriedTensor _) (.up ℤ) 0 0 0 (zero_add 0) ≫ eD.hom.f 0 =
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).hom ▷ K.X 0 := by
        dsimp only [eD, CochainComplex.mapBifunctorSingle₁Iso, Iso.symm_hom,
          HomologicalComplex.Hom.isoOfComponents, Iso.symm_inv,
          CochainComplex.mapBifunctorSingle₁XIso]
        erw [HomologicalComplex.ι_mapBifunctorDesc]
        simp only [and_self, dif_pos]
        change ((curriedTensor (Modules J l)).map
          (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 L 0 rfl).hom).app (K.X 0) ≫
            (tensorLeft L).map (𝟙 (K.X 0)) = _
        rw [CategoryTheory.Functor.map_id, Category.comp_id]
        rfl
      have heQ : eQ.hom.f 0 ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).hom =
          eq0.hom ≫ (tensorIso J l L (quotientSheaf J l n)).inv := by
        change ((HomologicalComplex.single (Modules J l) (.up ℤ) 0).map
          (tensorIso J l L (quotientSheaf J l n)).inv).f 0 ≫ _ = _
        rw [HomologicalComplex.single_map_f_self]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rfl
      dsimp only [α, zeroSummand, HomologicalComplex.comp_f]
      simp only [Category.assoc]
      rw [reassoc_of% hι, heQ, reassoc_of% hβ0]
      change (siteSheafTensorRightIso R (K.X 0)).hom.app ((single J l L).X 0) ≫
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).hom ▷ K.X 0) ≫
          (L ◁ (e0.hom ≫ q)) ≫ (tensorIso J l L (quotientSheaf J l n)).inv = _
      have hnat := (siteSheafTensorRightIso R (K.X 0)).hom.naturality
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).hom
      have hnat' := congrArg (fun z ↦ z ≫ (L ◁ (e0.hom ≫ q)) ≫
        (tensorIso J l L (quotientSheaf J l n)).inv) hnat.symm
      refine hnat'.trans ?_
      simp only [Category.assoc]
      rw [← tensorIso_eq J l L (K.X 0)]
      have hs := congrArg
        (fun z ↦ z ≫ (tensorIso J l L (quotientSheaf J l n)).inv)
        (tensorIso_naturality J l L (e0.hom ≫ q)).symm
      have hs' : (tensorIso J l L (K.X 0)).hom ≫
          (L ◁ (e0.hom ≫ q)) ≫ (tensorIso J l L (quotientSheaf J l n)).inv =
            siteSheafTensorSecondMap L (e0.hom ≫ q) := by
        simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hs
      exact congrArg (fun z ↦ (siteSheafTensorRight (K.X 0)).map
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).hom ≫ z) hs'
    · have : QuasiIso β := hβ
      dsimp [α]
      infer_instance


end SheafOfModules.ConstantPrimePower
