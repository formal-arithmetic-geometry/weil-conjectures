/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.Topology.OpenModuleCohomology
public import WeilConjectures.Topology.Sheaves.CechComparison
import Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineCechComplexes
import Sheaf.AlgebraicGeometry.ModuleCechBetaAffineQuasiIso
import WeilConjectures.AlgebraicGeometry.OpenRestrictionModuleCohomology
import Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Affine-right external coefficients and the tensor Cech complex

Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, affine-open calculation.
(blueprint: lem-sc-picard-external-coefficients-affine-cech-comparison).
-/

@[expose] public section

set_option autoImplicit false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

private noncomputable def nativeCechIso {X : Scheme.{w}} (F : X.Modules)
    [F.IsQuasicoherent] {ι : Type w} (U : ι → X.Opens)
    (hU : ∀ (n : ℕ) (y : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hcover : iSup U = ⊤) (q : ℕ) :
    ((cechComplexFunctor U).obj F.presheafModuleCat).homology q ≅
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj F := by
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let I := injectiveResolution F
  have : QuasiIso (moduleCechBeta U I) := moduleCechBeta_quasiIso_of_affine U hU F I
  have : IsIso (HomologicalComplex.homologyMap (moduleCechAlpha U I) q) :=
    moduleCechAlpha_isIso U hcover I q
  exact asIso (HomologicalComplex.homologyMap (moduleCechBeta U I) q) ≪≫
    (asIso (HomologicalComplex.homologyMap (moduleCechAlpha U I) q)).symm ≪≫
    (I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) q).symm

private theorem tensorPullback_qcoh {X Y : Scheme.{w}} (a : X ⟶ Y)
    (F : Y.Modules) [F.IsQuasicoherent] : ((tensorPullback a).obj F).IsQuasicoherent := by
  let e := (nonempty_tensorPullbackAdjunction a).some.leftAdjointUniq
    (pullbackPushforwardAdjunction a)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (e.app F).symm (isQuasicoherent_pullback a F)


/-- The product-cover calculation computes open cohomology by the termwise tensor
of the first coefficient's Cech complex. It does not identify the first Cech
cohomology with global cohomology, or commute tensor with homology.
Source: Stacks Project, Tag 0BED, lemma-kunneth, paragraph "Let V be an affine open";
Tags 01XD, 01ET and 01E1 for affine Cech comparison and restriction of injectives.
(blueprint: lem-sc-picard-external-coefficients-affine-cech-comparison).

Proof: Cover X times V by U_i times V. Every nonempty finite intersection is
U_intersection times V, hence affine by the affine fibre-product formula. The
restriction of the external coefficient agrees with the external coefficient of
F and G restricted to V: use the open-immersion pullback/restriction isomorphism,
its adjunction-unit equation, and compatibility of pullback with composition.
On each intersection the affine pullback section formula and affine tensor section
formula give F(U_intersection) tensor_k G(V). Their maps send pure tensors to the
products of the pulled-back sections. Naturality of the adjunction units and of
tensorSectionsMap makes these identifications commute with every face restriction.
In degree n the tuple set is finite; tensor commutes with this finite product by
coordinate projections and the inverse obtained from coordinate inclusions. Thus
these degreewise maps and inverses commute with the alternating face differential,
giving an isomorphism with the displayed termwise tensor complex. The external
coefficient is quasi-coherent by pullback and tensor quasi-coherence. Affine Cech
comparison computes its cohomology on X times V. Restriction of an injective
resolution to that open remains injective and computes the displayed derived
sections over the open of the original product. Forget scalars and compose these
comparisons. Empty covers (possible when X is empty), empty V, and zero
coefficients have zero section complexes, so the construction includes them. -/
theorem picardExternalCupCoefficients_affine_cech_comparison
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {ι : Type w} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ (n : ℕ) (y : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hcover : iSup U = ⊤) (V : Y.Opens) (hV : IsAffineOpen V) (q : ℕ) :
    let R := ModuleCat.restrictScalars (scalarMap f ⊤)
    let C := (R.mapHomologicalComplex (.up ℕ)).obj
      ((cechComplexFunctor U).obj F.presheafModuleCat)
    let T := tensorRight (scalarObj (V.ι ≫ g) (G.restrict V.ι) (Opposite.op ⊤))
    Nonempty
      (((RingedSpace.openModuleCohomology (Limits.pullback f g).toRingedSpace q
        ((pullback.snd f g) ⁻¹ᵁ V)).obj (externalCupCoefficients f g F G)) ≅
        (forget₂ (ModuleCat.{w} k) AddCommGrpCat.{w}).obj
          (((T.mapHomologicalComplex (.up ℕ)).obj C).homology q)) := by
  classical
  let Z := Limits.pullback f g
  let W : Z.Opens := (pullback.snd f g) ⁻¹ᵁ V
  let E := externalCupCoefficients f g F G
  let E' := E.restrict W.ι
  let U' : ι → W.toScheme.Opens := fun i ↦ W.ι ⁻¹ᵁ ((pullback.fst f g) ⁻¹ᵁ U i)
  let B := (cechComplexFunctor U').obj E'.presheafModuleCat
  let R := ModuleCat.restrictScalars (scalarMap f ⊤)
  let C := (R.mapHomologicalComplex (.up ℕ)).obj
    ((cechComplexFunctor U).obj F.presheafModuleCat)
  let T := tensorRight (scalarObj (V.ι ≫ g) (G.restrict V.ι) (Opposite.op ⊤))
  let D := (T.mapHomologicalComplex (.up ℕ)).obj C
  let Q := forget₂ (ModuleCat.{w} Γ(W.toScheme, ⊤)) AddCommGrpCat.{w}
  let Qk := forget₂ (ModuleCat.{w} k) AddCommGrpCat.{w}
  obtain ⟨c⟩ := picardExternalCupCoefficients_affine_cech_complexes
    k X Y f g F G U hU V hV
  have hU' (n : ℕ) (y : Fin (n + 1) → ι) : IsAffineOpen (⨅ l, U' (y l)) := by
    have hEq : (⨅ l, U' (y l)) = W.ι ⁻¹ᵁ ((pullback.fst f g) ⁻¹ᵁ (⨅ l, U (y l))) := by
      apply TopologicalSpace.Opens.ext
      simp only [TopologicalSpace.Opens.coe_iInf, Scheme.Hom.coe_preimage,
        Set.preimage_iInter]
      rfl
    rw [hEq, ← W.ι.isAffineOpen_iff_of_isOpenImmersion,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
    exact isAffineOpen_preimage_inf_preimage_pullback f g (hU n y) hV
  have hcover' : iSup U' = ⊤ := by
    dsimp only [U']
    rw [← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_iSup, hcover]
    simp
  have : ((tensorPullback (pullback.fst f g)).obj F).IsQuasicoherent :=
    tensorPullback_qcoh _ _
  have : ((tensorPullback (pullback.snd f g)).obj G).IsQuasicoherent :=
    tensorPullback_qcoh _ _
  have : E.IsQuasicoherent :=
    (quasiCoherent_tensor_product_affine_sections
      ((tensorPullback (pullback.fst f g)).obj F)
      ((tensorPullback (pullback.snd f g)).obj G)).1
  obtain ⟨eOpen⟩ := nonempty_openRestriction_moduleCohomology_iso Z W q
  let eCech := nativeCechIso E' U' hU' hcover' q
  exact ⟨(eOpen.app E).symm ≪≫ Q.mapIso eCech.symm ≪≫
    ((B.sc q).mapHomologyIso Q).symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{w} (.up ℕ) q).mapIso c ≪≫
    (D.sc q).mapHomologyIso Qk⟩

end AlgebraicGeometry.Scheme.Modules
